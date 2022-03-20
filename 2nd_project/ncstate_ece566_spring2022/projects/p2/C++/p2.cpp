#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <iostream>
#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Dominators.h"
//#include "llvm/IR/Dominance.h"
using namespace llvm;

static void CommonSubexpressionElimination(Module *M);
static bool isDead(Instruction &);
static bool Simplify_Inst(Instruction *, Module*);
static void cse_opt(Instruction *, BasicBlock*, bool );
static void CommonSubexpressionElimination_new(Module *M);
static void replaceUses(Instruction*, Instruction* );
static void summarize(Module *M);
static void print_csv_file(std::string outputfile);
static void PrintInstructions(Module *);
static void ReplaceLoadCSE (Module *);
static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        Mem2Reg("mem2reg",
                cl::desc("Perform memory to register promotion before CSE."),
                cl::init(false));

static cl::opt<bool>
        NoCSE("no-cse",
              cl::desc("Do not perform CSE Optimization."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    LLVMContext Context;

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);
    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // If requested, do some early optimizations
    if (Mem2Reg)
    {
        legacy::PassManager Passes;
        Passes.add(createPromoteMemoryToRegisterPass());
        Passes.run(*M.get());
    }

    if (!NoCSE) {
        CommonSubexpressionElimination(M.get());
        //ReplaceLoadCSE(M.get());
    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());
    PrintStatistics(errs());
    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M) {
    for (auto i = M->begin(); i != M->end(); i++) {
        if (i->begin() != i->end()) {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++) {
            for (auto k = j->begin(); k != j->end(); k++) {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I)) {
                    nLoads++;
                } else if (isa<StoreInst>(&I)) {
                    nStores++;
                }
            }
        }
    }
}

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}

static llvm::Statistic CSEDead = {"", "CSEDead", "CSE found dead instructions"};
static llvm::Statistic CSEElim = {"", "CSEElim", "CSE redundant instructions"};
static llvm::Statistic CSESimplify = {"", "CSESimplify", "CSE simplified instructions"};
static llvm::Statistic CSELdElim = {"", "CSELdElim", "CSE redundant loads"};
static llvm::Statistic CSEStore2Load = {"", "CSEStore2Load", "CSE forwarded store to load"};
static llvm::Statistic CSEStElim = {"", "CSEStElim", "CSE redundant stores"};

static void CommonSubexpressionElimination(Module *M) {	
	//errs() << " Printing instructions \n";
	//PrintInstructions(M);
	//std::cout << " printing Instructions done " << std::endl;
	BasicBlock *BB;
	int func_count = 0;
	for (auto func = M->begin(); func!=M->end(); func++) {
		// creating the dominator tree
		//std::cout << " function count " << func_count << std::endl;
		//func_count++;
		DominatorTree DT; 	
		//std::cout << " failing here1 " << std::endl;
		//auto *inst_to_check = func->begin()->begin();
		bool is_empty = func->empty();
		//std::cout << " is_empty " << is_empty << std::endl;
		if (is_empty) { continue; }
		//BasicBlock *c_b = &(*(func->begin()));
		//Instruction *inst_to_check = &(*(c_b->begin()));
		//std::cout << " function count " << func_count << std::endl;
		func_count++;
		//inst_to_check->print(errs());
		DT.recalculate(*func);
		//std::cout << " failing here2 " << std::endl;
        // looping over functions
        for (auto basic_block= func->begin(); basic_block!=func->end(); basic_block++) {
            // looping over basic block 
			auto duplicate_inst = basic_block->begin();
			auto inst=basic_block->begin();
			//std::cout << " new basic block " << std::endl;
			while (inst!=basic_block->end()) {
				// finding out dead instructions
				Instruction *my_inst = &(*inst);
				//Value* my_inst_value = dyn_cast<Value> my_inst;
				//LLVMTypeOf(cast<Value>my_inst);
				bool is_inst_dead = isDead(*my_inst);
				bool is_simplifiable = Simplify_Inst (my_inst, M);
				if (is_inst_dead == true) { CSEDead++; }
				if (is_simplifiable == true) { CSESimplify++;}
                if (is_inst_dead || is_simplifiable) {
					// if the instruction is the starting instruction 
					if (inst==basic_block->begin()) {
						duplicate_inst++;
						inst->eraseFromParent();
						inst = duplicate_inst;
					} else {
						inst->eraseFromParent();
						inst = duplicate_inst;
						inst++;
					}
					//LLVMBasicBlockRef child = LLVMFirstDomChild(basic_block);
				} else if (my_inst->getOpcode() == Instruction::Load || my_inst->getOpcode() == Instruction::Store) {
				    //ReplaceLoadCSE_opt(inst,basic_block);	
                    //inst++;	
                    // looping over basic block 
                    //auto duplicate_inst = inst;
                	//auto inst=basic_block->begin();
                        		if (my_inst->getOpcode() == Instruction::Load ) {
                			//std::cout << " I am here " << std::endl;
                			//my_inst->print(errs());
                			auto iterator_for_load = inst;
                			iterator_for_load++;
                			//iterator_for_load->print(errs());
                			while (iterator_for_load!=basic_block->end()) {
                				//errs() << " Printing instructions \n";
                				//PrintInstructions(M);
                				//std::cout << " printing Instructions done " << std::endl;
                				//std::cout << " I am here1 " << std::endl;
                				Instruction *cur_inst = &(*iterator_for_load);
                				//std::cout << " I am here2 " << std::endl;
                				//cur_inst->print(errs());
                				//if (cur_inst->getOpcode() == Instruction::Store && my_inst->getOperand(0) == cur_inst->getOperand(1) ) {break;}
                				//if (cur_inst->getOpcode() == Instruction::Store || cur_inst->getOpcode() == Instruction::Call ) {break;}
						//CallInst *x = dyn_cast<CallInst>(cur_inst);
						/*if (cur_inst->getOpcode() == Instruction::Call) {
							CallInst *x = dyn_cast<CallInst>(cur_inst);
							if (x!=NULL) {
								//x->print(errs());
								//std::cout << " has address taken" << x->hasAddressTaken() << std::endl;
								auto *F = x->getCalledFunction();
								//std::cout << " has address taken" << F->hasAddressTaken() << " does not access mem " << F->doesNotAccessMemory() << " only reads" << F->onlyReadsMemory() << " onlyAccessesArgMemory " << F->onlyAccessesArgMemory() << std::endl;
								//bool isPrintf = (F->getName() == "printf");
								if (F->hasAddressTaken()) {
									break;
								}
									if( !(x->doesNotAccessMemory()) && !(x->onlyReadsMemory()) && !isPrintf) { 
									//x->print(errs());
									//std::cout << " isPrintf " << isPrintf ;
									//std::cout << " Inside callInst " << std::endl;
									break; 
								} else {
									x->print(errs());
									std::cout << " isPrintf " << isPrintf ;
									std::cout << " Inside callInst " << std::endl;
								}
							}
						}*/
						if (cur_inst->getOpcode() == Instruction::Store ) {break;}
                				//std::cout << " I am here3 " << std::endl;
                				if (cur_inst->getOpcode() == Instruction::Load && my_inst->getOperand(0) == cur_inst->getOperand(0) && my_inst->getType() == cur_inst->getType()) {
                					LoadInst *li = dyn_cast<LoadInst>(cur_inst);
                					//std::cout << " I am here4 " << std::endl;
                					if (li && li->isVolatile()) {
                						break;
                						
                					}
                					cur_inst->print(errs());
							iterator_for_load++;
                					//std::cout << " Inside replace " << std::endl;
                					//replaceUses(my_inst,cur_inst);
                					cur_inst->replaceAllUsesWith(my_inst);
                                    cur_inst->eraseFromParent();
                					CSELdElim++;
                                }
                
                				iterator_for_load++;	
                            }
			    // trace the instructions above
			     LoadInst *li = dyn_cast<LoadInst>(my_inst);
			     if (li && li->isVolatile()) {
                		duplicate_inst = inst;
                		inst++;
				continue;	
			     }
			     auto iterator_for_load1 = basic_block->begin();
			     bool load_eliminate_pos = false;
			     bool store_to_load_upgrade_pos = false;
			     Instruction *cur_inst;
			     Instruction *inst_to_replace;
			     while (iterator_for_load1!=inst) {
			     	cur_inst = &(*iterator_for_load1);
				if (cur_inst->getOpcode() == Instruction::Store && my_inst->getOperand(0) == cur_inst->getOperand(1) && my_inst->getType() == (cur_inst->getOperand(0))->getType()) { 
					store_to_load_upgrade_pos = true; 
					load_eliminate_pos = false;
					inst_to_replace = cur_inst;
				} else if ( cur_inst->getOpcode() == Instruction::Store /*|| cur_inst->getOpcode() == Instruction::Call*/) {
					load_eliminate_pos = false;
					store_to_load_upgrade_pos = false;
				} else if (cur_inst->getOpcode() == Instruction::Load && my_inst->getOperand(0) == cur_inst->getOperand(0) && my_inst->getType() == cur_inst->getType()) {
					load_eliminate_pos = true;	
					inst_to_replace = cur_inst;
					store_to_load_upgrade_pos = false;
				}
				iterator_for_load1++;
			     }
			     if (load_eliminate_pos == true) { 
				     CSELdElim++; 
			     	     my_inst->replaceAllUsesWith(inst_to_replace);
			     }
			     if (store_to_load_upgrade_pos == true) { 
				     CSEStore2Load++; 
				     my_inst->replaceAllUsesWith(inst_to_replace->getOperand(0));			     	     
			     }
			     if (load_eliminate_pos == true || store_to_load_upgrade_pos == true) {
			     	 my_inst->print(errs());
				 std::cout << " \t" ;
				 inst_to_replace->print(errs());
				 std::cout << std::endl;
				 my_inst->eraseFromParent();
			     	 inst = duplicate_inst;
			     }
			     
                        } else if (my_inst->getOpcode() == Instruction::Store) {
                            auto iterator_for_store_check = inst;
                            iterator_for_store_check++;
			    StoreInst *si = dyn_cast<StoreInst>(my_inst);
			    if (si && si->isVolatile()) {
                		duplicate_inst = inst;
                		inst++;
				continue;	
			    }
                            while (iterator_for_store_check!=basic_block->end()) {
                                Instruction *cur_inst = &(*iterator_for_store_check);
                                if (cur_inst->getOpcode() == Instruction::Store && my_inst->getOperand(1) == cur_inst->getOperand(1) && (my_inst->getOperand(0))->getType() == (cur_inst->getOperand(0))->getType()) {
                                    /*StoreInst *si = dyn_cast<StoreInst>(my_inst);
                                    if (si && si->isVolatile()) {
                						break;
                						
                					}*/
                                    my_inst->eraseFromParent();
                                    CSEStElim++;
                                    inst = duplicate_inst;
                                    break; 
                                } else if (cur_inst->getOpcode() == Instruction::Load && my_inst->getOperand(1) == cur_inst->getOperand(0) && (my_inst->getOperand(0))->getType() == cur_inst->getType()) {
                			LoadInst *li = dyn_cast<LoadInst>(cur_inst);
                                    	if (li && li->isVolatile()) {
               					break;
                						
             				}
                			iterator_for_store_check++;
               				//std::cout << " I am here5 " << std::endl;
              				cur_inst->replaceAllUsesWith(my_inst->getOperand(0));
                                    	cur_inst->eraseFromParent();
                			CSEStore2Load++;
                                	//iterator_for_store_check++;
					continue;
				}  
				if (/* cur_inst->getOpcode() == Instruction::Call ||*/ cur_inst->getOpcode() == Instruction::Store || cur_inst->getOpcode() == Instruction::Load) {break;}
                                	iterator_for_store_check++;
                            	}
                        }
                	duplicate_inst = inst;
                	inst++;	
			} else {
					BB = &(*basic_block);
					//bool is_dominate = DominatorTree::dominates(my_inst,BB);
					for (auto new_bb_itr= func->begin(); new_bb_itr!=func->end(); new_bb_itr++) {
						BasicBlock *BB1 = &(*new_bb_itr);
						//std::cout << " before calling dominator " << std::endl;
						bool is_dominate = DT.dominates(BB,BB1);
						bool is_same_block = false;
                        if (BB==BB1) {
                            is_same_block = true;
                        }
						//std::cout << " before opt " << std::endl;
						//BB->begin()->print(errs());
						//BB1->begin()->print(errs());
						if (is_dominate) {
							cse_opt(my_inst, BB1, is_same_block);
						}
						//std::cout << " after opt " << std::endl;
						//std::cout << " is_dominate " << is_dominate << std::endl;
						
					}
					duplicate_inst = inst;
					inst++;
				}
			}
                }
        }
	//errs() << " Printing instructions \n";
	//PrintInstructions(M);

}
/* static void ReplaceLoadCSE_opt (Instruction *inst, BasicBlock *BB) {
 
    // looping over basic block 
    auto duplicate_inst = inst;
	//auto inst=basic_block->begin();
	while (inst!=BB->end()) {
		 Instruction *my_inst = &(*inst);
        if (my_inst->getOpcode() == Instruction::Load ) {
			//std::cout << " I am here " << std::endl;
			//my_inst->print(errs());
			auto iterator_for_load = inst;
			iterator_for_load++;
			//iterator_for_load->print(errs());
			while (iterator_for_load!=basic_block->end()) {
				//errs() << " Printing instructions \n";
				//PrintInstructions(M);
				//std::cout << " printing Instructions done " << std::endl;
				//std::cout << " I am here1 " << std::endl;
				Instruction *cur_inst = &(*iterator_for_load);
				//std::cout << " I am here2 " << std::endl;
				//cur_inst->print(errs());
				//if (cur_inst->getOpcode() == Instruction::Store && my_inst->getOperand(0) == cur_inst->getOperand(1) ) {break;}
				if (cur_inst->getOpcode() == Instruction::Store || cur_inst->getOpcode() == Instruction::Call || cur_inst->getOpcode() == Instruction::Invoke) {break;}
				//std::cout << " I am here3 " << std::endl;
				if (cur_inst->getOpcode() == Instruction::Load && my_inst->getOperand(0) == cur_inst->getOperand(0) && my_inst->getType() == cur_inst->getType()) {
					LoadInst *li = dyn_cast<LoadInst>(cur_inst);
					//std::cout << " I am here4 " << std::endl;
					if (li && li->isVolatile()) {
						break;
						
					}
					iterator_for_load++;
					//std::cout << " I am here5 " << std::endl;
					//replaceUses(my_inst,cur_inst);
					cur_inst->replaceAllUsesWith(my_inst);
                    cur_inst->eraseFromParent();
					CSELdElim++;
                }

				iterator_for_load++;	
            }
        } else if (my_inst->getOpcode() == Instruction::Store) {
            auto iterator_for_store_check = inst;
            iterator_for_store_check++;
            while (iterator_for_store_check!=basic_block->end()) {
                Instruction *cur_inst = &(*iterator_for_store_check);
                if (cur_inst->getOpcode() == Instruction::Store && my_inst->getOperand(1) == cur_inst->getOperand(1) && (my_inst->getOperand(0))->getType() == (cur_inst->getOperand(0))->getType()) {
                    StoreInst *si = dyn_cast<StoreInst>(my_inst);
                    if (si && si->isVolatile()) {
						break;
						
					}
                    my_inst->eraseFromParent();
                    CSEStElim++;
                    inst = duplicate_inst;
                    break; 
                }
                if (cur_inst->getOpcode() == Instruction::Load && my_inst->getOperand(1) == cur_inst->getOperand(0) && (my_inst->getOperand(0))->getType() == cur_inst->getType()) {
					LoadInst *li = dyn_cast<LoadInst>(cur_inst);
                    if (li && li->isVolatile()) {
						break;
						
					}
					iterator_for_store_check++;
					//std::cout << " I am here5 " << std::endl;
					cur_inst->replaceAllUsesWith(my_inst->getOperand(0));
                    cur_inst->eraseFromParent();
					CSEStore2Load++;
                }
				if ( cur_inst->getOpcode() == Instruction::Call || cur_inst->getOpcode() == Instruction::Invoke || cur_inst->getOpcode() == Instruction::Store || cur_inst->getOpcode() == Instruction::Load) {break;}
                iterator_for_store_check++;
            }
        }
		duplicate_inst = inst;
		inst++;	
    }
 }*/

 static void ReplaceLoadCSE (Module *M) {
 
	for (auto func = M->begin(); func!=M->end(); func++) {
        for (auto basic_block= func->begin(); basic_block!=func->end(); basic_block++) {
            // looping over basic block 
		    auto duplicate_inst = basic_block->begin();
			auto inst=basic_block->begin();
			while (inst!=basic_block->end()) {
				 Instruction *my_inst = &(*inst);
                if (my_inst->getOpcode() == Instruction::Load ) {
					//std::cout << " I am here " << std::endl;
					//my_inst->print(errs());
					auto iterator_for_load = inst;
					iterator_for_load++;
					//iterator_for_load->print(errs());
					while (iterator_for_load!=basic_block->end()) {
						//errs() << " Printing instructions \n";
						//PrintInstructions(M);
						//std::cout << " printing Instructions done " << std::endl;
						//std::cout << " I am here1 " << std::endl;
						Instruction *cur_inst = &(*iterator_for_load);
						//std::cout << " I am here2 " << std::endl;
						//cur_inst->print(errs());
						//if (cur_inst->getOpcode() == Instruction::Store && my_inst->getOperand(0) == cur_inst->getOperand(1) ) {break;}
						if (cur_inst->getOpcode() == Instruction::Store || cur_inst->getOpcode() == Instruction::Call || cur_inst->getOpcode() == Instruction::Invoke) {break;}
						//std::cout << " I am here3 " << std::endl;
						if (cur_inst->getOpcode() == Instruction::Load && my_inst->getOperand(0) == cur_inst->getOperand(0) && my_inst->getType() == cur_inst->getType()) {
							LoadInst *li = dyn_cast<LoadInst>(cur_inst);
							//std::cout << " I am here4 " << std::endl;
							if (li && li->isVolatile()) {
								break;
								
							}
							iterator_for_load++;
							//std::cout << " I am here5 " << std::endl;
							//replaceUses(my_inst,cur_inst);
							cur_inst->replaceAllUsesWith(my_inst);
                            cur_inst->eraseFromParent();
							CSELdElim++;
                        }

						iterator_for_load++;	
                    }
                } else if (my_inst->getOpcode() == Instruction::Store) {
                    auto iterator_for_store_check = inst;
                    iterator_for_store_check++;
                    while (iterator_for_store_check!=basic_block->end()) {
                        Instruction *cur_inst = &(*iterator_for_store_check);
                        if (cur_inst->getOpcode() == Instruction::Store && my_inst->getOperand(1) == cur_inst->getOperand(1) && (my_inst->getOperand(0))->getType() == (cur_inst->getOperand(0))->getType()) {
                            StoreInst *si = dyn_cast<StoreInst>(my_inst);
                            if (si && si->isVolatile()) {
								break;
								
							}
                            my_inst->eraseFromParent();
                            CSEStElim++;
                            inst = duplicate_inst;
                            break; 
                        }
                        if (cur_inst->getOpcode() == Instruction::Load && my_inst->getOperand(1) == cur_inst->getOperand(0) && (my_inst->getOperand(0))->getType() == cur_inst->getType()) {
							LoadInst *li = dyn_cast<LoadInst>(cur_inst);
                            if (li && li->isVolatile()) {
								break;
								
							}
							iterator_for_store_check++;
							//std::cout << " I am here5 " << std::endl;
							cur_inst->replaceAllUsesWith(my_inst->getOperand(0));
                            cur_inst->eraseFromParent();
							CSEStore2Load++;
                        }
						if ( cur_inst->getOpcode() == Instruction::Call || cur_inst->getOpcode() == Instruction::Invoke || cur_inst->getOpcode() == Instruction::Store || cur_inst->getOpcode() == Instruction::Load) {break;}
                        iterator_for_store_check++;
                    }
                }
				duplicate_inst = inst;
				inst++;	
            }
        }
    }
}
static void replaceUses(Instruction *inst_to_replace_with, Instruction* inst_to_replace) {
// This function replaces use of cur_inst with my_inst
	using use_iterator = Value::use_iterator;
	std::set<Instruction*> all_uses;
	for(use_iterator u = inst_to_replace->use_begin(); u!=inst_to_replace->use_end(); u++)
	{
		Value *v = u->getUser();
		all_uses.insert(dyn_cast<Instruction>(v));
	}
	while(all_uses.size()>0) {
		Instruction *inst_to_update = *all_uses.begin();
		for(unsigned op=0; op < inst_to_update->getNumOperands(); op++) {
			Instruction* def = dyn_cast<Instruction> (inst_to_update->getOperand(op));
			if (def != NULL) {
				if (def == inst_to_replace) {
					dyn_cast<Instruction>(inst_to_update)->setOperand(op,inst_to_replace_with);
				}
			}
		}
		all_uses.erase(inst_to_update);
	}
}



static bool isDead(Instruction &I) {
	if ( I.use_begin() == I.use_end() )
	{
        int opcode = I.getOpcode();
        switch(opcode){
            case Instruction::Add:
            case Instruction::FNeg:
            case Instruction::FAdd:
            case Instruction::Sub:
            case Instruction::FSub:
            case Instruction::Mul:
            case Instruction::FMul:
            case Instruction::UDiv:
            case Instruction::SDiv:
            case Instruction::FDiv:
            case Instruction::URem:
            case Instruction::SRem:
            case Instruction::FRem:
            case Instruction::Shl:
            case Instruction::LShr:
            case Instruction::AShr:
            case Instruction::And:
            case Instruction::Or:
            case Instruction::Xor:
            case Instruction::Alloca:
            case Instruction::GetElementPtr:
            case Instruction::Trunc:
            case Instruction::ZExt:
            case Instruction::SExt:
            case Instruction::FPToUI:
            case Instruction::FPToSI:
            case Instruction::UIToFP:
            case Instruction::SIToFP:
            case Instruction::FPTrunc:
            case Instruction::FPExt:
            case Instruction::PtrToInt:
            case Instruction::IntToPtr:
            case Instruction::BitCast:
            case Instruction::AddrSpaceCast:
            case Instruction::ICmp:
            case Instruction::FCmp:
            case Instruction::PHI:
            case Instruction::Select:
            case Instruction::ExtractElement:
            case Instruction::InsertElement:
            case Instruction::ShuffleVector:
            case Instruction::ExtractValue:
            case Instruction::InsertValue:
                return true; // dead, but this is not enough

            case Instruction::Load:
            {
                LoadInst *li = dyn_cast<LoadInst>(&I);
                if (li && li->isVolatile())
                    return false;
                return true;
            }
            default:
                // any other opcode fails
                return false;
        }
    }

    return false;
}

static void PrintInstructions(Module *M) {
	int func_count = 0;
	for (auto func = M->begin(); func!=M->end(); func++) {
		// looping over functions
		//std::cout << " function count " << func_count << std::endl;
	    //if (func->empty() == true) {continue;}
            //func_count++;
 	int b_count = 0;	
        for (auto basic_block= func->begin(); basic_block!=func->end(); basic_block++) {
			// looping over basic block 
			std::cout << " b_count " << b_count++ << std::endl;
			for (auto inst=basic_block->begin(); inst!=basic_block->end(); inst++) {
				Instruction *my_inst = &(*inst);
				my_inst->print(errs());
				errs() << "\n";
			}
			b_count++;
		}
        
	}
	errs() << " all Instruction printed \n"; 
}

static bool Simplify_Inst(Instruction *my_inst, Module* M) {

	/*if (my_inst->getOpcode() == Instruction::Load || my_inst->getOpcode() == Instruction::Alloca || my_inst->getOpcode() == Instruction::Store || my_inst->getOpcode() == Instruction::FCmp || my_inst->getOpcode() == Instruction::VAArg || my_inst->getOpcode() == Instruction::Call ) {
		return false;
	}*/
	DataLayout my_dl(&(*M));
	SimplifyQuery x(my_dl);
	Value* my_simplified_inst = SimplifyInstruction(my_inst,x);
	if (my_simplified_inst!=NULL) {
		my_inst->replaceAllUsesWith(my_simplified_inst);
			return true;
	}
	return false;
}

static void cse_opt(Instruction *my_inst, BasicBlock* BB, bool is_same_block) {
	
	std::set<Instruction*> matching_instruction;
	if (my_inst->isTerminator()) { return; }
	// my_inst->getOpcode() == Instruction::ExtractValue
	if (my_inst->getOpcode() == Instruction::Load || my_inst->getOpcode() == Instruction::Alloca || my_inst->getOpcode() == Instruction::Store || my_inst->getOpcode() == Instruction::FCmp || my_inst->getOpcode() == Instruction::VAArg || my_inst->getOpcode() == Instruction::Call || my_inst->getOpcode() == Instruction::ExtractValue ) {
		return;
	}
	
	//std::cout << " printing my_inst " << std::endl;
	//my_inst->print(errs(), true);
	//std::cout << std::endl;
	// If the basic block contains the original instruction
	// we need to parse only the instructions
	// below current instruction
	auto inst1=BB->begin();
	if (is_same_block) {
		Instruction *cur_inst = &(*inst1);
		while (cur_inst!=my_inst) {
            //std::cout << " I am here " << std::endl;
            inst1++;
            cur_inst = &(*inst1);
		}
	}
	for (auto inst=inst1; inst!=BB->end(); inst++) {	
		Instruction *cur_inst = &(*inst);
		if (my_inst == cur_inst) { continue;}
		if (my_inst->getType() != cur_inst->getType()) { continue; }
		if (my_inst->getOpcode() != cur_inst->getOpcode()) { continue;}
		if (my_inst->getNumOperands() != cur_inst->getNumOperands()) { continue;}
		if (my_inst->getOpcode() == Instruction::ICmp) {
            		ICmpInst *my_inst_icmp = cast<ICmpInst>(my_inst);
            		ICmpInst *cur_inst_icmp = cast<ICmpInst>(cur_inst);
            		if (my_inst_icmp->getPredicate()!=cur_inst_icmp->getPredicate()) { continue; }
            		//std::cout << " ICmp" << std::endl;
        	} 
        bool all_operands_matching = true;
		for(unsigned op=0; op < my_inst->getNumOperands(); op++) {
			if (my_inst->getOperand(op)!=cur_inst->getOperand(op)) {
				all_operands_matching = false;
				break;
			}
		}
		if (all_operands_matching) {
			matching_instruction.insert(cur_inst);
		}


	}
	while(matching_instruction.size()>0) {
		Instruction* i= *matching_instruction.begin();
		matching_instruction.erase(i);
		i->replaceAllUsesWith(my_inst);
        // loop over all the uses of i to remove 
		/*using use_iterator = Value::use_iterator;
		std::set<Instruction*> all_uses;
		for(use_iterator u = i->use_begin(); u!=i->use_end(); u++) {
			Value *v = u->getUser();
			all_uses.insert(dyn_cast<Instruction>(v));
		}
		while(all_uses.size()>0) {
			Instruction *inst_to_update = *all_uses.begin();
			for(unsigned op=0; op < inst_to_update->getNumOperands(); op++) {
				Instruction* def = dyn_cast<Instruction> (inst_to_update->getOperand(op));
				if (def != NULL) {
					if (def == i) {
						dyn_cast<Instruction>(inst_to_update)->setOperand(op,my_inst);
					}
				}
			}
			all_uses.erase(inst_to_update);
		}*/
		//std::cout << " printing CSE instruction " << std::endl;
		//i->print(errs(), true);
		//std::cout << std::endl;
		i->eraseFromParent();
		CSEElim++;
	}
}
