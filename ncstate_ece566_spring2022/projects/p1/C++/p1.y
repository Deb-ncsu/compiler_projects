%{
#include <cstdio>
#include <list>
#include <vector>
#include <map>
#include <iostream>
#include <string>
#include <memory>
#include <stdexcept>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/FileSystem.h"

using namespace llvm;
using namespace std;

// Need for parser and scanner
extern FILE *yyin;
int yylex();
void yyerror(const char*);
int yyparse();
 
// Needed for LLVM
string funName;
Module *M;
LLVMContext TheContext;
IRBuilder<> Builder(TheContext);
 
std::map<std::string, Value*> regs;
std::map<std::string, Value*> regs_left_shift;
std::map<std::string, Value*> regs_bit_mask;
std::map<std::string, Value*> regs_bit_width;
map<std::string, Value*>::iterator it;
Value * bitslice_left_shift;
Value * bitslice_mask;
int current_field_val;
bool is_only_ID;
std::vector<std::string> field_ID_vector;
struct bitslice_lhs_type {
	string ID_name;
	Value* bit_mask;
	Value* left_shift;
	Value* bit_mask_rhs;
};
//std::vector<std::string> my_param_list;
%}

%union {
  vector<string> *params_list;
  Value *val;
  int num;
  char *bit_addr;
  struct bitslice_lhs_type *my_bitslice_lhs;
}

/*%define parse.trace*/

%type <params_list> params_list
%type <val> expr bitslice bitslice_list_helper bitslice_list 
%type <bit_addr> ID
%type <my_bitslice_lhs> bitslice_lhs
//%type <val> statement
//%type <val> statements
//%type <val> statements_opt
%type <num> NUMBER
%token IN FINAL SLICE
%token ERROR
%token NUMBER
%token ID 
%token BINV INV PLUS MINUS XOR AND OR MUL DIV MOD
%token COMMA ENDLINE ASSIGN LBRACKET RBRACKET LPAREN RPAREN NONE COLON
%token LBRACE RBRACE DOT
%token REDUCE EXPAND

%precedence BINV
%precedence INV
%left PLUS MINUS OR
%left MUL DIV AND XOR MOD

%start program

%%

program: inputs statements_opt final
{
  YYACCEPT;
}
;

inputs:   IN params_list ENDLINE
{  
  std::vector<Type*> param_types;
  for(auto s: *$2)
    {
      param_types.push_back(Builder.getInt32Ty());
    }
  ArrayRef<Type*> Params (param_types);
  
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getInt32Ty(),Params,false);

  // Create a main function
  Function *Function = Function::Create(FunType,GlobalValue::ExternalLinkage,funName,M);

  int arg_no=0;
  for(auto &a: Function->args()) {
    cout << " Inside function argument declaration " << endl;
    string str($2->at(arg_no));
    regs[str] = &a;
    arg_no++;
  }
  
  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));

}
| IN NONE ENDLINE
{ 
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getInt32Ty(),false);

  // Create a main function
  Function *Function = Function::Create(FunType,  
         GlobalValue::ExternalLinkage,funName,M);

  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));
}
;

params_list: ID
{
  vector<string> *my_param_list = new vector<string>;
  cout << " Inside params list " << endl;
  string str($1);
  cout << " Inside params list1 " << endl;
  my_param_list->push_back(str);
  $$ = my_param_list;
  // add ID to vector
}
| params_list COMMA ID
{
  cout << " Inside params_list COMMA ID " << endl;
  string str($3);
  $1->push_back(str);
}
;

final: FINAL expr ENDLINE
{
  // FIX ME, ALWAYS RETURNS 0
  //Builder.CreateRet(Builder.getInt32($2));
   Builder.CreateRet($2);
}
;

statements_opt: %empty
            | statements 
;

statements:   statement  
            | statements statement 
;

statement: bitslice_lhs ASSIGN expr ENDLINE
{
	//printf ("I am in statement \n");
        string str = $1->ID_name;
	it = regs.find(str);
	if(it == regs.end()) {
		cout << " string not found " << endl;
		regs[str] = $3;
	} else {
		cout << " string found " << endl;
		Value* my_not = Builder.CreateNot($1->bit_mask,"NOT");
		Value* temp = Builder.CreateAnd(my_not, regs[str], "and");
		Value* truncated_value = Builder.CreateAnd($1->bit_mask_rhs, $3, "and");
		Value* left_shift = Builder.CreateShl(truncated_value,$1->left_shift,"left_shift");
		regs[str] = Builder.CreateOr(left_shift,temp,"OR");
	}
        //printf ("Exiting bitslice_lhs ASSIGN expr ENDLINE \n");	

} 
| SLICE field_list ENDLINE { 
		//printf (" Inside slice field_list "); 
		if (is_only_ID==true) {
			int count = 0;
			while (!field_ID_vector.empty()) {
				string str(field_ID_vector.back());
				regs_bit_mask[str] = Builder.CreateShl(regs_bit_mask[str] , Builder.getInt32(count), "left_shift1");
				regs_left_shift[str] = Builder.CreateAdd(regs_left_shift[str],Builder.getInt32(count),"add");
				count++;
				field_ID_vector.pop_back();
			}
		}
}
;

field_list : field_list COMMA field
           | field { //printf (" Inside slice field "); }
;

field : ID COLON expr {
      		is_only_ID = false;
      		//printf ("I am in field \n");
		string str($1);
		regs[str] = $3;
		Value *bit_mask = Builder.CreateShl(Builder.getInt32(1), $3, "left_shift1");
		regs_bit_mask[str] = bit_mask;
		regs_left_shift[str] = $3;
		regs_bit_width[str] = Builder.getInt32(1);
	}
| ID LBRACKET expr RBRACKET COLON expr {
		//printf ("I am inside ID LBRACKET expr RBRACKET COLON expr ");
		is_only_ID = false;
		string str($1);
		Value *my_val1= Builder.CreateSub(Builder.getInt32(32), $3, "sub");
		Value *my_val2 = Builder.CreateLShr(Builder.getInt32(-1) , my_val1, "right_shift");
		Value *bit_mask = Builder.CreateShl(my_val2 , $6, "left_shift1");
		regs_bit_mask[str] = bit_mask;
		regs_left_shift[str] = $6;
		regs_bit_width[str] = $3;
}
// 566 only below
| ID   {
                string str($1);
                is_only_ID = true;
		current_field_val = 0;
		//regs[str] = Builder.getInt32(current_field_val);
		field_ID_vector.push_back(str);
                Value *bit_mask = Builder.CreateShl(Builder.getInt32(1), Builder.getInt32(current_field_val), "left_shift1");
                regs_bit_mask[str] = bit_mask;
                regs_left_shift[str] = Builder.getInt32(current_field_val);
                regs_bit_width[str] = Builder.getInt32(1);
}
;

expr: bitslice { 
        //printf ("Inside expression bitslice \n");
	$$ = $1; 
}
| expr PLUS expr { $$ = Builder.CreateAdd($1, $3, "add"); }
| expr MINUS expr { $$ = Builder.CreateSub($1, $3, "sub"); }
| expr XOR expr  { $$ = Builder.CreateXor($1, $3, "xor"); }
| expr AND expr  { $$ = Builder.CreateAnd($1, $3, "and"); }
| expr OR expr   { $$ = Builder.CreateOr($1, $3, "or"); }
| INV expr       { //printf ("Inside INV expr \n");
		   $$ = Builder.CreateXor($2 , Builder.getInt32(-1) , "xor");
		 }
| BINV expr     {
                        //printf ("Inside BINV expr \n");
                        Value *my_and = Builder.CreateAnd($2 , Builder.getInt32(1) , "and");
			Value *my_xor = Builder.CreateXor(my_and , Builder.getInt32(1) , "and");
			Value *my_and1 = Builder.CreateAnd($2 , Builder.getInt32(-2) , "and");
			Value *my_or = Builder.CreateOr(my_and1 , my_xor , "or");
                        $$ = my_or;
		}
| expr MUL expr { //printf ("Inside Mul\n"); 
		$$ = Builder.CreateMul($1, $3, "mul"); }
| expr DIV expr { 	//printf ("Inside Div\n");
			$$ = Builder.CreateSDiv($1, $3, "div"); }
| expr MOD expr {       //printf ("Inside Mod\n");
			$$ = Builder.CreateSRem($1, $3, "rem"); }
/* 566 only */
| REDUCE AND LPAREN expr RPAREN { 
					Value *value_0 = Builder.getInt32(0);
					for (int i =0; i<32; i++) {
						Value *bit_mask = Builder.CreateShl(Builder.getInt32(1) , Builder.getInt32(i), "left_shift1");
						Value *my_and = Builder.CreateAnd($4 , bit_mask , "and");
						Value *shift_right = Builder.CreateLShr(my_and , Builder.getInt32(i), "right_shift");
						value_0 = Builder.CreateAnd(value_0, shift_right, "add");
					}
					$$ = value_0;
				 }
| REDUCE OR LPAREN expr RPAREN {
					Value *value_0 = Builder.getInt32(0);
					for (int i =0; i<32; i++) {
						Value *bit_mask = Builder.CreateShl(Builder.getInt32(1) , Builder.getInt32(i), "left_shift1");
						Value *my_and = Builder.CreateAnd($4 , bit_mask , "and");
						Value *shift_right = Builder.CreateLShr(my_and , Builder.getInt32(i), "right_shift");
						value_0 = Builder.CreateOr(value_0, shift_right, "add");
					}
					$$ = value_0;
				 }
| REDUCE XOR LPAREN expr RPAREN {
					Value *value_0 = Builder.getInt32(0);
					for (int i =0; i<32; i++) {
						Value *bit_mask = Builder.CreateShl(Builder.getInt32(1) , Builder.getInt32(i), "left_shift1");
						Value *my_and = Builder.CreateAnd($4 , bit_mask , "and");
						Value *shift_right = Builder.CreateLShr(my_and , Builder.getInt32(i), "right_shift");
						value_0 = Builder.CreateXor(value_0, shift_right, "add");
					}
					$$ = value_0;
				 }
| REDUCE PLUS LPAREN expr RPAREN {
					Value *value_0 = Builder.getInt32(0);
					for (int i =0; i<32; i++) {
						Value *bit_mask = Builder.CreateShl(Builder.getInt32(1) , Builder.getInt32(i), "left_shift1");
						Value *my_and = Builder.CreateAnd($4 , bit_mask , "and");
						Value *shift_right = Builder.CreateLShr(my_and , Builder.getInt32(i), "right_shift");
						value_0 = Builder.CreateAdd(value_0, shift_right, "add");
					}
					$$ = value_0;
				 }
| EXPAND LPAREN expr RPAREN {
			    	Value *my_and = Builder.CreateAnd($3 , Builder.getInt32(1) , "and");
				$$ = Builder.CreateSub(Builder.getInt32(0), my_and, "sub");
			    }
;

bitslice: ID {
		//printf ("Inside bitsilce ID \n");
		string str($1);
		Value* my_val = regs[str];
		bitslice_left_shift = Builder.getInt32(1);
		$$ = my_val;
	        bitslice_mask = Builder.getInt32(1);
	     }
| NUMBER { 	//printf ("Inside bitsilce number \n");
		$$ = Builder.getInt32($1);
		//printf ("Exiting bit slice number \n"); 
		bitslice_left_shift = Builder.getInt32(1); 
		bitslice_mask = Builder.getInt32(1);
	}
| bitslice_list { $$ = $1; }
| LPAREN expr RPAREN { $$ = $2; } 
| bitslice NUMBER { 
		  	//printf ("Inside bitsilce blitslice NUMBER \n");
			Value* imm = Builder.getInt32($2);
			Value *bit_mask = Builder.CreateShl(Builder.getInt32(1) , imm, "left_shift1");
			Value *my_and = Builder.CreateAnd($1 , bit_mask , "and");
			bitslice_left_shift = Builder.getInt32(1);
			$$ = Builder.CreateLShr(my_and , imm, "right_shift");
			bitslice_mask = Builder.getInt32(-1);  
		}
| bitslice DOT ID {
			//printf ("Inside bitsilce blitslice DOT ID \n");
			string str($3);
			it = regs_bit_mask.find(str);
        		if(it == regs_bit_mask.end()) {
				cout << " Undefined field" << endl; 
				YYABORT;
			}
			Value *bit_mask = regs_bit_mask[str];
			Value *shift = regs_left_shift[str];
			Value *my_and1 = Builder.CreateAnd($1 , bit_mask , "and");
			bitslice_left_shift = regs_bit_width[str];
			$$ = Builder.CreateLShr(my_and1 , shift, "right_shift");
		 	bitslice_mask = Builder.getInt32(-1);
		 }
// 566 only
| bitslice LBRACKET expr RBRACKET {
		  	//printf ("Inside bitsilce LBRACKET expr RBRACKET \n");
			Value *bit_mask = Builder.CreateShl(Builder.getInt32(1) , $3, "left_shift1");
			Value *my_and = Builder.CreateAnd($1 , bit_mask , "and");
			bitslice_left_shift = Builder.getInt32(1);
			$$ = Builder.CreateLShr(my_and , $3, "right_shift");
			bitslice_mask = Builder.getInt32(-1);
		  }
| bitslice LBRACKET expr COLON expr RBRACKET {
			//printf ("Inside bitslice LBRACKET expr COLON expr RBRACKET \n");
			Value *my_sub1 = Builder.CreateSub($3, $5, "sub");
			Value *my_add1 = Builder.CreateAdd(my_sub1, Builder.getInt32(1),"add");
			Value *my_val1= Builder.CreateSub(Builder.getInt32(32), my_add1, "sub");
			Value *my_val2 = Builder.CreateLShr(Builder.getInt32(-1) , my_val1, "right_shift");
			Value *bit_mask = Builder.CreateShl(my_val2 , $5, "left_shift1");
			Value *my_and1 = Builder.CreateAnd($1 , bit_mask , "and");
			$$ = Builder.CreateLShr(my_and1 , $5, "right_shift");
			bitslice_left_shift = my_add1;
			bitslice_mask = Builder.getInt32(-1);
		  }
;

bitslice_list: LBRACE bitslice_list_helper RBRACE { $$ = $2; }
;

bitslice_list_helper:  bitslice { $$ =  Builder.CreateAnd($1 , bitslice_mask , "and"); 
				}
| bitslice_list_helper COMMA bitslice {
	//printf ("I am inside bitslice_list_helper \n");
	Value *res1 = Builder.CreateShl($1, bitslice_left_shift , "mul");
	//printf ("I am inside bitslice_list_helper1 \n");
        Value* lsb_val = Builder.CreateAnd($3 , bitslice_mask , "and");
	$$ = Builder.CreateAdd(res1,lsb_val, "add");
}
;

bitslice_lhs: ID { //printf ("Inside bitslice_lhs \n ");
		   struct bitslice_lhs_type * bit_slice_data = new struct bitslice_lhs_type; 
		   string str($1);
		   bit_slice_data->ID_name = str; 
		   //printf ("In bitslice lhs ___ 1\n");
		   bit_slice_data->bit_mask = Builder.getInt32(-1);
		   bit_slice_data->left_shift = Builder.getInt32(0);
		   bit_slice_data->bit_mask_rhs = Builder.getInt32(-1);
		   $$ = bit_slice_data;
                 } 
| bitslice_lhs NUMBER {
		   $1->bit_mask = Builder.CreateShl(Builder.getInt32(1), $2 , "left_shift");
		   $1->left_shift = Builder.getInt32($2);
		   $1->bit_mask_rhs = Builder.getInt32(1);
		   $$ = $1; 
} 
| bitslice_lhs DOT ID {
		   string str($3);
        	   it = regs_bit_mask.find(str);
		   if(it == regs_bit_mask.end()) {
		 	cout << " Undefined field" << endl; 
			YYABORT;
	           }
		   Value* temp_bit_mask = Builder.CreateShl(regs_bit_mask[str], $1->left_shift, "left_shift");
		   Value* new_bit_mask = Builder.CreateAnd(temp_bit_mask,$1->bit_mask,"and");
		   Value* total_left_shift = Builder.CreateAdd($1->left_shift, regs_left_shift[str] ,"add");
		   Value *shift_right = Builder.CreateLShr(regs_bit_mask[str], regs_left_shift[str], "right_shift");
		   $1->bit_mask_rhs = shift_right;
		   $1->left_shift = total_left_shift;
		   $1->bit_mask = new_bit_mask;
		   $$ = $1;
}
// 566 only
| bitslice_lhs LBRACKET expr RBRACKET {
		   Value* total_left_shift = Builder.CreateAdd($1->left_shift, $3 ,"add");
		   Value* temp_bit_mask = Builder.CreateShl(Builder.getInt32(1), total_left_shift, "left_shift");
		   Value* new_bit_mask = Builder.CreateAnd(temp_bit_mask,$1->bit_mask,"and");
		   $1->bit_mask_rhs = Builder.getInt32(1); 
		   $1->left_shift = total_left_shift;
		   $1->bit_mask = new_bit_mask;
		   
}
| bitslice_lhs LBRACKET expr COLON expr RBRACKET { 
			Value *my_sub1 = Builder.CreateSub($3, $5, "sub");
			Value *my_add1 = Builder.CreateAdd(my_sub1, Builder.getInt32(1),"add");
			Value *my_val1= Builder.CreateSub(Builder.getInt32(32), my_add1, "sub");
			Value *my_val2 = Builder.CreateLShr(Builder.getInt32(-1) , my_val1, "right_shift");
			Value *bit_mask = Builder.CreateShl(my_val2 , $5, "left_shift1");
		   	Value* temp_bit_mask = Builder.CreateShl(bit_mask, $1->left_shift, "left_shift");
		   	Value* new_bit_mask = Builder.CreateAnd(temp_bit_mask,$1->bit_mask,"and");
			Value* total_left_shift = Builder.CreateAdd($1->left_shift,$5,"add");
			$1->bit_mask_rhs = my_val2;
			$1->left_shift = total_left_shift;
			$1->bit_mask = new_bit_mask;
}
;

%%

unique_ptr<Module> parseP1File(const string &InputFilename)
{
  funName = InputFilename;
  if (funName.find_last_of('/') != string::npos)
    funName = funName.substr(funName.find_last_of('/')+1);
  if (funName.find_last_of('.') != string::npos)
    funName.resize(funName.find_last_of('.'));
    
  //errs() << "Function will be called " << funName << ".\n";
  
  // unique_ptr will clean up after us, call destructor, etc.
  unique_ptr<Module> Mptr(new Module(funName.c_str(), TheContext));

  // set global module
  M = Mptr.get();
  
  /* this is the name of the file to generate, you can also use
     this string to figure out the name of the generated function */
  yyin = fopen(InputFilename.c_str(),"r");
  bitslice_left_shift = NULL;
  bitslice_mask = NULL;
  current_field_val = 0;
  is_only_ID = false;
  //yydebug = 1;
  if (yyparse() != 0)
    // errors, so discard module
    Mptr.reset();
  else
    // Dump LLVM IR to the screen for debugging
    M->print(errs(),nullptr,false,true);
  
  return Mptr;
}

void yyerror(const char* msg)
{
  //printf("%s\n",msg);
}
