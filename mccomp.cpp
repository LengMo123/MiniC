#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <exception>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::sys;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE {

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN {
  int type = -100;
  std::string lexeme;
  int lineNo;
  int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;                // Filled in if INT_LIT
static bool BoolVal;              // Filled in if BOOL_LIT
static float FloatVal;            // Filled in if FLOAT_LIT
static std::string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type) {
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok() {

  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar)) {
    if (LastChar == '\n' || LastChar == '\r') {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) ||
      (LastChar == '_')) { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true") {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false") {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9]+.
    std::string NumStr;

    if (LastChar == '.') { // Floatingpoint Number: .[0-9]+
      do {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    } else {
      do { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.') { // Floatingpoint Number: [0-9]+.[0-9]+)
        do {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      } else { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&') {
    NextChar = getc(pFile);
    if (NextChar == '&') { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|') {
    NextChar = getc(pFile);
    if (NextChar == '|') { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
      ;
    }
  }

  if (LastChar == '<') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/') { // could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/') { // definitely a comment
      do {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return gettok();
    } else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF) {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  std::string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

class PrototypeAST;
class DeclAST;
class BlockAST;
class ProgramAST;
class ExprAST;
class UnaryExprAST;
class BinaryOpAST;
class FunctionCallAST;
class IntAST;
class FloatAST;
class BoolAST;
class VariableAST;
class VariableDeclAST;
class FuncDeclAST;
class ParameterAST;
class StatementAST;
class ExprStmtAST;
class IfStmtAST;
class WhileStmtAST;
class ReturnStmtAST;

std::string printLCNo(TOKEN tok) {
  return " -- Line " + std::to_string(tok.lineNo) + " Column " + std::to_string(tok.columnNo);
}

/// ASTnode - Base class for all AST nodes.
class ASTnode {
public:
  virtual ~ASTnode() {}
  virtual Value *codegen() = 0;
  virtual std::string to_string(std::string indent) const {return "";};
};

// StatementAST - Base class for all statements AST nodes i.e. expression stmt, if stmt, while stmt and block stmt
class StatementAST: public ASTnode {
  TOKEN tok;
public:
  virtual Value *codegen() = 0;
};

// DeclAST- Base class for all declaration AST nodes -- Function Decl and Variable Decl
class DeclAST: public ASTnode {
public:
  virtual Value *codegen() = 0;
};

// ExprAST - Base Class for Expressions
class ExprAST: public ASTnode {
public:
  virtual Value *codegen() = 0;
};


// ParameterAST - Class for each parameter in a function call or a function declaration
// @arguments : TOKEN type, TOKEN id
class ParameterAST: public ASTnode {
  TOKEN type;
  TOKEN identifier;

public:
  ParameterAST(TOKEN type, TOKEN identifier): type(type), identifier(identifier) {}

  Value* codegen() override;

  virtual std::string to_string(std::string indent) const override {
  // return a string representation of this AST node
    std::string output = indent + "<Parameter> " + printLCNo(identifier) + "\n"; 
    indent += " ";
    output += indent + "<Var>" + identifier.lexeme + printLCNo(identifier) + "\n"; 
    output += indent + "<Type>"  + type.lexeme + printLCNo(identifier) + "\n";
    return output;
  };
  // getName() -- Will be used in IR generation
  std::string getName() {
    return identifier.lexeme;
  }
  int getType() {
    return type.type;
  }
};

// VariableDeclAST - Class for declared variables
// @arguments: TOKEN type, TOKEN id
class VariableDeclAST : public DeclAST {
  TOKEN type;
  TOKEN identifier;

public:
  VariableDeclAST(TOKEN type, TOKEN identifier): type(type), identifier(identifier) {}
  virtual Value *codegen() override;
  Value *codegen(bool isNotGlobal);
  virtual std::string to_string(std::string indent) const override {
    std::string output = indent + "<Parameter> " + printLCNo(identifier) + "\n"; 
    indent += " ";
    output += indent + "<Var>" + identifier.lexeme + printLCNo(identifier) + "\n"; 
    output += indent + "<Type>"  + type.lexeme + printLCNo(identifier) + "\n";
    return output;
  }
};

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
// @arguments: TOKEN return_type, TOKEN prototype_name,
//             std::vector<std::unique_ptr<ParameterAST>> Args
class PrototypeAST : public ASTnode {
  TOKEN type;
  TOKEN prototype_name; 
  std::vector<std::unique_ptr<ParameterAST>> Args;

public:
  PrototypeAST(TOKEN type, 
        TOKEN prototype_name, 
        std::vector<std::unique_ptr<ParameterAST>> Args)
    : type(type), prototype_name(prototype_name), Args(std::move(Args)) {}

  virtual Function *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    std::string output = indent + "<Function Name> " + prototype_name.lexeme + printLCNo(prototype_name) + "\n"; 
    output += indent + "<Return type> " + type.lexeme + printLCNo(type) + "\n";
    if (Args.size() > 0) {
      output += indent + "<Parameters>\n";
      indent += " "; // indent + 1
      for (const auto &param: Args) {
        // pass the indent to to_string() function of each to_string()
        output = output + param->to_string(indent);
      }
    }
    return output;
  };

  std::string getName() {
    return prototype_name.lexeme;
  }
};

// BlockAST - This class represents node of block statements
//            Including local variable declarations and statements
// @arguments: TOKEN tok (Apparently there is no TOKEN which can represent the whole block, but we take it for the sake of indicating column and row numbers)
//             std::vector<std::unique_ptr<VariableDeclAST>> local_decls -- vector of the variable decls in the block
//             std::vector<std::unique_ptr<StatementAST>> stmt_list -- vector of the statements in the block, e.g. assignments, arithmetic expressions
class BlockAST : public StatementAST {
  TOKEN tok;
  std::vector<std::unique_ptr<VariableDeclAST>> local_decls;
  std::vector<std::unique_ptr<StatementAST>> stmt_list;

public:
  BlockAST(std::vector<std::unique_ptr<VariableDeclAST>> local_decls,
           std::vector<std::unique_ptr<StatementAST>> stmt_list)
      : local_decls(std::move(local_decls)), stmt_list(std::move(stmt_list)) {}

  virtual Value *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    std::string output;
    output = output + indent + "<Block>" + printLCNo(tok) + "\n";
    // indent + 1
    indent += " ";
    if (local_decls.size() > 0)
      output += indent + "<Local Decls>\n";
    for (const auto &local_decl: local_decls) {
      // for declarations, we pass the indent + 1
      output = output + local_decl->to_string(indent + " ");
    }
    if (stmt_list.size() > 0)
      output += indent + "<Statement List>\n";
    for (const auto &stmt: stmt_list) {
      // for statements, we pass the indent + 1
      output = output + stmt->to_string(indent + " ");
    }
    return output;
  }
};


// ProgramAST - Class for the root node Program
// @arguments: std::vector<std::unique_ptr<PrototypeAST>> Extern_List
//             std::vector<std::unique_ptr<DeclAST>> Decl_List
class ProgramAST: public ASTnode {
  std::vector<std::unique_ptr<ASTnode>> Extern_List;
  std::vector<std::unique_ptr<DeclAST>> Decl_List;

public:
  ProgramAST(std::vector<std::unique_ptr<ASTnode>> Extern_List,
             std::vector<std::unique_ptr<DeclAST>> Decl_List):
    Extern_List(std::move(Extern_List)), Decl_List(std::move(Decl_List)) {}
  
  virtual Value *codegen() override;

  virtual std::string to_string(std::string indent = "") const override {
    std::string output = "<Program>\n"; // indent = 0 (root)
    indent += " ";
    if (Extern_List.size() > 0) 
      output = output + indent + "<Extern_List>\n"; // indent + 1
    
    for (const auto& Extern: Extern_List) {
      output = output + Extern->to_string(indent + " "); // print each extern function, which is the successor of <extern_list>, so indent + 2
    }
    if (Decl_List.size() > 0)
      output = output + indent + "<Decl_list>\n"; // indent + 1
    for (const auto& Decl: Decl_List) {
      output = output + Decl->to_string(indent + " "); // print each declaration, which is the successor of <decl_list>, so indent + 2
    }
    return output;
  }
};

// UnaryExprAST -- Class for unary expressions
// @arguments: TOKEN Operator -- Unary operator of the expression e.g. -(negative), !(not)
//             std::unique_ptr<ExprAST> Expr -- Expression after the unary operator
class UnaryExprAST: public ExprAST {
  TOKEN Operator;
  std::unique_ptr<ExprAST> UnaryExpr;

public:
  UnaryExprAST(TOKEN Operator, std::unique_ptr<ExprAST> UnaryExpr):
        Operator(Operator), UnaryExpr(std::move(UnaryExpr)) {}

  virtual Value *codegen() override;

  virtual std::string to_string(std::string indent) const override {
    std::string output;
    output += indent + "<Unary Expression>\n";
    indent += " "; 
    output += indent + "<Operator>: " + Operator.lexeme + printLCNo(Operator) +"\n"; // <Operator> is a child node of <Unary Expression>, so indent + 1
    output += UnaryExpr->to_string(indent); // Pass the increased indent to to_string() of the expression
    return output;    
  }
};

// BinaryOpAST -- Class for expression with binary operators
// @arguments: TOKEN Operator -- Binary Operator
//             std::unique_ptr<ExprAST> LHS;
//             std::unique_ptr<ExprAST> RHS;

class BinaryOpAST: public ExprAST {
  TOKEN Operator;
  std::unique_ptr<ExprAST> LHS;
  std::unique_ptr<ExprAST> RHS;

public:
  BinaryOpAST(TOKEN Operator, 
  std::unique_ptr<ExprAST> LHS,
  std::unique_ptr<ExprAST> RHS):
  Operator(Operator), LHS(std::move(LHS)), RHS(std::move(RHS)) {}

  virtual Value *codegen() override;

  virtual std::string to_string(std::string indent) const override {
    std::string output;
    output += indent + "<Binary Expression>\n";
    indent += " ";
    output += indent + "<Operator>: " + Operator.lexeme + printLCNo(Operator) + "\n"; // <Operator> is the child of <Binary Expression>, so we pass indent + 1 to its string expression
    indent += " ";
    output += LHS->to_string(indent); // We decide to let LHS and RHS be the children of the <Operator>, so make indent + 1
    output += RHS->to_string(indent); 
    
    return output;
  }

};

// AssignmentAST - Class for value assignments to variables
// @arguments: TOKEN id -- Variable name
//             std::unique_ptr<ExprAST> Expr -- Expression to be computed to assign its result to the variable
class AssignmentAST: public ExprAST {
  TOKEN identifier;
  std::unique_ptr<ExprAST> Expr;

public:
  AssignmentAST(TOKEN identifier, std::unique_ptr<ExprAST> Expr):
    identifier(identifier), Expr(std::move(Expr)) {}

  virtual Value *codegen() override;

  virtual std::string to_string(std::string indent) const override {
    std::string output;
    output += indent + "<Assignment>" + printLCNo(identifier) + "\n"; 
    indent += " ";
    output += indent + "<Variable>: " + identifier.lexeme + printLCNo(identifier) + "\n"; // <Variable> and <Assigned Value> are the children of AssignmentAST, so indent + 1
    output += indent + "<Assigned Value>: \n";
    indent += " ";
    output += Expr->to_string(indent); // <Expr> is the child of <Assigned Value>, so indent + 1
    return output;
  }
};

// FunctionCallAST - Class for function calls (Subclass of ExprAST)
// @arguments: TOKEN function_name
//             std::vector<std::unique_ptr<ExprAST>> args -- vector of expressions passed into the function call as arguments.
class FunctionCallAST: public ExprAST {
  TOKEN function_name;
  std::vector<std::unique_ptr<ExprAST>> args;

public:
  FunctionCallAST(TOKEN function_name, 
              std::vector<std::unique_ptr<ExprAST>> args):
      function_name(function_name), args(std::move(args)) {}

  virtual Value *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    std::string output = indent + "<Function Call>" + printLCNo(function_name) + "\n";
    indent += " ";
    output += indent + "<Function Name> " + function_name.lexeme + printLCNo(function_name) + "\n"; // <Function Name> and <Arguments> are children of <Function Call>, so indent + 1
    output += indent + "<Arguments>\n";
    for (const auto& arg: args) {
      output = output + arg->to_string(indent + " "); // Each argument is the child of <Arguments>, so indent + 1
    }
    return output;
  }
};

// IntAST - Class for int literals
// @arguments: TOKEN int_literal
class IntAST: public ExprAST {
  TOKEN int_literal;
  
public:
  IntAST(TOKEN int_literal): int_literal(int_literal) {}
  virtual Value *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    return indent + "<int literal> " + int_literal.lexeme + printLCNo(int_literal) + "\n";
  }
};

// FloatAST - Class for int literals
// @arguments: TOKEN float_literal
class FloatAST: public ExprAST {
  TOKEN float_literal;

public:
  FloatAST(TOKEN float_literal): float_literal(float_literal) {}

  virtual Value *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    return indent + "<float literal> " + float_literal.lexeme + printLCNo(float_literal) + "\n";
  }
};

// BoolAST - Class for int literals
// @arguments: TOKEN bool_literal
class BoolAST: public ExprAST {
  TOKEN bool_literal;

public:
  BoolAST(TOKEN bool_literal): bool_literal(bool_literal) {}

  virtual Value *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    return indent + "<bool literal> " + bool_literal.lexeme + printLCNo(bool_literal) + "\n";
  }
};

// VariableAST - Class for variables used in expressions 
// @arguments: TOKEN var
class VariableAST: public ExprAST {
  TOKEN var;

public:
  VariableAST(TOKEN var): var(var) {}

  virtual Value *codegen() override;

  virtual std::string to_string(std::string indent) const override {
    return indent + "<Variable> " + var.lexeme + printLCNo(var) + " \n";
  }

};

// FuncDeclAST - Class for declared functions
// @arguments: TOKEN id - function name
//             std::unique_ptr<PrototypeAST> prototype -- Contains information of return type, function name and required arguments
//             std::unique_ptr<BlockAST> func_body -- Function body.
class FuncDeclAST: public DeclAST {
  TOKEN identifier;
  std::unique_ptr<PrototypeAST> prototype;
  std::unique_ptr<BlockAST> func_body;

public:
  FuncDeclAST(TOKEN identifier, 
  std::unique_ptr<PrototypeAST> prototype, 
  std::unique_ptr<BlockAST> func_body): 
  identifier(identifier), prototype(std::move(prototype)), func_body(std::move(func_body)) {}

  virtual Function *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    std::string output = indent+"<Function Decl>" + printLCNo(identifier) + "\n";
    output += prototype->to_string(indent + " "); // <Prototype> and <Block>(function body) are the children of <Function Decl>
    output += func_body->to_string(indent + " ");
    return output;
  };
};

// ExprStmtAST - Class for expression statements e.g. arthimetic expressions, assignments and function calls
// @arguments: TOKEN tok -- Generally, one token is not able to represent an expression, but we take the first token of the expression for the sake of column and row numbers
//             std::unique_ptr<ExprAST> Expr
class ExprStmtAST: public StatementAST {
  TOKEN tok;
  std::unique_ptr<ExprAST> Expr;
public:
  ExprStmtAST(TOKEN tok, std::unique_ptr<ExprAST> Expr): tok(tok), Expr(std::move(Expr)) {}

  virtual Value *codegen() override;
  virtual std::string to_string(std::string indent) const override {
    std::string output;
    output = indent + output + "<Expr Statement>" + printLCNo(tok) + "\n";
    indent += " ";
    if (Expr != nullptr) {
      output = output + Expr->to_string(indent); // <Expr> is the child of <Expr Statement>, so indent + 1
    }
    return output;
  }
};

// IfStmtAST - Class for if statements
// @arguments: TOKEN tok -- We take the "if" token to indicate the column and row numbers of the if block
//             std::unique_ptr<ExprAST> IfCondition; -- If condition of the block, represented by an expression
//             std::unique_ptr<BlockAST> IfBody;    
//             std::unique_ptr<BlockAST> Else;
class IfStmtAST: public StatementAST {
  TOKEN tok;
  std::unique_ptr<ExprAST> IfCondition;
  std::unique_ptr<BlockAST> IfBody;
  std::unique_ptr<BlockAST> Else;

public:
  IfStmtAST(TOKEN tok,
  std::unique_ptr<ExprAST> IfCondition,
  std::unique_ptr<BlockAST> IfBody,
  std::unique_ptr<BlockAST> Else): 
  tok(tok), IfCondition(std::move(IfCondition)), 
  IfBody(std::move(IfBody)), Else(std::move(Else)) {}

  virtual Value *codegen() override;

  virtual std::string to_string(std::string indent) const override {
    std::string output = indent + "<if statement>" + printLCNo(tok) + "\n";
    indent += " ";
    output += indent + "<If Condition>\n"; // If condition, If body and Else body (if any) are children of <If statement>, so indent + 1
    output = output + IfCondition->to_string(indent + " ");
    output += indent + "<If Body>\n";      
    output = output + IfBody->to_string(indent + " ");
    output += indent + "<Else Body>\n";
    output = output + Else->to_string(indent + " ");
    return output;
  }
};

// WhileStmtAST - Class for while statement
// @arguments: TOKEN tok -- We take the "while" token for the purpose of indicating the row and column number
//             std::unique_ptr<ExprAST> WhileCondition;
//             std::unique_ptr<StatementAST> WhileBody;
class WhileStmtAST: public StatementAST {
  TOKEN tok;
  std::unique_ptr<ExprAST> WhileCondition;
  std::unique_ptr<StatementAST> WhileBody;

public:
  WhileStmtAST(TOKEN tok, std::unique_ptr<ExprAST> WhileCondition, std::unique_ptr<StatementAST> WhileBody): 
    tok(tok), WhileCondition(std::move(WhileCondition)), WhileBody(std::move(WhileBody)) {}

  virtual Value *codegen() override;  
  virtual std::string to_string(std::string indent) const override {
    std::string output = indent + "<While Statement>" + printLCNo(tok) + "\n";
    indent += " "; // <While condition> and <While Body> are children of <While Statement>, so indent + 1
    output += indent + "<While Condition>\n";
    output = output + WhileCondition->to_string(indent + " "); // The <Expr> is the child of <While Condition>, so indent + 1 
    output += indent + "<While Body>\n";
    output = output + WhileBody->to_string(indent + " "); // The <Statement> is the child of <While Body>, so indent + 1
    return output;
  }
};

// ReturnStmtAST -- Class for return statements
// @arguments - TOKEN tok -- We take the "return" token for the purpose of indicating the row and column numbers
//              std::unique_ptr<ExprAST> ReturnExpr -- According to the grammar rules, return_stmt would produce expression, so <Expr> is the child of <Return Statement>
class ReturnStmtAST: public StatementAST {
  TOKEN tok;
  std::unique_ptr<ExprAST> ReturnExpr;

public:
  ReturnStmtAST(TOKEN tok, std::unique_ptr<ExprAST> ReturnExpr): tok(tok), ReturnExpr(std::move(ReturnExpr)) {}

  virtual Value *codegen() override;

  virtual std::string to_string(std::string indent) const override {
    std::string output = indent + "<Return Statement>" + printLCNo(tok) + "\n";
    indent += " "; // <Expr> is the child of <Return Statement>, so indent + 1
    if (ReturnExpr != nullptr) { // Here we first if the return statement has any returned value
      output = output + ReturnExpr->to_string(indent); // If it does, we pass the indent to to_string() function of the returned expression
    }
    else {                      // If it doesn't, we would print out a "<void>" to represent that the return statement has no returning value
      output += indent + "<void>";
    }
    return output;
  }
};


//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

class SyntaxError: public std::exception {
  TOKEN tok;
  std::string ErrorMessage;

public:
  SyntaxError(TOKEN tok, std::string ErrorMessage): tok(tok), ErrorMessage(ErrorMessage) {}
  std::string getMessage() {
    std::string o = "SYNTAX ERROR: " + ErrorMessage + " Line " + std::to_string(tok.lineNo) + " Column " + std::to_string(tok.columnNo) + "\n";
    return o;
  }
};

class SemanticError: public std::exception {
  TOKEN tok;
  std::string ErrorMessage;

public:
  SemanticError(TOKEN tok, std::string ErrorMessage): tok(tok), ErrorMessage(ErrorMessage) {}
  std::string getMessage() {
    std::string o = "SEMANTIC ERROR: " + ErrorMessage + " Line " + std::to_string(tok.lineNo) + " Column " + std::to_string(tok.columnNo) + "\n";
    return o;
  }
};

// CurTok/gettok - Provide a simple token buffer.  CurTok is the current
// token the parser is looking at.  gettok reads another token from the
// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken() {

  if (tok_buffer.size() == 0)
    tok_buffer.push_back(gettok());

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static void putBackToken(TOKEN tok) { 
  tok_buffer.push_front(CurTok);
  CurTok = tok;
}


// Forward declarations of the parse functions
static std::unique_ptr<ProgramAST> parseProgram();
static std::vector<std::unique_ptr<ASTnode>> parseExtern_List();
static std::unique_ptr<ASTnode> parseExtern();
static std::vector<std::unique_ptr<DeclAST>> parseDecl_List();
static std::unique_ptr<DeclAST> parseDecl();
static std::unique_ptr<VariableDeclAST> parseVarDecl();
static std::unique_ptr<FuncDeclAST> parseFuncDecl();
static std::unique_ptr<BlockAST> parseBlock();
static std::vector<std::unique_ptr<VariableDeclAST>> parseLocal_Decls();
static std::vector<std::unique_ptr<StatementAST>> parseStmt_list();
static std::unique_ptr<StatementAST> parseStmt();
static std::unique_ptr<ExprStmtAST> parseExprStmt();
static std::unique_ptr<WhileStmtAST> parseWhileStmt();
static std::unique_ptr<IfStmtAST> parseIfStmt();
static std::unique_ptr<BlockAST> parseElseStmt();
static std::unique_ptr<ReturnStmtAST> parseReturnStmt();
static std::unique_ptr<ExprAST> parseExpr();
static std::unique_ptr<ExprAST> parseOr_Rval();
static std::unique_ptr<ExprAST> parseAnd_Rval();
static std::unique_ptr<ExprAST> parseEquality_Rval();
static std::unique_ptr<ExprAST> parseRelational_Rval();
static std::unique_ptr<ExprAST> parseAdditive_Rval();
static std::unique_ptr<ExprAST> parseMulti_Rval();
static std::unique_ptr<ExprAST> parseUnary_Rval();
static TOKEN parseFunctionType();
static TOKEN parseVarType();
static std::vector<std::unique_ptr<ParameterAST>> parseParams();
static std::vector<std::unique_ptr<ParameterAST>> parseParam_List();
static std::unique_ptr<ParameterAST> parseParameter();


// parse the root node
static std::unique_ptr<ProgramAST> parser() {
  getNextToken();
  return parseProgram();
}

// program ::= extern_list decl_list
//          |  decl_list
static std::unique_ptr<ProgramAST> parseProgram() {
  std::vector<std::unique_ptr<ASTnode>> Extern_List;
  // Create vector of extern Prototypes

  if (CurTok.type == EXTERN) {
  // "extern" is in FIRST SET of extern_list
    Extern_List = parseExtern_List();
  }

  // parse decl_list
  auto Decl_List = parseDecl_List();

  return std::make_unique<ProgramAST>(std::move(Extern_List), std::move(Decl_List));
}

// extern_list ::= extern extern_list'
// extern_list' ::= extern extern_list'
//              |  epsilon
static std::vector<std::unique_ptr<ASTnode>> parseExtern_List() {
  auto Extern = parseExtern();
  // Parse the first [extern] we encounter

  std::vector<std::unique_ptr<ASTnode>> Extern_List;
  Extern_List.push_back(std::move(Extern));

  // If CurTok.type == EXTERN, then we know we have more [extern] following and we will try to parse the externs
  while (CurTok.type == EXTERN) {
    Extern = parseExtern();
    Extern_List.push_back(std::move(Extern));
  }
  // If CurTok.type != EXTERN, we know the last [extern_list'] produces epsilon, then we completed the parsing of [extern_list]

  return std::move(Extern_List);
}

// extern ::= "extern" type_spec IDENT "(" params ")" ";"
//          | "extern" type_spec IDENT "(" ")" ";"    
static std::unique_ptr<ASTnode> parseExtern() {
  if (CurTok.type != EXTERN) {
    throw SyntaxError(CurTok, "Expected 'extern' keyword");
  }

  getNextToken(); // eat "extern"
  auto Type = parseFunctionType(); 
  // Consume [type] token

  if (CurTok.type != IDENT) {
    throw SyntaxError(CurTok, "Expected IDENT");
  }
  TOKEN identifier = CurTok;
  getNextToken(); // eat IDENT

  if (CurTok.type != LPAR) {
    throw SyntaxError(CurTok, "Expected '('");
  }
  getNextToken(); // eat "("
  
  std::vector<std::unique_ptr<ParameterAST>> Params;
  Params = parseParams();
  
  if (CurTok.type != RPAR) {
    throw SyntaxError(CurTok, "Expected ')'");
  }
  getNextToken(); // eat ")"

  if (CurTok.type != SC) {
    throw SyntaxError(CurTok, "Expected ;");
  }
  getNextToken(); // eat ";"

  return std::make_unique<PrototypeAST>(Type, identifier, std::move(Params));
}

// decl_list ::= decl decl_list'
// decl_list' ::= decl decl_list' | epsilon
static std::vector<std::unique_ptr<DeclAST>> parseDecl_List() {
  auto Decl = parseDecl();
  // Parse the first [decl] we encounter
  
  std::vector<std::unique_ptr<DeclAST>> Decls;
  Decls.push_back(std::move(Decl));

  // If CurTok.type is in the first set of [decl], then we know we have more [decl] following and we will try to parse the [decl]s
  while (CurTok.type == VOID_TOK || CurTok.type == INT_TOK || CurTok.type == BOOL_TOK || CurTok.type == FLOAT_TOK) {
    Decl = parseDecl();
    Decls.push_back(std::move(Decl));
  }
  // If CurTok.type is not in the first set of [decl], we know the last [decl_list'] produces epsilon, then we completed the parsing of [decl_list]

  return Decls;
}

// decl ::= var_decl
//        | func_decl
static std::unique_ptr<DeclAST> parseDecl() {
  TOKEN t1 = CurTok;
  TOKEN t2 = getNextToken();
  TOKEN t3 = getNextToken();
  putBackToken(t2);
  putBackToken(t1);
  // We look ahead for 2 tokens since first and second symbols of [var_decl] and [func_decl] are the same.
  // After the lookahead, we put back the tokens for correct parsing
  
  // If 3rd symbol is ";", we know it is [var_decl]
  if (t3.type == SC) {
    return parseVarDecl();
  }
  // If 3rd symbol is "(", we know it is [func_decl]
  else {
    return parseFuncDecl();
  }
}

// var_decl ::= var_type IDENT ";"
static std::unique_ptr<VariableDeclAST> parseVarDecl() {
  auto type = parseVarType();
  // Parse the [var_type] symbol

  if (CurTok.type != IDENT) {
    throw SyntaxError(CurTok, "Expected IDENT");
  } // Throw Error
  TOKEN identifier = CurTok;
  getNextToken(); // eat IDENT

  if (CurTok.type != SC) {
    throw SyntaxError(CurTok, "Expected ;");
  }
  getNextToken(); // eat ";"

  return std::make_unique<VariableDeclAST>(type, identifier);
}

// func_decl ::= "void" IDENT "(" params ")" block
//            |  var_type IDENT "(" ")" block
static std::unique_ptr<FuncDeclAST> parseFuncDecl() {
  auto type = parseFunctionType();
  // "void" and [var_type]

  if (CurTok.type != IDENT) {
    throw SyntaxError(CurTok, "Expected IDENT");
  } // Throw Error
  TOKEN identifier = CurTok; // Store the name of the function for creation of <FuncDeclAST> instance
  getNextToken();

  if (CurTok.type != LPAR) {
    throw SyntaxError(CurTok, "Expected '(' at Line " +
                      std::to_string(CurTok.lineNo) + " Column " + 
                      std::to_string(CurTok.columnNo) + "\n");
  }
  getNextToken(); // eat "("

  std::vector<std::unique_ptr<ParameterAST>> Params = parseParams();
  auto Func_Decl = std::make_unique<PrototypeAST>(type, identifier, std::move(Params));
  if (CurTok.type != RPAR) {
    throw SyntaxError(CurTok, "Expected ')'");
  }
  getNextToken(); // eat ")"

  auto Block = parseBlock();

  return std::make_unique<FuncDeclAST>(identifier, std::move(Func_Decl), std::move(Block));
}

// var_type ::= "int" | "float" | "bool"
static TOKEN parseVarType() {
  if (CurTok.type != INT_TOK && 
      CurTok.type != FLOAT_TOK && 
      CurTok.type != BOOL_TOK) {
    throw SyntaxError(CurTok, "Expected");
  }
  
  //if (CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK) {
  TOKEN type = CurTok;
  getNextToken(); // eat var_type
  return type;
  //} 
}

// params ::= param_list
//          | "void"
static std::vector<std::unique_ptr<ParameterAST>> parseParams() {
  std::vector<std::unique_ptr<ParameterAST>> Params;

  if (CurTok.type == VOID_TOK) {
    getNextToken(); // eat "void"
  }
  else if (CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK) {
    Params = parseParam_List();
  }

  return std::move(Params);
}

// param_list ::= param param_list'
// param_list' ::= "," param param_list'
//               | epsilon
static std::vector<std::unique_ptr<ParameterAST>> parseParam_List() {
  auto param = parseParameter();
  std::vector<std::unique_ptr<ParameterAST>> Parameters;
  Parameters.push_back(std::move(param));
  if (CurTok.type == COMMA) {
    getNextToken(); // eat ","
    while (CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK) {
      // Parse the parameter AST node
      auto param = parseParameter();
      Parameters.push_back(std::move(param));

      if (CurTok.type == COMMA) {
        getNextToken(); // eat ","
      }
      // If the next token is ",", eat "," and go to the next parameter
    }
  }
  return std::move(Parameters);
}

// param ::= var_type IDENT
static std::unique_ptr<ParameterAST> parseParameter() {
  TOKEN type = parseVarType();
  
  if (CurTok.type != IDENT) {
    throw SyntaxError(CurTok, "Expected IDENT");
  } // Error
  TOKEN identifier = CurTok;
  getNextToken(); // eat IDENT
  return std::make_unique<ParameterAST>(type, identifier);
}

// Check first set of stmt
static bool firstSet_stmt(TOKEN tok) {
  if (tok.type == LBRA || tok.type == SC || tok.type == MINUS || tok.type == NOT || tok.type == LPAR ||
      tok.type == IDENT || tok.type == INT_LIT || tok.type == FLOAT_LIT || tok.type == BOOL_LIT ||
      tok.type == WHILE || tok.type == IF || tok.type == RETURN) {
        return true;
      }
  return false;
}

// block ::= "{" local_decls stmt_list "}"
static std::unique_ptr<BlockAST> parseBlock() {
  if (CurTok.type != LBRA) {
    throw SyntaxError(CurTok, "Expected '{'");
  } //Throw error
  getNextToken(); // eat "{"
  std::vector<std::unique_ptr<VariableDeclAST>> local_decls;
  std::vector<std::unique_ptr<StatementAST>> stmt_list;

  if (CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK) {
    local_decls = parseLocal_Decls();
  }

  if (firstSet_stmt(CurTok)) {
    stmt_list = parseStmt_list();
  }

  if (CurTok.type != RBRA) { // Throw Error 
    throw SyntaxError(CurTok, "Expected '}'");
  }
  getNextToken();

  return std::make_unique<BlockAST>(std::move(local_decls), std::move(stmt_list));
}



// local_decls ::= local_decl local_decls'
// local_decls' ::= local_decl local_decls' | epsilon
static std::vector<std::unique_ptr<VariableDeclAST>> parseLocal_Decls() {
  std::vector<std::unique_ptr<VariableDeclAST>> local_decls;
  local_decls.push_back(parseVarDecl());

  // go to while lopp to consume local_decls'
  while (CurTok.type == INT_TOK || CurTok.type == BOOL_TOK || CurTok.type == FLOAT_TOK) {
    auto local_decl = parseVarDecl();
    local_decls.push_back(std::move(local_decl));
  }

  return std::move(local_decls);
}

// stmt_list ::= stmt_list'
// stmt_list' ::= stmt stmt_list' | epsilon
static std::vector<std::unique_ptr<StatementAST>> parseStmt_list() {
  std::vector<std::unique_ptr<StatementAST>> Stmt_list;
  Stmt_list.push_back(parseStmt());

  while (firstSet_stmt(CurTok)) {
    Stmt_list.push_back(parseStmt());
  }
  return std::move(Stmt_list);
}

// stmt ::= expr_stmt 
//      |  block 
//      |  if_stmt 
//      |  while_stmt 
//      |  return_stmt
static std::unique_ptr<StatementAST> parseStmt() {
  switch (CurTok.type) {
    case LBRA:
      return parseBlock();
    case IF:
      return parseIfStmt();
    case WHILE:
      return parseWhileStmt();
    case RETURN:
      return parseReturnStmt();
    case IDENT:
    case MINUS: 
    case NOT:
    case LPAR:
    case INT_LIT:
    case FLOAT_LIT:
    case BOOL_LIT: 
    case SC:
    {
      auto Expr = parseExprStmt();
      return std::move(Expr);
    }
    default:
      return nullptr;
  }
}

// expr_stmt ::= expr ";" | ";"
static std::unique_ptr<ExprStmtAST> parseExprStmt() {
  if (CurTok.type == SC) {
    TOKEN tok = CurTok;
    getNextToken(); // Eat ";"
    return std::make_unique<ExprStmtAST>(tok, nullptr);
  }
  TOKEN expr_tok = CurTok;
  auto Expr = parseExpr();
  if (CurTok.type != SC) {
    throw SyntaxError(CurTok, "Expected ';'");
  }
  getNextToken(); // eat ";"
  return std::make_unique<ExprStmtAST>(expr_tok, std::move(Expr));
}

// expr ::= IDENT "=" expr
//        | or_rval
static std::unique_ptr<ExprAST> parseExpr() {
  // IDENT is in first set of rval, so we need a lookahead
  TOKEN t1 = CurTok;
  TOKEN t2 = getNextToken();

  if (t1.type == IDENT && t2.type == ASSIGN) {
    getNextToken(); 
    // eat "="

    auto Expr = parseExpr();
    return std::make_unique<AssignmentAST>(t1, std::move(Expr));
  }
  
  putBackToken(t1);

  return parseOr_Rval();
}

// while_stmt ::= "while" "(" expr ")" stmt
static std::unique_ptr<WhileStmtAST> parseWhileStmt() {
  if (CurTok.type != WHILE) {
    throw SyntaxError(CurTok, "Expected 'while' keyword");
  }
  TOKEN while_tok = CurTok;
  getNextToken();
  // eat "while"

  if (CurTok.type != LPAR) {
    throw SyntaxError(CurTok, "Expected '('");
  }
  getNextToken();
  // eat "("

  auto Expr = parseExpr();

  if (CurTok.type != RPAR) {
    throw SyntaxError(CurTok, "Expected ')'");
  } // Throw Error
  getNextToken();
  // eat ")"

  auto Stmt = parseStmt();

  return std::make_unique<WhileStmtAST>(while_tok, std::move(Expr), std::move(Stmt));

}

// if_stmt ::= "if" "(" expr ")" block else_stmt
//          |  "if" "(" expr ")" block
static std::unique_ptr<IfStmtAST> parseIfStmt() {
  if (CurTok.type != IF) {
    throw SyntaxError(CurTok, "Expected 'if' keyword");
  }

  TOKEN if_tok = CurTok;
  getNextToken();
  // eat "if"

  if (CurTok.type != LPAR) {
    throw SyntaxError(CurTok, "Expected '('");
  }

  getNextToken();
  // eat "("

  auto Expr = parseExpr();

  if (CurTok.type != RPAR) {
    throw SyntaxError(CurTok, "Expected ')'");
  }
  
  getNextToken();
  // eat ")"

  auto ifBody = parseBlock();
  
  std::unique_ptr<BlockAST> Else_Block = nullptr;
  // We assume there is no else statement by default
  if (CurTok.type == ELSE) {
    Else_Block = parseElseStmt();
  }
  auto IfStmt = std::make_unique<IfStmtAST>(if_tok, std::move(Expr), std::move(ifBody), std::move(Else_Block));
  return std::move(IfStmt);
}

// else_stmt ::= "else" block
static std::unique_ptr<BlockAST> parseElseStmt() {
  if (CurTok.type != ELSE) {
    throw SyntaxError(CurTok, "Expected 'else' keyword");
  }
  getNextToken();
  // eat "else"

  auto Block = parseBlock();
  return std::move(Block);
}

// return_stmt ::= "return" ";"
//               | "return" expr ";"
static std::unique_ptr<ReturnStmtAST> parseReturnStmt() {
  if (CurTok.type != RETURN) {
    throw SyntaxError(CurTok, "Expected 'return' keyword");
  }
  TOKEN return_tok = CurTok;
  getNextToken();
  // eat "return"

  std::unique_ptr<ExprAST> Expr = nullptr;
  if (CurTok.type == SC) {
    getNextToken(); // eat ";"
    return std::make_unique<ReturnStmtAST>(return_tok, std::move(Expr));
  }

  Expr = parseExpr();
  if (CurTok.type != SC) {
    throw SyntaxError(CurTok, "Expected ';'");
  }
  getNextToken(); // eat ";"
  return std::make_unique<ReturnStmtAST>(return_tok, std::move(Expr));
}



// or_rval ::= and_rval or_rest
// or_rest ::= "||" and_rval or_rest | ε
static std::unique_ptr<ExprAST> parseOr_Rest(std::unique_ptr<ExprAST> LHS) {
  while (CurTok.type == OR) {
    TOKEN or_op = CurTok;
    getNextToken();
    // eat "||"
    
    auto RHS = parseOr_Rval();
    LHS = std::make_unique<BinaryOpAST>(or_op, std::move(LHS), std::move(RHS));
  }
  return std::move(LHS);
}

static std::unique_ptr<ExprAST> parseOr_Rval() {
  auto LHS = parseAnd_Rval();
  LHS = parseOr_Rest(std::move(LHS));
  return std::move(LHS);
}

// and_rval ::= equality_rval and_rest
// and_rest ::= "&&" equality_rval and_rest | ε
static std::unique_ptr<ExprAST> parseAnd_Rest(std::unique_ptr<ExprAST> LHS) {
  while (CurTok.type == AND) {
      TOKEN and_op = CurTok;
      getNextToken();
      // eat "&&"
      
      auto RHS = parseAnd_Rval();
      LHS = std::make_unique<BinaryOpAST>(and_op, std::move(LHS), std::move(RHS));
  }

  return std::move(LHS);
}
static std::unique_ptr<ExprAST> parseAnd_Rval() {
  auto LHS = parseEquality_Rval();
  LHS = parseAnd_Rest(std::move(LHS));
  return std::move(LHS);
}

// equality_rval ::= relational_rval equality_rest
// equality_rest ::= "==" relational_rval equality_rest 
//                | "!=" relational_rval equality_rest 
//                | ε
static std::unique_ptr<ExprAST> parseEquality_Rest(std::unique_ptr<ExprAST> LHS) {
  while (CurTok.type == EQ || CurTok.type == NE) {
    TOKEN equality_op = CurTok;
    getNextToken();
    // eat "==" or "!="
    
    auto RHS = parseEquality_Rval();
    LHS = std::make_unique<BinaryOpAST>(equality_op, std::move(LHS), std::move(RHS));
  }

    return std::move(LHS);
}
static std::unique_ptr<ExprAST> parseEquality_Rval() {
  auto LHS = parseRelational_Rval();
  LHS = parseEquality_Rest(std::move(LHS));
  return std::move(LHS);
}

// relational_expr ::= additive_expr relational_rest
// relational_rest ::= "<=" additive_expr relational_rest
//                   | "<" additive_expr relational_rest
//                   | ">=" additive_expr relational_rest
//                   | ">" additive_expr) relational_rest 
//                   | ε
static std::unique_ptr<ExprAST> parseRelational_Rest(std::unique_ptr<ExprAST> LHS) {
  while (CurTok.type == LE || CurTok.type == LT || CurTok.type == GE || CurTok.type == GT) {
      TOKEN relational_op = CurTok;
      getNextToken();
      // eat ">=", "<=", ""> or "<"
      
      auto RHS = parseRelational_Rval();
      LHS = std::make_unique<BinaryOpAST>(relational_op, std::move(LHS), std::move(RHS));
    }
  return std::move(LHS);
}
static std::unique_ptr<ExprAST> parseRelational_Rval() {
  auto LHS = parseAdditive_Rval();
  LHS = parseRelational_Rest(std::move(LHS));
  return std::move(LHS); 
  
}

static std::unique_ptr<ExprAST> parseAdditive_Rest(std::unique_ptr<ExprAST> LHS);
// additive_rval ::= multiplicative_rval additive_rest
// additive_rest ::= "+" multiplicative_rval additive_rest | 
//                   "-" multiplicative_rval additive_rest | ε
static std::unique_ptr<ExprAST> parseAdditive_Rval() {
  auto LHS = parseMulti_Rval();
  LHS = parseAdditive_Rest(std::move(LHS));
  return std::move(LHS); 
}

static std::unique_ptr<ExprAST> parseAdditive_Rest(std::unique_ptr<ExprAST> LHS) {
  while (CurTok.type == PLUS || CurTok.type == MINUS) {
    TOKEN additive_op = CurTok;
    getNextToken();

    auto RHS = parseMulti_Rval();
    LHS = std::make_unique<BinaryOpAST>(additive_op, std::move(LHS), std::move(RHS));
  }
  return std::move(LHS);
}

static std::unique_ptr<ExprAST> parseMulti_Rest(std::unique_ptr<ExprAST> LHS);
// multiplicative_expr ::= unary_expr multiplicative_rest

static std::unique_ptr<ExprAST> parseMulti_Rval() {
  auto LHS = parseUnary_Rval();
  LHS = parseMulti_Rest(std::move(LHS));
  return std::move(LHS); 
}

// multiplicative_rest ::= "*" unary_expr multiplicative_rest
//                       | "/" unary_expr multiplicative_rest
//                       | "%" unary_expr multiplicative_rest | ε
static std::unique_ptr<ExprAST> parseMulti_Rest(std::unique_ptr<ExprAST> LHS) {
  while (CurTok.type == ASTERIX || CurTok.type == DIV || CurTok.type == MOD) {
    TOKEN multi_op = CurTok;
    getNextToken();
    auto RHS = parseUnary_Rval();
    LHS = std::make_unique<BinaryOpAST>(multi_op, std::move(LHS), std::move(RHS));
  }
  return std::move(LHS);
}

// unary_rval ::= "-" unary_rval    
//            | "!" unary_rval 
//            | "(" expr ")" 
//            | IDENT
//            | IDENT "(" ")"
//            | IDENT "(" args ")"
//            | INT_LIT 
//            | FLOAT_LIT 
//            | BOOL_LIT
static std::unique_ptr<ExprAST> parseUnary_Rval() {
  switch (CurTok.type) {
    case MINUS: 
    case NOT: {
    TOKEN unary_op = CurTok;
    getNextToken();

    auto unary_expr = parseUnary_Rval();

    return std::make_unique<UnaryExprAST>(unary_op, std::move(unary_expr));
    }
    case LPAR: {
      getNextToken();
      // eat "("
      auto Expr = parseExpr();
      if (CurTok.type != RPAR) {
        throw SyntaxError(CurTok, "Expected ')'");
      }
      getNextToken();
      // eat ")"
      return std::move(Expr);
    }
    case INT_LIT: {
      TOKEN int_lit = CurTok;
      getNextToken();
      // eat INT_LIT
      return std::make_unique<IntAST>(int_lit);
    }
    case FLOAT_LIT: {
      TOKEN float_lit = CurTok;
      getNextToken();

      return std::make_unique<FloatAST>(float_lit);
    }
    case BOOL_LIT: {
      TOKEN bool_lit = CurTok;
      getNextToken();

      return std::make_unique<BoolAST>(bool_lit);
    }
    case IDENT: {
      TOKEN identifier = CurTok;
      getNextToken();
      if (CurTok.type == LPAR) {
        getNextToken();
        // EAT "("

        std::vector<std::unique_ptr<ExprAST>> args;
        if (CurTok.type == RPAR) {
          return std::make_unique<FunctionCallAST>(identifier, std::move(args));
        }

        while (CurTok.type == MINUS || CurTok.type == NOT || CurTok.type == IDENT ||
          CurTok.type == INT_LIT || CurTok.type == FLOAT_LIT || CurTok.type == BOOL_LIT) {
            auto Expr = parseExpr();
            args.push_back(std::move(Expr));

            if (CurTok.type == COMMA) {
              getNextToken();
              // eat ","
            }
        }

        if (CurTok.type != RPAR) { 
          throw SyntaxError(CurTok, "Expected ')'");
          // throw error
        }
        getNextToken();
        // eat ")"
        return std::make_unique<FunctionCallAST>(identifier, std::move(args));
      }
      return std::make_unique<VariableAST>(identifier);
    }
    default:
      return nullptr;
  }
}


// type_spec ::= "void" | var_type
static TOKEN parseFunctionType() {
  if (CurTok.type == VOID_TOK) {
    TOKEN type = CurTok;
    getNextToken(); // eat "void"
    return type;
  } 
  else {
    return parseVarType(); // Get use of var_type parse function
  }
}



//===----------------------------------------------------------------------===//
// Top-Level parsing
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */


//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, AllocaInst*> NamedValues;
static std::map<std::string, Value *> GlobalNamedValues; 
static std::deque<std::map<std::string, AllocaInst*>> Scope;

Type* getTokenType(int type);

int main(int argc, char ** argv);


Value *castBool(Value* input, std::string StmtType);

Constant* getInitializer(int type) {
  switch(type) {
    case INT_TOK:
      return (Constant *) ConstantInt::get(getTokenType(INT_TOK), 0, true);
    case BOOL_TOK:
      return (Constant *) ConstantInt::get(getTokenType(BOOL_TOK), 0, true);
    case FLOAT_TOK:
      return (Constant *) ConstantFP::get(getTokenType(FLOAT_TOK), 0.0);
    default:
      break;
  }

  return nullptr;
}

// Cast int or bool to float
Value* castFloat(Value* Val) {
  return Builder.CreateCast(Instruction::SIToFP, Val, getTokenType(FLOAT_TOK), "cast");
}

static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
                                          const std::string &VarName,
                                          Type *type) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(),TheFunction->getEntryBlock().begin());
  return TmpB.CreateAlloca(type, nullptr, VarName);
}

// find the variable in the scopes other than Global Variables
AllocaInst* findVariable(std::string VarName) {
  for (auto &Local_Scope: Scope) {
    auto Val = Local_Scope[VarName];
    if (Val) {
      return Val;
    }
  }
  return nullptr;
}

Function *getFunction(std::string Name) {
  // First, see if the function has already been added to the current module.
  if (auto *F = TheModule->getFunction(Name))
    return F;

  // If no existing prototype exists, return null.
  return nullptr;
}

// Get the bool value of input
Value* getBoolValue(bool input) {
  return ConstantInt::get(getTokenType(BOOL_TOK), int(input), true);
}

// Get the float value of input
Value* getFloatValue(float input) {
  return ConstantFP::get(getTokenType(FLOAT_TOK), input);
}

// Check if the first arg is narrowing conversion from the second arg
bool IsNarrowingConversion(Type *VariableType, Type *AssignedType) {
  if (VariableType == Type::getInt32Ty(TheContext)) {
     if (AssignedType == Type::getFloatTy(TheContext)) {
      return true;
     }
  }
  else if (VariableType == Type::getInt1Ty(TheContext)) {
    if (AssignedType == Type::getInt32Ty(TheContext) ||
        AssignedType == Type::getFloatTy(TheContext)) {
          return true;
        }
  }
  return false;
}

// Get string form of three variable types
std::string getTypeStr(Type *type) {
  if (type == Type::getInt32Ty(TheContext))
    return "int";
  else if (type == Type::getInt1Ty(TheContext))
    return "bool";
  else 
    return "float";
}

// @arguments: Value* input
// Output: Value* boolean value output
Value *castBool(Value* input, std::string Label) {
  Type* input_type = input->getType();
  if (input_type == getTokenType(FLOAT_TOK)) {
    return Builder.CreateFCmpONE(input, getFloatValue(0.0), Label.c_str());
  }
  else {
    return Builder.CreateICmpNE(input, getBoolValue(false), Label.c_str());
  }
}

// ProgramAST::codegen()
Value* ProgramAST::codegen() {
  for (const auto &Extern: Extern_List) {
    Extern->codegen();
  }

  for (const auto &Decl: Decl_List) {
    Decl->codegen();
  }

  return ConstantInt::get(TheContext, APInt(32, 1));
}

Value *ParameterAST::codegen() {
  return ConstantInt::get(TheContext, APInt(32, 1));
}

Function* PrototypeAST::codegen() {
  // Get arguments' types
  std::vector<Type*> args_type;
  for (auto& Arg: Args) {
    // Arg is an instance of ParameterAST
    args_type.push_back(getTokenType(Arg->getType()));
  }
  
  // Get Return type
  Type* Return_type = getTokenType(type.type);
  
  FunctionType* FT = FunctionType::get(Return_type, args_type, false);
  Function *F = Function::Create(FT, Function::ExternalLinkage, prototype_name.lexeme, TheModule.get());

  unsigned int i = 0;
  for (auto& arg : F->args()) {
    arg.setName(Args[i++]->getName()); 
  }
  return F;
}

// [var_decl] 
Value* VariableDeclAST::codegen() {
  if (TheModule->getNamedGlobal(identifier.lexeme)) {
    throw SemanticError(identifier, "Redeclaration of variable '" + identifier.lexeme + "'");
  }

  Constant *initializer = getInitializer(type.type);
  assert(initializer);

  GlobalVariable *GV = new GlobalVariable(*TheModule, getTokenType(type.type), false,
                        GlobalVariable::ExternalLinkage, initializer,
                        identifier.lexeme);
  assert(GV);

  return GV;
}

Value* VariableDeclAST::codegen(bool isNotGlobal) {
  if (Scope.front()[identifier.lexeme]) {
    throw SemanticError(identifier, "Redeclaration of '" + identifier.lexeme + "'");
  }
  
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  Type *VarType = getTokenType(type.type);
  AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, identifier.lexeme, VarType);
  assert(Alloca);

  Constant *StartVal = getInitializer(type.type);
  assert(StartVal);

  Builder.CreateStore(StartVal, Alloca);

  Scope.front()[identifier.lexeme] = Alloca;
  return StartVal;
}

Function* FuncDeclAST::codegen() {
  // First, check for an existing function from a previous "extern" declaration
  Function *TheFunction = TheModule->getFunction(prototype->getName());

  if (!TheFunction) {
    TheFunction = prototype->codegen();
  }

  if (!TheFunction->empty()) {
    std::string Output = "Duplicate definition of function '" + prototype->getName() + "'";
    throw SemanticError(identifier, Output);
  }

  BasicBlock *BB = BasicBlock::Create(TheContext, "Function Body", TheFunction);
  Builder.SetInsertPoint(BB);

  std::map<std::string, AllocaInst*> Local_Scope;
  for (auto &arg: TheFunction->args()) {
    Type *type = arg.getType();
    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, std::string(arg.getName()), type);
    Builder.CreateStore(&arg, Alloca);
    Local_Scope[std::string(arg.getName())] = Alloca;
  }

  Scope.push_front(Local_Scope);

  if (Value *ReturnVal = func_body->codegen()) {
    verifyFunction(*TheFunction);
    return TheFunction;
  }

  TheFunction->eraseFromParent();
  return nullptr;
}


// BlockAST needs to return a Value* for FuncDeclAST to have a return value.
Value* BlockAST::codegen() {
  std::map<std::string, AllocaInst*> Local_Scope;
  Scope.push_front(Local_Scope);
  
  for (const auto& local_decl: local_decls) {
    local_decl->codegen(true);
  }

  for (auto& stmt: stmt_list) {
    stmt->codegen();
  }

  Scope.pop_front();
  return ConstantInt::get(TheContext, APInt(32, 1));
  // return a default value
}

Value *ExprStmtAST::codegen() {
  Value *Val = nullptr;
  
  if (Expr != nullptr) {
    Val = Expr->codegen();
  }

  return Val;
}

Value *IfStmtAST::codegen() {
  Value *CondV = IfCondition->codegen();
  CondV = castBool(CondV, "IfCondition");
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  BasicBlock *ThenBB = BasicBlock::Create(TheContext, "then", TheFunction);
  BasicBlock *ElseBB = nullptr;
  if (Else != nullptr) {
    ElseBB = BasicBlock::Create(TheContext, "else");
  }
  BasicBlock *MergeBB = BasicBlock::Create(TheContext, "IfContd");

  if (Else != nullptr)
    Builder.CreateCondBr(CondV, ThenBB, ElseBB);
  else 
    Builder.CreateCondBr(CondV, ThenBB, MergeBB);

  Builder.SetInsertPoint(ThenBB);
  Value *ThenV = IfBody->codegen();
  Builder.CreateBr(MergeBB);
  if (Else != nullptr) {
    TheFunction->insert(TheFunction->end(), ElseBB);
    Builder.SetInsertPoint(ElseBB);
    Value *ElseV = Else->codegen();
    Builder.CreateBr(MergeBB);
  }

  TheFunction->insert(TheFunction->end(), MergeBB);
  Builder.SetInsertPoint(MergeBB);
  return ConstantInt::get(getTokenType(INT_TOK), 1, true);
}

Value *WhileStmtAST::codegen() {
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  BasicBlock *WhileHeaderBB = BasicBlock::Create(TheContext, "WhileHeader", TheFunction);

  Builder.CreateBr(WhileHeaderBB);
  Builder.SetInsertPoint(WhileHeaderBB);

  Value *CondV = WhileCondition->codegen();
  assert(CondV);

  CondV = castBool(CondV, "WhileCondition");

  BasicBlock *WhileBodyBB = BasicBlock::Create(TheContext, "WhileBody", TheFunction);
  BasicBlock *WhileContdBB = BasicBlock::Create(TheContext, "WhileContd", TheFunction);

  Builder.CreateCondBr(CondV, WhileBodyBB, WhileContdBB);

  Builder.SetInsertPoint(WhileBodyBB);
  WhileBody->codegen();
  Builder.CreateBr(WhileHeaderBB);

  Builder.SetInsertPoint(WhileContdBB);

  return ConstantInt::get(TheContext, APInt(32, 1));
}

Value *ReturnStmtAST::codegen() {
  Function *TheFunction = Builder.GetInsertBlock()->getParent();

  Type *FuncReturnType = TheFunction->getReturnType();

  if (FuncReturnType == Type::getVoidTy(TheContext) && ReturnExpr != nullptr) {
    throw SemanticError(tok, "Can't return a value from a void function");
  }

  if (FuncReturnType != Type::getVoidTy(TheContext) && ReturnExpr == nullptr) {
    throw SemanticError(tok, "Must return a value from a non-void function");
  }

  Value *Val;
  if (ReturnExpr != nullptr) {
    Val = ReturnExpr->codegen();
    Type *ReturnedType = Val->getType();
    if (IsNarrowingConversion(FuncReturnType, ReturnedType)) {
      throw SemanticError(tok, "Can't return " + getTypeStr(ReturnedType) + ", wider value for a " + getTypeStr(FuncReturnType) + " function");
    }
    if (FuncReturnType != ReturnedType) {
      if (FuncReturnType == getTokenType(FLOAT_TOK)) {
        Val = Builder.CreateCast(Instruction::SIToFP, Val, getTokenType(FLOAT_TOK), "cast");
      }
      if (FuncReturnType == getTokenType(INT_TOK)) {
        Val = Builder.CreateSExt(Val, getTokenType(INT_TOK), "cast");
      }
    }
  }
  else {
    Val = nullptr;
  }
  
  Builder.CreateRet(Val);
  return Val;
}


// Assignment = IDENT "=" expr;
Value *AssignmentAST::codegen() {
  Value *Val = Expr->codegen();
  assert(Val);
  
  Type *AssignedType = Val->getType();
  AllocaInst *Variable = findVariable(identifier.lexeme);

  if (!Variable) {
    Value * GlobalVar = TheModule->getNamedGlobal(identifier.lexeme);
    if (!GlobalVar) {
      std::string ErrorMessage = "Unknown variable name '" + identifier.lexeme + "'";
      throw SemanticError(identifier, ErrorMessage);
    }
    Type* GlobalVarType = GlobalVar->getType();
    Builder.CreateStore(Val, GlobalVar);
    return Val;
  }

  if (!Variable) {
    std::string ErrorMessage = "Unknown variable name '" + identifier.lexeme + "'";
    throw SemanticError(identifier, ErrorMessage);
  }
  
  Builder.CreateStore(Val, Variable);

  return Val;
}

Value *UnaryExprAST::codegen() {
  Value *Expr = UnaryExpr->codegen();
  assert(Expr);

  bool isFloat = false;
  if (Expr->getType() == getTokenType(FLOAT_TOK)) {
    isFloat = true;
  }

  switch(Operator.type) {
    case NOT:
      return Builder.CreateNot(castBool(Expr, "cast"), "Not");
    case MINUS: {
      if (Expr->getType() == getTokenType(BOOL_TOK)) {
        throw SemanticError(Operator, "Can't negate 'bool' values");
      }
      return isFloat? Builder.CreateBinOp(Instruction::FMul, Expr, ConstantFP::get(getTokenType(FLOAT_TOK), -1.0f), "mul"): 
                      Builder.CreateBinOp(Instruction::Mul, Expr, ConstantInt::get(getTokenType(INT_TOK), -1, true), "mul");
    }                    
    default:
      throw SemanticError(Operator, "Invalid unary operator '" + Operator.lexeme + "'");
  } 
}

Value *BinaryOpAST::codegen() {
  Value *L = LHS->codegen();
  Value *R = RHS->codegen();
  assert(L && R);


  bool isFloat = false;

  if (L->getType() == getTokenType(FLOAT_TOK) || R->getType() == getTokenType(FLOAT_TOK)) {
    isFloat = true;

    if (L->getType() == getTokenType(FLOAT_TOK) && !(R->getType() == getTokenType(FLOAT_TOK))) {
      R = castFloat(R);
    }

    if (!(L->getType() == getTokenType(FLOAT_TOK)) && R->getType() == getTokenType(FLOAT_TOK)) {
      L = castFloat(L);
    }
  }

  switch (Operator.type) {
    case PLUS: 
      return isFloat? Builder.CreateBinOp(Instruction::FAdd, L, R, "add"): Builder.CreateBinOp(Instruction::Add, L, R, "add");
    case MINUS:
      return isFloat? Builder.CreateBinOp(Instruction::FSub, L, R, "sub"): Builder.CreateBinOp(Instruction::Sub, L, R, "sub");
    case ASTERIX:
      return isFloat? Builder.CreateBinOp(Instruction::FMul, L, R, "mul"): Builder.CreateBinOp(Instruction::Mul, L, R, "mul");
    case DIV:
      return isFloat? Builder.CreateBinOp(Instruction::FDiv, L, R, "div"): Builder.CreateBinOp(Instruction::SDiv, L, R, "div");
    case MOD:
      return isFloat? Builder.CreateBinOp(Instruction::FRem, L, R, "mod"): Builder.CreateBinOp(Instruction::SRem, L, R, "mod");
    case EQ: 
      return isFloat? Builder.CreateFCmpOEQ(L, R, "Equal"): Builder.CreateICmpEQ(L, R, "Equal");
    case NE:
      return isFloat? Builder.CreateFCmpONE(L, R, "Not Equal"): Builder.CreateICmpNE(L, R, "Not Equal");
    case LE:
      return isFloat? Builder.CreateFCmpOLE(L, R, "LE"): Builder.CreateICmpSLE(L, R, "LE");
    case LT:
      return isFloat? Builder.CreateFCmpOLT(L, R, "LT"): Builder.CreateICmpSLT(L, R, "LT");
    case GE:
      return isFloat? Builder.CreateFCmpOGE(L, R, "GE"): Builder.CreateICmpSGE(L, R, "GE");
    case GT:
      return isFloat? Builder.CreateFCmpOGT(L, R, "GT"): Builder.CreateICmpSGT(L, R, "GT");
    case OR:
      return Builder.CreateSelect(castBool(L, "cast"), (Value *) ConstantInt::getTrue(TheContext), castBool(R, "cast"), "or");
    case AND:
      return Builder.CreateSelect(castBool(L, "cast"), castBool(R, "cast"), (Value *) ConstantInt::getFalse(TheContext), "and");
    default:
      throw SemanticError(Operator, "Invalid binary operator '" + Operator.lexeme + "'");
  }
}

Value *VariableAST::codegen() {
  std::string VarName = var.lexeme;

  AllocaInst *A = findVariable(VarName);
  if (!A) {
    GlobalVariable* B = TheModule->getNamedGlobal(VarName);
    if (!B) {
      throw SemanticError(var, "Unknown variable name '" + VarName + "'");
    }
    return Builder.CreateLoad(B->getValueType(), B, VarName.c_str());
  }
  if (!A) {
    throw SemanticError(var, "Unknown variable name '" + VarName + "'");
  }
  
  return Builder.CreateLoad(A->getAllocatedType(), A, VarName.c_str());
}

Value *FunctionCallAST::codegen() {
  Function *CalleeF = TheModule->getFunction(function_name.lexeme);
  if (!CalleeF) {
    throw SemanticError(function_name, "Unknown function '" + function_name.lexeme + "' referenced");
  }

  if (CalleeF->arg_size() != args.size()) {
    std::string Output = "Incorrect number of arguments passed to '" + function_name.lexeme + "'";
    throw SemanticError(function_name, Output);
  }

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = args.size(); i != e; ++i) {
    Value* Val = args[i]->codegen();
    assert(Val);
    Type* argument_type = CalleeF->getFunctionType()->getParamType(i);
    Type* passed_type = Val->getType();

    if (IsNarrowingConversion(argument_type, passed_type))
      throw SemanticError(function_name, "Incorrect argument type passed to call to function '" + function_name.lexeme + "'");
    
    if (argument_type != passed_type) {
      if (argument_type == getTokenType(FLOAT_TOK)) {
        Val = Builder.CreateCast(Instruction::SIToFP, Val, getTokenType(FLOAT_TOK), "cast");
      }
      if (argument_type == getTokenType(INT_TOK)) {
        Val = Builder.CreateSExt(Val, getTokenType(INT_TOK), "cast");
      }
    }

    ArgsV.push_back(Val);
  }
  return Builder.CreateCall(CalleeF, ArgsV, "call");
}

Value* IntAST::codegen() {
  int Val = std::stoi(int_literal.lexeme);

  return ConstantInt::get(getTokenType(INT_TOK), Val, true);
}

Value* FloatAST::codegen() {
  double Val = std::stod(float_literal.lexeme);
  return ConstantFP::get(getTokenType(FLOAT_TOK), Val);
}

Value* BoolAST::codegen() {
  if (bool_literal.lexeme == "true") {
    return ConstantInt::getTrue(TheContext);
  }
  else if (bool_literal.lexeme == "false") {
    return ConstantInt::getFalse(TheContext);
  }
  else {
    throw SemanticError(bool_literal, "Wrong boolean value '" + bool_literal.lexeme + "'");
  }
}

Type* getTokenType(int type) {
  switch (type) {
    case VOID_TOK:
      return Type::getVoidTy(TheContext);
    case INT_TOK:
      return Type::getInt32Ty(TheContext);
    case FLOAT_TOK:
      return Type::getFloatTy(TheContext);
    default:
      return Type::getInt1Ty(TheContext);
  }
  return nullptr;
}


//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//



int main(int argc, char **argv) {
  if (argc == 2) {
    pFile = fopen(argv[1], "r");
    if (pFile == NULL)
      perror("Error opening file");
  } else {
    std::cout << "Usage: ./code InputFile\n";
    return 1;
  }
  try {
  // initialize line number and column numbers to zero
    lineNo = 1;
    columnNo = 1;
    fprintf(stderr, "Lexer Finished\n");
    // get the first token
    auto rootNode = parser();
    /*while (CurTok.type != EOF_TOK) {
      fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
              CurTok.type);
    }*/
    std::cout << rootNode->to_string("") << "\n";
    fprintf(stderr, "Parsing Finished\n");

    // Make the module, which holds all the code.
    TheModule = std::make_unique<Module>("mini-c", TheContext);
    // Run the parser now.
    /******************** Start printing final IR **************************/
    // Print out all of the generated code into a file called output.ll
    auto Filename = "output.ll";

    rootNode->codegen();

    std::error_code EC;
    raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

    if (EC) {
      errs() << "Could not open file: " << EC.message();
      return 1;
    }
    TheModule->print(errs(), nullptr); // print IR to terminal
    TheModule->print(dest, nullptr);
    /********************* End printing final IR ****************************/

    fclose(pFile); // close the file that contains the code that was parsed
    return 0;
  }
  catch (SyntaxError e) {
    fprintf(stderr, "%s\n", e.getMessage().c_str());
  }
  catch (SemanticError e) {
    fprintf(stderr, "%s\n", e.getMessage().c_str());
  }
  catch (std::exception e) {
    std::string ErrorMessage = CurTok.lexeme + " at Line " + std::to_string(CurTok.lineNo) + " Column " + std::to_string(CurTok.columnNo);
    fprintf(stderr, "%s\n", ErrorMessage.c_str());
  }
}
