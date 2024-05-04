//(*Let Parser know what all token is Lex going to give it. *)


%token <string> IDENTIFIER 
%token <string> STRING_CONSTANTS 
%token <string> VARIABLES
%token LPAREN RPAREN COMMA CUT FAIL EQ NOT_EQ SEMICOLON ARROW PIPE PERIOD PLUS MINUS MULT DIV GT LT SQOPEN SQCLOSE CURLOPEN CURLCLOSE EOF
%token <int> CONSTANT

%nonassoc EQ PIPE LT GT
%left PLUS MINUS
%left MULT DIV



%start program
%type <Syntax.program> program  //(*You only need to tell the starting type*)

%%

program:
     clause  {[$1]}
    | clause  program {$1::$2}

clause:
    fact PERIOD  {FactClause $1 }
    | rule PERIOD {RuleClause $1 }

fact:
     atomic_formula { Fact $1 }

rule:
     atomic_formula ARROW body  { Rule ($1, $3) }


atomic_formula:
      predicate_symbol LPAREN term_list RPAREN    { PredicateSymbol ($1, $3) }
    |  term { ConstantAtomicFormula $1 }
    | term EQ term                        {PredicateSymbol("_eq", [$1; $3])}
    | term NOT_EQ term                    {PredicateSymbol("_not_eq", [$1; $3])}
    | term LT term                        {PredicateSymbol("<", [$1; $3])}
    | term GT term                        {PredicateSymbol(">", [$1; $3])}
    | CUT                                 {PredicateSymbol("_cut", [])}


body:
     atomic_formula { [$1] }
    | atomic_formula COMMA body { $1 :: $3 }

term:
     variable { VARIABLES $1 }
    | constant { CONSTANT $1 }
    | string_constant { STRING_CONSTANT $1 }  
    | string_constant_ident { STRING_CONSTANT $1 }  
    | function_symbol LPAREN term_list RPAREN { FunctionSymbol ($1, $3) }
    | list                                {$1}
    | term PLUS term                      {FunctionSymbol("+", [$1; $3])}
    | term MINUS term                     {FunctionSymbol("-", [$1; $3])}
    | term MULT term                      {FunctionSymbol("*", [$1; $3])}
    | term DIV term                       {FunctionSymbol("/", [$1; $3])}


term_list:
      term { [$1] }
    | term COMMA term_list { $1 :: $3 }


goal:            
    atomic_formula { [$1] }
    | atomic_formula COMMA goal { $1 :: $3 }


list:
    SQOPEN SQCLOSE                               {FunctionSymbol("_empty_list", [])}
  | SQOPEN list_body SQCLOSE                     {$2}
;

list_body:
    term                                 {FunctionSymbol("_list", [$1; FunctionSymbol("_empty_list", [])])}
  | term COMMA list_body                 {FunctionSymbol("_list", [$1; $3])}
  | term PIPE term                       {FunctionSymbol("_list", [$1; $3])}
;



variable:
    VARIABLES {$1}

constant:
    CONSTANT {$1}

string_constant:
    STRING_CONSTANTS {$1}

string_constant_ident:
    IDENTIFIER  {$1}

predicate_symbol:
    IDENTIFIER {$1}

function_symbol:
    IDENTIFIER {$1}
