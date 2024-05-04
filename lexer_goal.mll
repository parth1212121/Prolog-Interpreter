{
open Parser_goal    (*AFTER ENSURING THE CORRECTNESS OF PARSER , WE SHALL AIM FOR LANGUAGE ENRICHMENT...(SURFACE_SYNTAX) *)
}

let digits = ['0'-'9']
let integers_raw= ( ['0'-'9']+)

let lower_letters = ['a'-'z']
let upper_letters = ['A'-'Z']
let prime = '''
let underscore = '_'
let alpha_numeric = (digits | lower_letters | upper_letters)
let identifier = (lower_letters | underscore) (alpha_numeric | prime | underscore)*
let strings_constants = (('"') [^ '"']* ('"')) 
let string_constant2= (strings_constants | identifier)
let variable_letters = (upper_letters) (alpha_numeric | prime | underscore)*


rule token = parse
  | [' ' '\t' '\n'] { token lexbuf } 
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { CURLOPEN }
  | '}' { CURLCLOSE }
  | '[' { SQOPEN }
  | ']' { SQCLOSE }
  | ',' { COMMA }
  | ';' { SEMICOLON }
  | '.' { PERIOD }
  | ":-" { ARROW }
  | '='   {EQ}
  | '+'   {PLUS}
  | '-'   {MINUS}
  | '*'   {MULT}
  | '/'   {DIV}
  | '>'   {GT}
  | '<'   {LT}
  | "\\=" {NOT_EQ}
  | '!' {CUT}
  | '|' {PIPE}
  | "fail" {FAIL}
  | identifier as id { IDENTIFIER id }
  | string_constant2 as sc { STRING_CONSTANTS sc }
  | variable_letters as vl { VARIABLES vl }
  | integers_raw as num { CONSTANT (int_of_string num) }
  | eof {EOF}
  | _ { failwith ("Unexpected character: " ^ Lexing.lexeme lexbuf) }


  (*So, Basicallly after recognizing an illiegel token should my Parser halt the program !!!!*)