
(* The type of tokens. *)

type token = 
  | XOR_ASSIGN of (Cabs.loc)
  | WHILE of (Cabs.loc)
  | VOLATILE of (Cabs.loc)
  | VOID of (Cabs.loc)
  | VAR_NAME of (string * Pre_parser_aux.identifier_type ref * Cabs.loc)
  | UNSIGNED of (Cabs.loc)
  | UNION of (Cabs.loc)
  | UNDERSCORE_BOOL of (Cabs.loc)
  | TYPEDEF_NAME of (string * Pre_parser_aux.identifier_type ref * Cabs.loc)
  | TYPEDEF of (Cabs.loc)
  | TILDE of (Cabs.loc)
  | SWITCH of (Cabs.loc)
  | SUB_ASSIGN of (Cabs.loc)
  | STRUCT of (Cabs.loc)
  | STRING_LITERAL of (bool * int64 list * Cabs.loc)
  | STATIC_ASSERT of (Cabs.loc)
  | STATIC of (Cabs.loc)
  | STAR of (Cabs.loc)
  | SLASH of (Cabs.loc)
  | SIZEOF of (Cabs.loc)
  | SIGNED of (Cabs.loc)
  | SHORT of (Cabs.loc)
  | SEMICOLON of (Cabs.loc)
  | RPAREN of (Cabs.loc)
  | RIGHT_ASSIGN of (Cabs.loc)
  | RIGHT of (Cabs.loc)
  | RETURN of (Cabs.loc)
  | RESTRICT of (Cabs.loc)
  | REGISTER of (Cabs.loc)
  | RBRACK of (Cabs.loc)
  | RBRACE of (Cabs.loc)
  | QUESTION of (Cabs.loc)
  | PTR of (Cabs.loc)
  | PRE_NAME of (string)
  | PRAGMA of (string * Cabs.loc)
  | PLUS of (Cabs.loc)
  | PERCENT of (Cabs.loc)
  | PACKED of (Cabs.loc)
  | OR_ASSIGN of (Cabs.loc)
  | NORETURN of (Cabs.loc)
  | NEQ of (Cabs.loc)
  | MUL_ASSIGN of (Cabs.loc)
  | MOD_ASSIGN of (Cabs.loc)
  | MINUS of (Cabs.loc)
  | LT of (Cabs.loc)
  | LPAREN of (Cabs.loc)
  | LONG of (Cabs.loc)
  | LEQ of (Cabs.loc)
  | LEFT_ASSIGN of (Cabs.loc)
  | LEFT of (Cabs.loc)
  | LBRACK of (Cabs.loc)
  | LBRACE of (Cabs.loc)
  | INT of (Cabs.loc)
  | INLINE of (Cabs.loc)
  | INC of (Cabs.loc)
  | IF of (Cabs.loc)
  | HAT of (Cabs.loc)
  | GT of (Cabs.loc)
  | GOTO of (Cabs.loc)
  | GEQ of (Cabs.loc)
  | GENERIC of (Cabs.loc)
  | FOR of (Cabs.loc)
  | FLOAT of (Cabs.loc)
  | EXTERN of (Cabs.loc)
  | EQEQ of (Cabs.loc)
  | EQ of (Cabs.loc)
  | EOF
  | ENUM of (Cabs.loc)
  | ELSE of (Cabs.loc)
  | ELLIPSIS of (Cabs.loc)
  | DOUBLE of (Cabs.loc)
  | DOT of (Cabs.loc)
  | DO of (Cabs.loc)
  | DIV_ASSIGN of (Cabs.loc)
  | DEFAULT of (Cabs.loc)
  | DEC of (Cabs.loc)
  | CONTINUE of (Cabs.loc)
  | CONSTANT of (Cabs.constant * Cabs.loc)
  | CONST of (Cabs.loc)
  | COMMA of (Cabs.loc)
  | COLON of (Cabs.loc)
  | CHAR of (Cabs.loc)
  | CASE of (Cabs.loc)
  | BUILTIN_VA_ARG of (Cabs.loc)
  | BUILTIN_OFFSETOF of (Cabs.loc)
  | BREAK of (Cabs.loc)
  | BARBAR of (Cabs.loc)
  | BAR of (Cabs.loc)
  | BANG of (Cabs.loc)
  | AUTO of (Cabs.loc)
  | ATTRIBUTE of (Cabs.loc)
  | ASM of (Cabs.loc)
  | AND_ASSIGN of (Cabs.loc)
  | ANDAND of (Cabs.loc)
  | AND of (Cabs.loc)
  | ALIGNOF of (Cabs.loc)
  | ALIGNAS of (Cabs.loc)
  | ADD_ASSIGN of (Cabs.loc)

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val translation_unit_file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (unit)

module MenhirInterpreter : sig
  
  (* The incremental API. *)
  
  include MenhirLib.IncrementalEngine.INCREMENTAL_ENGINE
    with type token = token
  
end

(* The entry point(s) to the incremental API. *)

module Incremental : sig
  
  val translation_unit_file: Lexing.position -> (unit) MenhirInterpreter.checkpoint
  
end
