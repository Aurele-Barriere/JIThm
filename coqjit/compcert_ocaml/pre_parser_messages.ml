
(* This file was auto-generated based on "handcrafted.messages". *)

(* Please note that the function [message] can raise [Not_found]. *)

let message =
  fun s ->
    match s with
    | 29 | 247 | 48 | 458 | 205 | 193 ->
        "Internal error when printing a syntax error message. Please report.\n"
    | 385 ->
        "Ill-formed _Generic expression.\nUp to this point, one or several generic associations have been recognized,\nfollowed by a comma ',':\n  $0\nAt this point, another generic association is expected.\nIt should start either with a type name or with the 'default' keyword.\n"
    | 383 ->
        "Ill-formed _Generic expression.\nUp to this point, one or several generic associations have been recognized:\n  $0\nAt this point, either a closing parenthesis ')' or a comma ',' are expected.\nUse a closing parenthesis ')' to terminate the _Generic expression.\nUse a comma to add another generic association.\n"
    | 380 ->
        "Ill-formed _Generic expression.\nUp to this point, a type name followed by a colon have been recognized:\n  $0\nAt this point, an expression is expected.\n"
    | 379 ->
        "Ill-formed _Generic expression.\nUp to this point, a type name has been recognized:\n  $0\nAt this point, a colon ':' is expected.\n"
    | 377 ->
        "Ill-formed _Generic expression.\nAt this point, an expression is expected.\n"
    | 376 ->
        "Ill-formed _Generic expression.\nAt this point, a colon ':' is expected.\n"
    | 375 ->
        "Ill-formed _Generic expression.\nAt this point, either a type name or 'default' are expected.\n"
    | 374 ->
        "Ill-formed _Generic expression.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a comma ',' is expected.\n"
    | 36 ->
        "Ill-formed _Generic expression.\nAt this point, an expression is expected.\n"
    | 35 ->
        "Ill-formed _Generic expression.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 173 ->
        "Ill-formed _Static_assert.\nAt this point, a semicolon ';' is expected.\n"
    | 172 ->
        "Ill-formed _Static_assert.\nAt this point, a closing parenthesis ')' is expected.\n"
    | 171 ->
        "Ill-formed _Static_assert.\nAt this point, a string literal is expected.\n"
    | 170 ->
        "Ill-formed _Static_assert.\nAt this point, a comma ',' is expected.\n"
    | 169 ->
        "Ill-formed _Static_assert.\nAt this point, a constant expression is expected.\n"
    | 168 ->
        "Ill-formed _Static_assert.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 367 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a member-designator is expected.\n# ------------------------------------------------------------------------------\n"
    | 358 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a member-designator is expected.\n"
    | 357 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a member-designator is expected.\n"
    | 356 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a colon ',' is expected\n"
    | 42 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a struct or union name is expected.\n"
    | 41 ->
        "Ill-formed __builtin_offsetof.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 622 ->
        "Ill-formed K&R function definition.\nAt this point, one of the following is expected:\n  a declaration; or\n  an opening brace '{' (for the function body).\n"
    | 16 ->
        "Ill-formed declaration.\nThe following identifier is used as a type, but has not been defined as such:\n  $0\n"
    | 240 ->
        "Up to this point, a list of parameter declarations has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 241 ->
        "At this point, one of the following is expected:\n  a parameter declaration; or\n  an ellipsis '...'.\n"
    | 626 ->
        "Ill-formed declaration or function definition.\nUp to this point, a list of attribute specifiers has been recognized.\nIf this is a declaration,\n  then at this point, a semicolon ';' is expected.\nIf this is a function definition,\n  then at this point, an opening brace '{' is expected (for the function body).\nIf this is the parameter declaration of a K&R function definition,\n  then at this point, one of the following is expected:\n    a storage class specifier; or\n    a type qualifier; or\n    a type specifier.\n"
    | 613 ->
        "Ill-formed K&R parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 612 | 617 | 610 | 615 ->
        "Ill-formed K&R parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a list of declarators.\n"
    | 294 ->
        "Ill-formed K&R function definition.\nThe following type name is used as a K&R parameter name:\n  $0\n"
    | 293 ->
        "Ill-formed K&R function definition.\nAt this point, an identifier is expected.\n"
    | 254 ->
        "Up to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing bracket ']' is expected.\n"
    | 577 ->
        "Ill-formed init declarator.\nAt this point, an initializer is expected.\n"
    | 391 ->
        "Ill-formed initializer.\nAt this point, an optional designation,\nfollowed with an initializer, is expected.\n"
    | 392 ->
        "Ill-formed initializer.\nUp to this point, a list of initializers has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing brace '}' is expected.\n"
    | 393 ->
        "Ill-formed initializer list.\nAt this point, one of the following is expected:\n  an optional designation, followed with an initializer; or\n  a closing brace '}'.\n"
    | 361 ->
        "Ill-formed designator.\nAt this point, a constant expression is expected.\n"
    | 362 ->
        "Ill-formed designator.\nUp to this point, an opening bracket and an expression have been recognized:\n  $1 $0\nIf this expression is complete,\nthen at this point, a closing bracket ']' is expected.\n"
    | 364 ->
        "Ill-formed designator.\nAt this point, the name of a struct or union member is expected.\n"
    | 397 ->
        "Ill-formed designation.\nUp to this point, a list of designators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, an equals sign '=' is expected.\n"
    | 390 | 394 ->
        "Ill-formed initializer list.\nAt this point, an initializer is expected.\n"
    | 572 ->
        "Ill-formed declaration.\nAt this point, an init declarator is expected.\n"
    | 571 ->
        "Up to this point, a list of declarators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 135 ->
        "Ill-formed use of the sequencing operator ','.\nAt this point, an expression is expected.\n"
    | 594 ->
        "A type identifier has been recognized.\nAssuming this is the beginning of a declaration,\nat this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  an init declarator, followed with a semicolon ';'.\n"
    | 456 ->
        "Up to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 453 ->
        "Ill-formed 'return' statement.\nAt this point, one of the following is expected:\n  an expression; or\n  a semicolon ';'.\n"
    | 452 ->
        "At this point, one of the following is expected:\n  a declaration; or\n  a statement; or\n  a pragma; or\n  a closing brace '}'.\n"
    | 508 ->
        "Ill-formed 'while' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 509 ->
        "Ill-formed 'while' statement.\nAt this point, an expression is expected.\n"
    | 510 ->
        "Ill-formed 'while' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 511 ->
        "Ill-formed 'while' statement.\nAt this point, a statement (the loop body) is expected.\n"
    | 524 ->
        "Ill-formed 'switch' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 525 ->
        "Ill-formed 'switch' statement.\nAt this point, an expression is expected.\n"
    | 526 ->
        "Ill-formed 'switch' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 527 ->
        "Ill-formed 'switch' statement.\nAt this point, a statement is expected.\nIt usually takes the form of a series of labeled statements,\nenclosed within braces '{' and '}'.\n"
    | 529 ->
        "Ill-formed 'if' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 530 ->
        "Ill-formed 'if' statement.\nAt this point, an expression is expected.\n"
    | 531 ->
        "Ill-formed 'if' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 533 ->
        "Ill-formed 'if' statement.\nAt this point, a statement is expected.\n"
    | 585 ->
        "Ill-formed 'if' ... 'else' statement.\nAt this point, a statement is expected.\n"
    | 461 ->
        "Ill-formed 'goto' statement.\nAt this point, an identifier (a 'goto' label) is expected.\n"
    | 536 ->
        "Ill-formed 'for' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 537 ->
        "Ill-formed 'for' statement.\nAt this point, one of the following is expected:\n  an optional expression\n    (evaluated once at the beginning),\n  followed with a semicolon ';'; or\n  a declaration.\n"
    | 557 ->
        "Ill-formed 'for' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 550 ->
        "Ill-formed 'for' statement.\nAt this point, an optional expression\n  (evaluated before each execution of the loop body),\nfollowed with a semicolon ';', is expected.\n"
    | 551 ->
        "Ill-formed 'for' statement.\nAt this point, an optional expression\n  (evaluated after each execution of the loop body),\nfollowed with a closing parenthesis ')', is expected.\n"
    | 555 ->
        "Ill-formed 'for' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 553 ->
        "Ill-formed 'for' statement.\nAt this point, a statement (the loop body) is expected.\n"
    | 583 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, a statement (the loop body) is expected.\n"
    | 587 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, a 'while' keyword is expected.\n"
    | 588 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 589 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, an expression is expected.\n"
    | 590 ->
        "Ill-formed 'do' ... 'while' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' and a semicolon ';' are expected.\n"
    | 464 | 518 ->
        "Ill-formed labeled statement.\nAt this point, a colon ':' is expected.\n"
    | 468 ->
        "Ill-formed labeled statement.\nAt this point, a constant expression is expected.\n"
    | 469 ->
        "Ill-formed labeled statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a colon ':' is expected.\n"
    | 470 | 465 | 519 ->
        "Ill-formed labeled statement.\nAt this point, a statement is expected.\n"
    | 471 | 466 | 591 | 462 | 503 ->
        "Ill-formed statement.\nAt this point, a semicolon ';' is expected.\n"
    | 479 ->
        "Ill-formed assembly statement.\nAt this point, a string literal, representing an instruction, is expected.\n"
    | 480 ->
        "Ill-formed assembly statement.\nAt this point, one of the following is expected:\n  a string literal, representing one more instruction; or\n  a colon ':', followed with a list of outputs; or\n  a closing parenthesis ')'.\n"
    | 489 ->
        "Ill-formed assembly operand.\nAt this point, an opening parenthesis '(',\nfollowed with an expression and a closing parenthesis ')', is expected.\n"
    | 490 ->
        "Ill-formed assembly operand.\nAt this point, an expression is expected.\n"
    | 491 ->
        "Ill-formed assembly operand.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 486 ->
        "Ill-formed assembly statement.\nAt this point, an assembly operand is expected.\n"
    | 482 ->
        "Ill-formed assembly operand.\nAt this point, an identifier is expected.\n"
    | 483 ->
        "Ill-formed assembly operand.\nAt this point, a closing bracket ']' is expected.\n"
    | 488 ->
        "Ill-formed assembly operand.\nAt this point, a string literal, representing a constraint, is expected.\n"
    | 495 ->
        "Ill-formed assembly statement.\nUp to this point, a list of outputs and a list of inputs have been recognized:\n  $2\n  $0\nIf the latter list is complete,\nthen at this point, one of the following is expected:\n  a colon ':', followed with a list of clobbered resources; or\n  a closing parenthesis ')'.\n"
    | 493 ->
        "Ill-formed assembly statement.\nUp to this point, a list of outputs has been recognized:\n  $0\nIf this list is complete,\nthen at this point, one of the following is expected:\n  a colon ':', followed with a list of inputs; or\n  a closing parenthesis ')'.\n"
    | 498 ->
        "Ill-formed assembly statement.\nUp to this point, a list of clobbered resources has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 499 | 496 ->
        "Ill-formed assembly statement.\nAt this point, a clobbered resource is expected.\nExamples of clobbered resources:\n  \"memory\"\n  \"eax\"\n"
    | 475 | 474 | 473 ->
        "Ill-formed assembly statement.\nAt this point, one of the following is expected:\n  an assembly attribute, such as 'volatile'; or\n  an opening parenthesis '('.\n"
    | 260 ->
        "At this point, a list of parameter declarations,\nfollowed with a closing parenthesis ')', is expected.\n"
    | 561 ->
        "At this point, a declarator is expected.\n"
    | 560 ->
        "Up to this point, a list of declarators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 201 ->
        "Ill-formed declarator.\nAt this point, one of the following is expected:\n  a type qualifier; or\n  a star '*', possibly followed with type qualifiers; or\n  a direct declarator.\n"
    | 204 ->
        "Ill-formed function definition.\nAt this point, a list of parameter declarations,\nfollowed with a closing parenthesis ')', is expected.\n"
    | 292 ->
        "Ill-formed K&R function definition.\nUp to this point, a list of identifiers has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 198 ->
        "Ill-formed direct declarator.\nAt this point, a declarator is expected.\n"
    | 275 ->
        "Up to this point, a declarator has been recognized:\n  $0\nIf this declarator is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 164 ->
        "Ill-formed struct or union specifier.\nAt this point, one of the following is expected:\n  an attribute specifier; or\n  an identifier; or\n  an opening brace '{', followed with a list of members.\n"
    | 167 ->
        "At this point, one of the following is expected:\n  a struct declaration; or\n  a closing brace '}'.\n"
    | 185 ->
        "Ill-formed struct declaration.\nAt this point, one of the following is expected:\n  a type qualifier; or\n  a type specifier.\n"
    | 304 ->
        "Ill-formed struct declaration.\nUp to this point, a declarator has been recognized:\n  $0\nIf this declarator is complete,\nthen at this point, one of the following is expected:\n  a colon ':', followed with a constant expression; or\n  a comma ',', followed with a struct declarator; or\n  a semicolon ';'.\n"
    | 299 ->
        "Ill-formed struct declaration.\nAt this point, a struct declarator is expected.\n"
    | 302 ->
        "Ill-formed struct declarator.\nAt this point, a constant expression is expected.\n"
    | 298 ->
        "Ill-formed struct declaration.\nUp to this point, a list of struct declarators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 192 ->
        "Ill-formed struct declaration.\nUp to this point,\na list of type qualifiers and type specifiers has been recognized:\n  $0\nIf this list is complete, then \nat this point, one of the following is expected:\n  a struct declarator; or\n  a semicolon ';'.\n"
    | 540 | 546 | 542 | 548 ->
        "Ill-formed declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  an init declarator.\n"
    | 544 ->
        "Ill-formed declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 434 ->
        "Ill-formed declaration or function definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 212 | 235 | 218 | 237 ->
        "Ill-formed parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a declarator; or\n  an abstract declarator; or\n  a comma ',', followed with a parameter declaration; or\n  a closing parenthesis ')'.\n"
    | 425 | 442 | 429 | 446 ->
        "Ill-formed declaration or function definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  an init declarator,\n    if this is a declaration; or\n  a declarator,\n    followed with a function body,\n    if this is a function definition.\n"
    | 233 ->
        "Ill-formed parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 9 | 436 ->
        "Ill-formed type definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 418 | 427 | 438 | 444 | 420 | 431 | 440 | 448 ->
        "Ill-formed type definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a list of declarators, followed with a semicolon ';'.\n"
    | 2 ->
        "At this point, one of the following is expected:\n  a function definition; or\n  a declaration; or\n  a pragma; or\n  the end of the file.\n"
    | 18 ->
        "Ill-formed $0 attribute.\nAt this point, an opening parenthesis '(',\nfollowed with a possibly empty list of expressions,\nis expected.\n"
    | 24 ->
        "Ill-formed expression.\nThe following identifier is used as a variable, but has been defined as a type:\n  $0\n"
    | 19 ->
        "Ill-formed $1 attribute.\nAt this point, a list of expressions is expected.\n"
    | 415 ->
        "Ill-formed $2 attribute.\nUp to this point, a list of expressions has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 134 ->
        "Ill-formed conditional expression.\nUp to this point, an expression, '?', and an expression have been recognized:\n  $2\n  $1\n  $0\nIf the last expression is complete,\nthen at this point, a colon ':' is expected.\n"
    | 138 | 116 ->
        "Ill-formed conditional expression.\nAt this point, an expression is expected.\n"
    | 76 ->
        "Ill-formed expression.\nAt this point, a list of expressions,\nfollowed with a closing parenthesis ')', is expected.\n"
    | 147 ->
        "Up to this point, a list of expressions has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 150 ->
        "Ill-formed expression.\nAt this point, an expression is expected.\n"
    | 151 ->
        "Ill-formed expression.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing bracket ']' is expected.\n"
    | 154 | 74 ->
        "Ill-formed use of the dereferencing operator $0.\nAt this point, the name of a struct or union member is expected.\n"
    | 148 ->
        "Ill-formed list of expressions.\nAt this point, an expression is expected.\n"
    | 89 ->
        "Ill-formed use of the assignment operator $0.\nAt this point, an expression is expected.\n"
    | 129 | 118 | 120 | 141 | 122 | 112 | 126 | 105 | 93 | 98 ->
        "Ill-formed use of the binary operator $0.\nAt this point, an expression is expected.\n"
    | 68 ->
        "Ill-formed use of the unary operator $0.\nAt this point, an expression is expected.\n"
    | 30 ->
        "Ill-formed expression.\nAn opening parenthesis '(' has just been recognized.\nAt this point, one of the following is expected:\n  a type name,   if this is a type cast or a compound literal; or\n  an expression, if this is a parenthesized expression.\n"
    | 410 ->
        "Ill-formed expression.\nUp to this point, a type name in parentheses has been recognized:\n  $2 $1 $0\nAt this point, one of the following is expected:\n  an expression,        if this is a type cast; or\n  an opening brace '{', if this is a compound literal.\n"
    | 389 ->
        "Ill-formed compound literal.\nAt this point, an initializer is expected.\n"
    | 403 ->
        "Ill-formed compound literal.\nUp to this point, a list of initializers has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing brace '}' is expected.\n"
    | 406 ->
        "Ill-formed expression.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 34 ->
        "Ill-formed expression.\nAt this point, one of the following is expected:\n  a type name (if this is the beginning of a compound literal); or\n  an expression.\n"
    | 388 ->
        "Ill-formed expression.\nUp to this point, a type name in parentheses has been recognized:\n  $2 $1 $0\nIf this is the beginning of a compound literal,\n  then at this point, an opening brace '{' is expected.\nIf this is intended to be the beginning of a cast expression,\n  then perhaps an opening parenthesis '(' was forgotten earlier.\n"
    | 37 | 33 ->
        "Ill-formed expression.\nAt this point, an expression is expected.\n"
    | 39 ->
        "Ill-formed use of $0.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 40 ->
        "Ill-formed use of $1.\nAt this point, an expression is expected.\n"
    | 370 ->
        "Ill-formed use of $3.\nAt this point, a type name is expected.\n"
    | 369 ->
        "Ill-formed use of $2.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a comma ',' is expected.\n"
    | 23 ->
        "Ill-formed use of $0.\nAt this point, an opening parenthesis '(' is expected,\nfollowed with an expression or a type name.\n"
    | 58 ->
        "Ill-formed use of $0.\nAt this point, an opening parenthesis '(' is expected,\nfollowed with a type name.\n"
    | 59 | 28 ->
        "Ill-formed use of $1.\nAt this point, an expression is expected.\n"
    | 341 ->
        "Ill-formed enumeration specifier.\nAt this point, one of the following is expected:\n  an attribute specifier; or\n  an identifier; or\n  an opening brace '{'.\n"
    | 343 ->
        "Ill-formed enumeration specifier.\nAt this point, an enumerator is expected.\n"
    | 348 ->
        "Ill-formed enumeration specifier.\nAt this point, one of the following is expected:\n  an equals sign '=', followed with a constant expression; or\n  a comma ',', followed with an enumerator; or\n  a closing brace '}'.\n"
    | 349 ->
        "Ill-formed enumeration specifier.\nAt this point, a constant expression is expected.\n"
    | 345 ->
        "Ill-formed enumeration specifier.\nUp to this point, a list of enumerators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing brace '}' is expected.\n"
    | 346 ->
        "Ill-formed enumeration specifier.\nAt this point, an enumerator is expected.\n"
    | 45 ->
        "Ill-formed gcc attribute specifier.\nAt this point, two opening parentheses '((' are expected.\n"
    | 46 ->
        "Ill-formed gcc attribute specifier.\nAt this point, a second opening parenthesis '(' is expected.\n"
    | 47 ->
        "Ill-formed gcc attribute specifier.\nAt this point, a gcc attribute is expected.\n"
    | 54 ->
        "Ill-formed gcc attribute specifier.\nUp to this point, an attribute has been recognized:\n  $0\nAt this point, one of the following is expected:\n  an opening parenthesis '(',\n    followed with a list of parameters for this attribute; or\n  a comma ',',\n    followed with another attribute; or\n  a closing parenthesis ')'.\n"
    | 55 ->
        "Ill-formed gcc attribute.\nAt this point, a list of expressions is expected.\n"
    | 329 ->
        "Ill-formed gcc attribute.\nAt this point, a comma ',' is expected.\n"
    | 330 ->
        "Ill-formed gcc attribute.\nAt this point, an expression is expected.\n"
    | 331 ->
        "Ill-formed gcc attribute.\nUp to this point, a list of expressions has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 335 ->
        "Ill-formed attribute specifier.\nAt this point, one of the following is expected:\n  a comma ',', followed with a gcc attribute; or\n  two closing parentheses '))'.\n"
    | 336 ->
        "Ill-formed attribute specifier.\nAt this point, a second closing parenthesis ')' is expected.\n"
    | 338 ->
        "Ill-formed attribute specifier.\nAt this point, a gcc attribute is expected.\n"
    | 66 ->
        "Ill-formed _Alignas qualifier.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 67 ->
        "Ill-formed _Alignas qualifier.\nAt this point, one of the following is expected:\n  an expression; or\n  a type name.\n"
    | 310 ->
        "Ill-formed type name.\nAt this point, one of the following is expected:\n  a type qualifier; or\n  a type specifier.\n"
    | 245 ->
        "An opening parenthesis '(' has been recognized.\nAt this point, one of the following is expected:\n  an abstract declarator or a declarator,\n    if this parenthesis is a delimiter; or\n  a list of parameter declarations,\n    if this parenthesis is the beginning of a function declarator.\n"
    | 318 ->
        "An opening parenthesis '(' has been recognized.\nAt this point, one of the following is expected:\n  an abstract declarator,\n    if this parenthesis is a delimiter; or\n  a list of parameter declarations,\n    if this parenthesis is the beginning of a function declarator.\n"
    | 277 ->
        "Up to this point, an abstract declarator has been recognized:\n  $0\nAt this point, a closing parenthesis ')' is expected.\n"
    | 279 | 262 | 296 ->
        "At this point, a closing parenthesis ')' is expected.\n"
    | 251 | 268 ->
        "Ill-formed array declarator.\nAt this point, one of the following is expected:\n  an expression, followed with a closing bracket ']'; or\n  a closing bracket ']'.\n"
    | 325 ->
        "Ill-formed _Alignas qualifier.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 409 ->
        "Up to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 387 ->
        "Ill-formed compound literal.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 371 ->
        "Ill-formed use of __builtin_va_arg.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 327 | 412 ->
        "Ill-formed use of $2.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 315 ->
        "Ill-formed _Alignas qualifier.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | _ ->
        raise Not_found
