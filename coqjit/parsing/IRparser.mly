%token LBRACK RBRACK
%token LPAR RPAR
%token LBRACE RBRACE
%token EOF
%token COLON DOT COMMA
%token ENDVER ENDFUNC ENDPROG
%token FUNCTION VERSION
%token PARAMS
%token ENTRY MAIN
%token <IRast.areg> REG
%token <IRast.alabel> LBL
%token <IRast.afun_id> FID
%token <IRast.acst> CSTI
%token LL RR
%token PLUS MINUS MULT LT EQ MOD
%token UMINUS UMULT UPLUS EQZERO
%token NOP CALL IRETURN COND PRINT ASSUME MEMGET MEMSET
%token ARROW
%start <IRast.aprogram option> prog
%%

reg:
  | r=REG {r}

binop:
  | PLUS {IRast.Abplus}
  | MINUS {IRast.Abneg}
  | MULT {IRast.Abmul}
  | LT {IRast.Ablt}
  | EQ {IRast.Abeq}
  | MOD {IRast.Abmod}

unop:
  | UMINUS {IRast.Auneg}
  | EQZERO {IRast.Aueqzero}
  | UPLUS c=CSTI {IRast.Auplus c}
  | UMULT c=CSTI {IRast.Aumul c}

expr:
  | b=binop o1=reg o2=reg
    {IRast.ABIN (b,o1,o2)}
  | u=unop o=reg
    {IRast.AUNA (u,o)}
  | o=reg
    {IRast.AUNA (IRast.Auplus 0,o)}
  | c=CSTI
    {IRast.AZAR c}
  | LPAR e=expr RPAR
    {e}

list_reg:
  | {[]}
  | r=reg {[r]}
  | r=reg COMMA lr=list_reg {r::lr}

regexpr:
  | LPAR r=REG COMMA e=expr RPAR {(r,e)}

varmap:
  | {[]}
  | re=regexpr vm=varmap {re::vm}

target:
  | f=FID DOT l=LBL
    { (f,l) }

instruction:
  | NOP l=LBL
    {IRast.Anop (l)}
  | r=REG ARROW e=expr l=LBL
    {IRast.Aop (r,e,l)}
  | r=REG ARROW CALL f=FID LPAR le=list_reg RPAR l=LBL
    {IRast.Acall (f,le,r,l)}
  | IRETURN e=reg
    {IRast.Areturn e}
  | COND e=reg l1=LBL l2=LBL
    {IRast.Acond (e,l1,l2)}
  | MEMSET LBRACK r1=reg RBRACK ARROW r2=reg l=LBL
    {IRast.Amemset (r1,r2,l)}
  | r1=REG ARROW MEMGET LBRACK r2=reg RBRACK l=LBL
    {IRast.Amemget (r1,r2,l)}
  | PRINT e=reg l=LBL
    {IRast.Aprint (e,l)}
  | ASSUME LPAR guard=reg RPAR t=target LBRACE vm=varmap RBRACE next=LBL
    {IRast.Aassume (guard,t,vm,next)}

node:
  | LL l=LBL RR i=instruction
    {(l,i)}

list_node:
  | ENDVER {[]}
  | n=node ln=list_node {n::ln}

version_decl:
  | VERSION COLON LBRACK ENTRY COLON l=LBL RBRACK n=list_node
    {(l,n)}

fun_decl:
  | FUNCTION f=FID COLON PARAMS COLON LPAR rl=list_reg RPAR v=version_decl ENDFUNC
    {(f,rl,v,None)}
  | FUNCTION f=FID COLON PARAMS COLON LPAR rl=list_reg RPAR v=version_decl vopt=version_decl ENDFUNC
    {(f,rl,v,Some vopt)}

list_fun:
  | ENDPROG {[]}
  | f=fun_decl lf=list_fun {f::lf}

prog:
  | LBRACK MAIN COLON f=FID RBRACK fl=list_fun {Some (f,fl)}
  | EOF {None}


%%
