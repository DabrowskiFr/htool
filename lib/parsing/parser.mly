%{
    open HoareSyntax.Syntax 
%}

%token <Z.t> INT 
%token <string> ID 
%token EOF
%token LPAREN RPAREN LBRACE RBRACE LSQBRACE RSQBRACE
%token EQ NEQ LT GT LE GE
%token NOT
%token ASSIGN 
%token SEMICOLON COMMA
%token PLUS MINUS
%token MULT DIV
%token OR
%token AND 
%token IMP
%token TRUE FALSE FORALL EXISTS
%token DOT
%token SKIP IF THEN ELSE END WHILE DO DONE
%token INVARIANT VARIANT ASSERT

%left AND OR IMP
%left LT GT LE GE EQ NEQ
%left PLUS MINUS 
%left MULT DIV
%left SEMICOLON
%left DOT

%nonassoc UNARY
%nonassoc RPAREN
%nonassoc ELSE

%start <HoareSyntax.Syntax.program> program

%% 

let program :=
    | LBRACE; f1=formula;RBRACE; s = stmt; LBRACE; f2=formula;RBRACE; {(f1, s, f2)}

let stmt :=
    | SKIP; {Skip}
    | id=ID; ASSIGN; e=aexpr; {Assign(id,e)}
    | id=ID; LSQBRACE; e1=aexpr;RSQBRACE;ASSIGN;e2=aexpr; {AssignArray(id,e1,e2)}
    //| s1=stmt;SEMICOLON;s2=stmt; {Seq (s1,(None,s2))}
    | s1=stmt;SEMICOLON; f=option(assertion);s2=stmt; {Seq (s1,(f,s2))}
    //| s1=stmt;SEMICOLON; LBRACE;f=formula;RBRACE;s2=stmt; {Seq(s1,(Some f, s2))}
    | IF;b=bexpr;THEN;s1=stmt;ELSE;s2=stmt;END; {Ite(b,s1,s2)}
    | WHILE;b=bexpr;DO; INVARIANT;LBRACE;f=formula; RBRACE;VARIANT;LPAREN;e=aexpr; RPAREN;s=stmt;DONE;
        {While (b, f, e,s)}

let assertion := 
    | LBRACE;f=formula;RBRACE; {f}

let aexpr :=
    | MINUS; e=aexpr; %prec UNARY {Neg(e)}
    | n=INT; {Cst(n)}
    | id=ID; {Var(id)}
    | id=ID;LSQBRACE;e=aexpr; RSQBRACE; {Array(id,e)}
    | e1 = aexpr; PLUS;e2=aexpr; {Binop(Plus,e1,e2)}
    | e1 = aexpr; MINUS;e2=aexpr; {Binop(Minus,e1,e2)}
    | e1 = aexpr; MULT;e2=aexpr; {Binop(Mult,e1,e2)}
   
let laexpr := 
    | MINUS; e=laexpr; %prec UNARY {LANeg(e)}
    | n=INT; {LACst(n)}
    | id=ID; {LAVar(id)}
    | id=ID;LSQBRACE;e=laexpr; RSQBRACE; {LAArray(id,[],e)}
    | e1 = laexpr; PLUS;e2=laexpr; {LABinop(Plus,e1,e2)}
    | e1 = laexpr; MINUS;e2=laexpr; {LABinop(Minus,e1,e2)}
    | e1 = laexpr; MULT;e2=laexpr; {LABinop(Mult,e1,e2)}
    | id=ID;LPAREN;l=separated_list(COMMA,laexpr);RPAREN; {LAFunction(id,l)}

let rel :=
    | EQ;{Eq}
    | NEQ;{NEq}
    | LT; {Lt}
    | GT; {Gt}
    | LE;{Le}
    | GE;{Ge}

let bexpr := 
    | NOT; b=bexpr;{Not(b)}
    | e1=aexpr;r=rel;e2=aexpr;{Rel(r,e1,e2)}

let lbexpr := 
    | NOT; b=lbexpr;{LBNot(b)}
    | e1=laexpr;r=rel;e2=laexpr;{LBRel(r,e1,e2)}
    | id=ID;LPAREN;l=separated_list(COMMA,laexpr);RPAREN; {LBPredicate(id,l)}

let formula :=
    | TRUE; {True}
    | FALSE; {False}
    | e=lbexpr; {LBExpr (e)}
    | f1 = formula; AND; f2=formula; {And(f1,f2)}
    | f1 = formula; OR; f2=formula; {Or(f1,f2)}
    | f1 = formula; IMP; f2=formula; {Impl(f1,f2)}
    | FORALL;l=list(ID);DOT;f=formula; {Forall(l,f)}
    | EXISTS;l=list(ID);DOT;f=formula; {Exists(l,f)}