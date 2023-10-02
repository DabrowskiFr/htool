type var = string 

type binop = Plus | Minus | Mult 

type rel = Eq | NEq | Lt | Le | Gt | Ge

type log = BAnd | BOr

type aexpr =
  | Cst of Z.t
  | Var of var 
  | Array of var * aexpr
  | Neg of aexpr 
  | Binop of binop * aexpr * aexpr 

type bexpr = 
  | Rel of rel * aexpr * aexpr 
  | Not of bexpr 
  | Log of log * bexpr * bexpr 

(* Logical expressions extend expressions with array update and functions *)
(* Logical boolean expression extend boolean expressions with predicates *)
(* =,<>, < ,... are predicates *)
type laexpr = 
  | LACst of Z.t
  | LAVar of var 
  | LAArray of var * (laexpr * laexpr) list * laexpr 
  | LANeg of laexpr 
  | LABinop of binop * laexpr * laexpr 
  | LAFunction of string * laexpr list

type lbexpr = 
  | LBRel of rel * laexpr * laexpr 
  | LBNot of lbexpr 
  | LBLog of log * lbexpr * lbexpr 
  | LBPredicate of string * laexpr list 

let rec laexpr_of_aexpr (e : aexpr) = 
    match e with 
      | Cst n -> LACst n
      | Var x -> LAVar x 
      | Array (x, e) -> LAArray (x, [],laexpr_of_aexpr e) 
      | Neg e -> LANeg (laexpr_of_aexpr e)
      | Binop (o, e1, e2) -> LABinop (o, laexpr_of_aexpr e1, laexpr_of_aexpr e2)

let rec lbexpr_of_bexpr (b : bexpr) : lbexpr = (* lbexpr are predicates ? *)
  match b with 
  | Rel (r,a1,a2) -> LBRel (r, laexpr_of_aexpr a1, laexpr_of_aexpr a2)
  | Not (b) -> LBNot (lbexpr_of_bexpr b) (* remove *)
  | Log (l, b1, b2) -> LBLog (l, lbexpr_of_bexpr b1, lbexpr_of_bexpr b2) (* remove *)

(* predicate_of_bexpr *)

(* predicates = p(...), e R e / predicates over extendes expressions *)
(* predicate = Rel | Abstract *)

type formula = 
  | True 
  | False 
  | LVar of var
  | LBExpr of lbexpr (* predicate *)
  | Not of formula
  | And of formula * formula
  | Or of formula * formula 
  | Impl of formula * formula
  | Forall of var list * formula 
  | Exists of var list * formula

type stmt = 
  | Skip 
  | Assign of var * aexpr
  | AssignArray of var * aexpr * aexpr 
  | Seq of stmt * (formula option * stmt) 
  | Ite of bexpr * stmt * stmt 
  | While of bexpr * formula * aexpr * stmt 

type program = formula * stmt * formula

(* Substitutions *)

let rec subst_aexpr (e1 : laexpr) (x : var) (e2 : laexpr) : laexpr = 
  match e1 with 
    | LACst n -> LACst n
    | LAVar y when x = y -> e2 
    | LAVar _ -> e1
    | LAArray (y, l, e) -> 
        LAArray (y, List.map (fun (a,b) -> (subst_aexpr a x e2, subst_aexpr b x e2)) l, 
        subst_aexpr e x e2)
    | LANeg e -> LANeg (subst_aexpr e x e2)
    | LABinop (o, e3, e4) -> LABinop (o, subst_aexpr e3 x e2, subst_aexpr e4 x e2)
    | LAFunction (f, l) -> LAFunction (f, List.map (fun e -> subst_aexpr e x e2) l)

let rec subst_bexpr (b1 : lbexpr) (x : var) (e2 : laexpr) : lbexpr = 
  match b1 with 
    | LBRel (r, e3, e4) -> LBRel (r, subst_aexpr e3 x e2, subst_aexpr e4 x e2)
    | LBNot b -> LBNot (subst_bexpr b x e2)
    | LBLog (l, b1, b2) -> LBLog (l, subst_bexpr b1 x e2, subst_bexpr b2 x e2)
    | LBPredicate (p, l) -> LBPredicate (p, List.map (fun e -> subst_aexpr e x e2) l)

let rec subst_array_aexpr (e1 : laexpr) (x : var) (idx : laexpr) (v : laexpr) : laexpr =
  match e1 with 
    | LACst n -> LACst n
    | LAVar _ -> e1
    | LAArray (y,l,e) -> LAArray (y, 
        (idx,v)::(List.map (fun (a,b) -> (subst_array_aexpr a x idx v, subst_array_aexpr b x idx v)) ) l, 
        subst_array_aexpr e x idx v)
    | LANeg e -> LANeg (subst_array_aexpr e x idx v)
    | LABinop (o, e3, e4) -> LABinop (o, subst_array_aexpr e3 x idx v, subst_array_aexpr e4 x idx v) 
    | LAFunction (f, l) -> LAFunction (f, List.map (fun e -> subst_array_aexpr e x idx v) l)

let rec subst_array_bexpr (b1 : lbexpr) (x : var) (idx : laexpr) (v : laexpr) : lbexpr =
  match b1 with 
    | LBRel (r, e3, e4) -> LBRel (r, subst_array_aexpr e3 x idx v, subst_array_aexpr e4 x idx v)
    | LBNot b -> LBNot (subst_array_bexpr b x idx v)
    | LBLog (l, b1, b2) -> LBLog (l, subst_array_bexpr b1 x idx v, subst_array_bexpr b2 x idx v)
    | LBPredicate (p, l) -> LBPredicate (p, List.map (fun e -> subst_array_aexpr e x idx v) l)

let rec subst (f : formula) (x : var) (e : laexpr) = 
  match f with 
    | True | False | LVar _ -> f 
    | LBExpr b -> LBExpr (subst_bexpr b x e) 
    | Not f -> Not (subst f x e)
    | And (f1, f2) -> And (subst f1 x e, subst f2 x e)
    | Or (f1, f2) -> Or (subst f1 x e, subst f2 x e)
    | Impl (f1, f2) -> Impl (subst f1 x e, subst f2 x e) 
    | Forall (y, f) -> Forall (y, subst f x e)
    | Exists (y, f) -> Exists (y, subst f x e) 

let rec subst_array (f : formula) (x : var) (idx : laexpr) (v : laexpr) : formula = 
  match f with 
    | True | False | LVar _ -> f 
    | LBExpr b -> LBExpr (subst_array_bexpr b x idx v) 
    | Not f -> Not (subst_array f x idx v)
    | And (f1, f2) -> And (subst_array f1 x idx v, subst_array f2 x idx v )
    | Or (f1, f2) -> Or (subst_array f1 x idx v, subst_array f2 x idx v )
    | Impl (f1, f2) -> Impl (subst_array f1 x idx v, subst_array f2 x idx v )
    | Forall (y, f) -> Forall (y, subst_array f x idx v)
    | Exists (y, f) -> Exists (y, subst_array f x idx v)
    
(* Printing *)

let string_of_binop (o : binop) : string = 
  match o with Plus -> "+" | Minus -> "-" | Mult -> "*"

let string_of_rel (r : rel) : string = 
  match r with 
    | Eq -> "=" | NEq -> "<>"
    | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="

let string_of_log (l : log) : string = 
  match l with BAnd -> " && " | BOr -> " || "

let rec string_of_laexpr (e : laexpr) : string = 
  match e with 
    | LACst n -> Z.to_string  n
    | LAVar x -> x 
    | LAArray (y, [], e) -> 
      y ^ "["^(string_of_laexpr e) ^"]"
    | LAArray (y, l, e) -> 
      y ^(string_of_mapping l)^
      "["^(string_of_laexpr e) ^"]"
    | LANeg e -> "-"^(string_of_laexpr e)
    | LABinop (o, e1, e2) -> (string_of_laexpr e1)^(string_of_binop o)^(string_of_laexpr e2)
    | LAFunction (f, l) -> f^"("^(String.concat "," (List.map string_of_laexpr l))^")"
and string_of_mapping l = 
      String.concat ""
      (List.map (fun (a,b) -> "{"^((string_of_laexpr a)^"->"^(string_of_laexpr b))^"}") l)

let rec string_of_lbexpr (b : lbexpr) : string =
  match b with 
    | LBRel (r, e1, e2) -> (string_of_laexpr e1)^(string_of_rel r)^(string_of_laexpr e2) 
    | LBNot (b) -> "~"^(string_of_lbexpr b) 
    | LBLog (l, b1,b2) -> (string_of_lbexpr b1)^(string_of_log l)^(string_of_lbexpr b2)
    | LBPredicate (p, l) -> p^"("^(String.concat "," (List.map string_of_laexpr l))^")"

let rec string_of_formula (f : formula) : string = 
  match f with 
    | True -> "true" | False -> "false" | LVar x -> x
    | LBExpr b -> string_of_lbexpr b
    | Not f -> "(~"^(string_of_formula f)^")"
    | And (f1, f2) -> (string_of_formula f1)^" /\\ "^(string_of_formula f2)
    | Or (f1, f2) -> (string_of_formula f1)^" \\/ "^(string_of_formula f2)
    | Impl (f1, f2) -> "("^(string_of_formula f1)^") -> ("^(string_of_formula f2)^")"
    | Forall (y,f) -> "(forall "^(String.concat " " y)^"."^(string_of_formula f)^")"
    | Exists (y,f) -> "(exists "^(String.concat " " y)^"."^(string_of_formula f)^")"

(* update variables *)
let rec updates (s : stmt) : var list = 
  match s with 
    | Skip -> [] 
    | Assign (x, _) -> [x]
    | AssignArray (x, _, _) -> [x]
    | Seq (s1, (_,s2)) -> (updates s1)@(updates s2)
    | Ite (_, s1, s2) -> (updates s1)@(updates s2)
    | While (_, _, _, s) -> updates s 

let generalize (l : string list) (f : formula) : formula = 
  match l with 
    | [] -> f 
    | _ -> Forall (l, f)

let rec wp (partial : bool) (s : stmt) (p : formula) : formula = 
  match s with 
    | Skip -> p
    | Assign (x, e) -> subst p x (laexpr_of_aexpr e)
    | AssignArray (x, e1, e2) -> subst_array p x (laexpr_of_aexpr e1) (laexpr_of_aexpr e2) 
    | Seq (s1, (_, s2)) -> wp partial s1 (wp partial s2 p)
    | Ite (b, s1, s2) -> 
        And (Impl (LBExpr (lbexpr_of_bexpr b), wp partial s1 p),
            Impl (Not (LBExpr (lbexpr_of_bexpr b)), wp partial s2 p))
    | While (b, f, _, s) -> 
      let c = LBExpr (lbexpr_of_bexpr b) in
      And (f, 
        generalize (updates s)
          (And (
            Impl (And (f, c), wp partial s f),  
            Impl (And (f, Not c), p))))

let rec vcgen ( partial : bool ) (p : formula) (s : stmt) (q : formula) : formula list = 
  match s with 
    | Skip -> []
    | Assign (x,e) -> [Impl (p, subst q x (laexpr_of_aexpr e))]
    | AssignArray (x,e1,e2) -> [Impl (p,subst_array q x (laexpr_of_aexpr e1) (laexpr_of_aexpr e2))]
    | Seq (s1, (_, Assign (x,e))) -> 
        vcgen partial p s1 (subst q x ((laexpr_of_aexpr e)))
    | Seq (s1, (_,AssignArray (x,e1,e2))) -> 
          vcgen partial p s1 (subst_array q x (laexpr_of_aexpr e1) (laexpr_of_aexpr e2))      
    | Seq (s1, (Some r, s2)) -> 
        vcgen partial p s1 r @ vcgen partial r s2 q
    | Seq (s1, (None, s2)) ->
        let r = wp partial s2 q in 
        vcgen partial p s1 r @ vcgen partial r s2 q 
    | Ite (b, s1,s2) -> 
        vcgen partial (And (p,LBExpr(lbexpr_of_bexpr b))) s1 q
        @ vcgen partial (And (p,Not (LBExpr(lbexpr_of_bexpr b)))) s2 q
    | While (b, f,_, s) ->
        [ 
          Impl (p,f); 
          Impl (
            And (f,
              Not (LBExpr (lbexpr_of_bexpr b))),q )]@
              vcgen partial ( And (f, LBExpr (lbexpr_of_bexpr b))) s f

let wpgen (partial : bool) (p : formula) (s : stmt) (q : formula) : formula = 
  Impl (p, wp partial s q)
