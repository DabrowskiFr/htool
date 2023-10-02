open HoareSyntax.Syntax
open HoareParser.Lexer
open HoareParser.Parser

let usage_msg ="htool -a [vcgen|vcgenwp|wp] <file>"

let algo = ref "vc" (* vc / hybrid / wp *)
let input = ref None 
let partial = ref false

let speclist = 
  [
    ("-a", Arg.Set_string algo, "Set Algorithm");
    ("-c", Arg.Set partial, "Set Correctness")
  ]

let anon_fun filename = input := Some filename

let () = 
  Arg.parse speclist anon_fun usage_msg;
  match !input with 
    | None -> print_string "no input file"
    | Some filename -> 
      let f = open_in filename in 
      print_string (">>"^filename);
      let lexbuf = Lexing.from_channel f in
      let (p,s,q) = program read_token lexbuf in
      print_string "\n";
      print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))))

(* git *)
(* add variant / total version *)
(* add arrays *)
(* add wp vcgenwp *)
(* variant optional in annotated code *)
(* proof cuhecker *)
(* print program *)
(* wp / wlp -> total *)
(* -> formula && => AND, || => OR *)


(*
let () = print_endline "Hello, World!"


let _ = 
  let s = Assign ("x", Binop (Plus, Var "x", Cst (Z.of_int 1))) in
  let q = LBExpr (LBRel (Eq, LAVar "x", LACst (Z. of_int 1))) in 
   print_endline (string_of_formula (wp true s q))

let _ = 
  let s = Assign ("x", Binop (Plus, Var "x", Cst (Z.of_int 1))) in
  let s = Seq (s, (None,s)) in 
  let q = LBExpr (LBRel (Eq, LAVar "x", LACst (Z.of_int 1))) in 
    print_endline (string_of_formula (wp true s q))
  
let _ = 
  let s = Ite (Rel (Ge, Var "x", Cst (Z.of_int 0)), Assign ("y", Var "x"), Assign ("y", Neg (Var "x"))) in
  let q = LBExpr (LBRel (Eq, LAVar "y", LAFunction ("abs", [LAVar "x"]))) in 
  print_endline (string_of_formula (wp true s q))

let _ = 
  let s = 
    While (
      Rel (Gt, Var "x", Cst (Z.of_int 0)), 
      And (
        LBExpr (LBRel (Eq, LABinop (Plus, LAVar "x", LAVar "y"), LAVar "a")), 
        LBExpr (LBRel (Ge, LAVar "x", LACst (Z.of_int 0)))
      ),
      Var "x",
      Seq (
        Assign ("x", Binop (Minus, Var "x", Cst (Z.of_int 1))), 
        (None, Assign ("y", Binop (Plus, Var "y", Cst (Z.of_int 1))))
        )
    ) in 
    let p = 
      And (LBExpr (LBRel (Eq, LAVar "x", LAVar "a")), 
        And (LBExpr (LBRel (Ge, LAVar "a", LACst (Z.of_int 0))), 
        LBExpr (LBRel (Eq, LAVar "y",LACst (Z.of_int 0))))) in 
    let q = LBExpr (LBRel (Eq, LAVar "y", LAVar "a")) in
    print_endline (string_of_formula (wp true s q));
    print_string "---\n";
    print_endline (String.concat "\n" (List.map string_of_formula (vcgen true p s q)));
    print_string "---\n";
    print_endline (string_of_formula (wpgen true p s q))

let _ = 
  let s = Assign ("x", Binop (Plus,Var "x", Cst (Z.of_int 1))) in 
  let p = LBExpr (LBRel (Eq, LAVar "x", LACst (Z.of_int 0))) in 
  let q = LBExpr (LBRel (Eq, LAVar "x", LACst (Z.of_int 1))) in
  print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))))

let _ = 
  let s = 
    Ite (
      Rel (Ge, Var "x", Var "y"), 
      Assign ("m", Var "x"), Assign ("m", Var "y")) in 
  let p = True in 
  let q = LBExpr (LBRel (Eq, LAVar "m", LAFunction ("max", [LAVar "x"; LAVar "y"]))) in 
  print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))))

  let _ =
    let s = 
      Seq (Assign ("x", Cst (Z.of_int 0)),
        (Some (LBExpr (LBRel (Eq, LAVar "x", LACst (Z.of_int 0)))), Assign ("x", Binop (Plus, Var "x", Cst (Z.of_int 1))))) in 
    let p = True in 
    let q = LBExpr (LBRel (Eq, LAVar "x", LACst (Z.of_int 1))) in 
    print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))))

    let _ = 
      let s = 
        Seq (Assign ("z", Cst (Z.of_int 0)), 
          ( Some (LBExpr(LBRel(Eq, LAVar "z", LACst (Z.of_int 0)))), Ite (Rel (Ge, Var "x", Var "z"), Assign ("y", Var "x"), Assign ("y", Neg (Var "x"))))) in
      let p = True in
        let q = LBExpr (LBRel (Eq, LAVar "y", LAFunction ("abs", [LAVar "x"]))) in 
      print_string "\n";
      print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))))
    
      let _ = 
        let s = 
          Seq (Assign ("z", Cst (Z.of_int 0)), 
            ( None, Ite (Rel (Ge, Var "x", Var "z"), Assign ("y", Var "x"), Assign ("y", Neg (Var "x"))))) in
        let p = True in
          let q = LBExpr (LBRel (Eq, LAVar "y", LAFunction ("abs", [LAVar "x"]))) in 
        print_string "\n";
        print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))))
      
let _ = 
  let s = 
    Seq (
      Seq ( Assign ("r", Var "a"), (None, Assign ("q", Cst (Z.of_int 0)))),
        (Some (
          And (
            LBExpr (LBRel (Eq, LAVar "r",LAVar "a")),
            And (LBExpr (LBRel (Eq, LAVar "q", LACst (Z.of_int 0))),
                LBExpr (LBRel (Ge, LAVar "r", LACst (Z.of_int 0))))) 
          ),  
          While( (Rel (Ge, Var "r", Var "b")), 
            And (LBExpr (LBRel (Eq, LAVar "a", LABinop (Plus, LABinop (Mult, LAVar "b", LAVar "q"), LAVar "r"))),
            LBExpr (LBRel (Ge, LAVar "r", LACst (Z.of_int 0)))
            ),
            Var "x",
            Seq (Assign ("r", Binop (Minus, Var "r", Var "b")), 
              (None, Assign ("q", Binop (Plus, Var "q", Cst (Z.of_int 1))))))
          )
        )
  in let p =
    LBExpr (LBRel (Ge, LAVar "a", LACst (Z.of_int 0)))
  in 
  let q = And (LBExpr (LBRel (Eq, LAVar "a", LABinop (Plus, LABinop (Mult, LAVar "b", LAVar "q"), LAVar "r"))),
  And (LBExpr (LBRel (Ge, LAVar "r", LACst (Z.of_int 0))), 
    LBExpr (LBRel (Lt, LAVar "r", LAVar "b"))))
in
print_string "\n";
        print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))))

        let _ = 
  let s = 
    Seq (
      Seq ( Assign ("r", Var "a"), (None, Assign ("q", Cst (Z.of_int 0)))),
        (None,  
          While( (Rel (Ge, Var "r", Var "b")), 
            And (LBExpr (LBRel (Eq, LAVar "a", LABinop (Plus, LABinop (Mult, LAVar "b", LAVar "q"), LAVar "r"))),
            LBExpr (LBRel (Ge, LAVar "r", LACst (Z.of_int 0)))
            ),
            Var "x",
            Seq (Assign ("r", Binop (Minus, Var "r", Var "b")), 
              (None, Assign ("q", Binop (Plus, Var "q", Cst (Z.of_int 1))))))
          )
        )
  in let p =
    LBExpr (LBRel (Ge, LAVar "a", LACst (Z.of_int 0)))
  in 
  let q = And (LBExpr (LBRel (Eq, LAVar "a", LABinop (Plus, LABinop (Mult, LAVar "b", LAVar "q"), LAVar "r"))),
  And (LBExpr (LBRel (Ge, LAVar "r", LACst (Z.of_int 0))), 
    LBExpr (LBRel (Lt, LAVar "r", LAVar "b"))))
in
print_string "\n";
print_endline ((String.concat "\n" (List.map string_of_formula (vcgen true p s q))));
print_string "\n";
print_endline (string_of_formula (Impl (p, wp true s q)))
*)