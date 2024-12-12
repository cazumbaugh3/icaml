(*
Grammar

Types:

  T ::=   int
        | I
        | (T -> T)
        | (T * T)

Expressions:

  E ::=   N                             number
        | I                             identifier
        | (fun I:T -> E)                anonymous function definition
        | (E E)                         function application
        | (if relop E then E else E)    conditional, with relop either < or =
        | (E op E)                      arithmetic operation, with op either + or - or *
        | (E , E)                       make a pair
        | (fst E)                       first component of a pair
        | (snd E)                       second component of a pair
        | (C E)                         apply constructor
        | (match E with B)              match E with various patterns where B is a sequence of clauses of the form | C I -> E

Let Bindings:

  L ::=   let I = E
        | let I (I:T) = E
        | let rec I (I:T) = (E : T)

*)
open Lexer ;;
open Syntax ;;

exception InputEndsButExpected of string
exception TokenSeenButExpected of string * string
exception ExtraInput
exception ParserIncomplete

let expectToken : tokenT -> tokenT list -> tokenT list = 
  fun expected tokens -> 
   match tokens with
   |  [] -> raise (InputEndsButExpected (print_token expected))
   | token1 :: tokens' -> 
       if token1 = expected
       then tokens'
       else raise (TokenSeenButExpected (print_token expected, print_token token1))

let getIdT : tokenT list -> string * tokenT list =
  fun tokens -> 
   match tokens with
   | [] -> raise (InputEndsButExpected "an identifier")
   | (IdT id) :: tokens' -> (id, tokens')
   | (token :: _) -> 
       raise (TokenSeenButExpected ("an identifier", print_token token))

let getConstructT : tokenT list -> string * tokenT list =
  fun tokens -> 
   match tokens with
   | [] -> raise (InputEndsButExpected "a constructor")
   | (ConstructT id) :: tokens' -> (id, tokens')
   | (token :: _) -> 
       raise (TokenSeenButExpected ("a constructor", print_token token))

let rec parseType : tokenT list -> typeY * tokenT list =
   fun tokens ->
    match tokens with
    | [] -> raise (InputEndsButExpected "a type")
    | (IntT :: tokens1) ->
         (IntY, tokens1)
    | (StringT :: tokens1) ->
        (StrY, tokens1)
    | (BoolT :: tokens1) ->
        (BoolY, tokens1)
    | (IdT id :: tokens1) ->
         (DeclaredY id, tokens1)
    | (LparenT :: tokens1) ->
         let (typ1, tokens2) = parseType tokens1 in
        (match tokens2 with
         | [] -> raise (InputEndsButExpected "'*' or '->'")
         | (TimesT :: tokens3) ->
           let (typ2, tokens4) = parseType tokens3 in
           (ProdY (typ1, typ2), expectToken RparenT tokens4)
         | (ArrowT :: tokens3) ->
               let (typ2, tokens4) = parseType tokens3 in
                  (FunY (typ1,typ2), expectToken RparenT tokens4)
         | (token :: _) -> raise (TokenSeenButExpected ("'*' or '->'", print_token token)))
    | (token :: _) -> raise (TokenSeenButExpected ("a type", print_token token))

let rec parseConstructors : 
      tokenT list -> ((constructor * typeY) list) * tokenT list =
   fun tokens ->
    match tokens with
    | [] -> ([], tokens)
    | (VbarT :: tokens1) ->
         let (c1,tokens2) = getConstructT tokens1 in
         let (typ1, tokens3) = parseType (expectToken OfT tokens2) in
         let (constrs, tokens4) = parseConstructors tokens3 in
        (((c1,typ1) :: constrs), tokens4)
    | _ -> ([], tokens)

let parseDecl : tokenT list -> declareD * tokenT list =
          (* called after the 'type' has been parsed *)
   fun tokens ->
      let (id, tokens1) = getIdT tokens in
      let (constrs, tokens2) = parseConstructors (expectToken EqualT tokens1) in
     ((id, constrs), tokens2)

let rec parseDecls : tokenT list -> declareD list * tokenT list =
   fun tokens ->
     match tokens with
     | [] -> ([], tokens)
     | (TypeT :: tokens1) ->
           let (decl, tokens2) = parseDecl tokens1 in
           let (decls, tokens3) = parseDecls tokens2 in
          (decl :: decls, tokens3)
     | _ -> ([], tokens)

let getNextToken tokens = 
  match tokens with
  | (h :: t) -> (h, t)
  | _ -> raise (InputEndsButExpected "a relop") 

let rec parseExp : tokenT list -> expE * tokenT list =
   fun tokens ->
    match tokens with
    | [] -> raise (InputEndsButExpected "an expression")
    | (NumT z) :: tokens1 ->
         (NumE z, tokens1)
    | (StrT s) :: tokens1 ->
         (StrE s, tokens1)
    | (IdT s) :: tokens1 ->
         (IdE s, tokens1)
    | LparenT :: tokens1 ->
         (match tokens1 with
          | FunT :: tokens2 ->
             let (x, tokens3) = getIdT tokens2 in
             let (t, tokens4) = parseType (expectToken ColonT tokens3) in
             let (e, tokens5) = parseExp (expectToken ArrowT tokens4) in
            (FunE (x,t,e), expectToken RparenT tokens5)
         | IfT :: tokens2 ->
            parseIfExp tokens2
         | (FstT :: tokens2) -> 
          let (e1, tokens3) = parseExp tokens2 in
            (FstE e1,  expectToken RparenT tokens3)
         | (SndT :: tokens2) -> 
          let (e1, tokens3) = parseExp tokens2 in
            (SndE e1, expectToken RparenT tokens3)
         | (ConstructT c :: tokens2) -> 
			let (e, tokens3) = parseExp tokens2 in
			(ConstructE (c, e), expectToken RparenT tokens3)
         | (MatchT :: tokens2) -> 
			let (e, tokens3) = parseExp tokens2 in
			let (clauses, tokens4) = parseClauses (expectToken WithT tokens3) in
			(MatchE(e, clauses), expectToken RparenT tokens4)
         | _ -> 
          let (e1, tokens2) = parseExp tokens1 in
        (match tokens2 with
         | [] -> raise (InputEndsButExpected "the second operand")
         | (PlusT :: tokens3) -> 
            let (e2, tokens4) = parseExp tokens3 in
            (PlusE (e1, e2), expectToken RparenT tokens4)
         | (MinusT :: tokens3) -> 
            let (e2, tokens4) = parseExp tokens3 in
            (MinusE (e1, e2), expectToken RparenT tokens4)
         | (TimesT :: tokens3) -> 
            let (e2, tokens4) = parseExp tokens3 in
            (TimesE(e1, e2), expectToken RparenT tokens4)
         | (EqualT :: tokens3) ->
          let (e2, tokens4) = parseExp tokens3 in
          (EqualE(e1, e2), expectToken RparenT tokens4)
         | (LessT :: tokens3) ->
          let (e2, tokens4) = parseExp tokens3 in
          (LessE(e1, e2), expectToken RparenT tokens4)
         | (GreaterT :: tokens3) ->
          let (e2, tokens4) = parseExp tokens3 in
          (GreaterE(e1, e2), expectToken RparenT tokens4)
		 | (ConcatT :: tokens3) ->
			let (e2, tokens4) = parseExp tokens3 in
			(ConcatE(e1, e2), expectToken RparenT tokens4)
         | (CommaT :: tokens3) -> 
          let (e2, tokens4) = parseExp tokens3 in
          (PairE (e1, e2), expectToken RparenT tokens4)
         | _ ->
              let (e2, tokens3) = parseExp tokens2
               in (ApplyE (e1,e2), expectToken RparenT tokens3)))
     | token :: _ -> raise (TokenSeenButExpected 
                       ("the start of an expression", print_token token))

and parseIfExp tokens = 
  let (relop, tokens3) = parseExp tokens in
  let (thenBody, tokens4) = parseExp (expectToken ThenT tokens3) in
  let (elseBody, tokens5) = parseExp (expectToken ElseT tokens4) in
  	(IfE(relop, thenBody, elseBody), expectToken RparenT tokens5)



and parseClauses : 
      tokenT list -> (clauseC list) * tokenT list =
   fun tokens ->
    match tokens with
    | [] -> ([], tokens)
    | (VbarT :: tokens1) ->
		parseClause tokens
    | _ -> ([], tokens)

and parseClause tokens = 
	match tokens with
	| [] -> raise (InputEndsButExpected "a clause")
	| (VbarT :: ConstructT c :: IdT id :: ArrowT :: tokens1) ->
		let (e, tokens2) = parseExp tokens1 in
		(match tokens2 with
		| (VbarT :: _) -> 
			let (clauses, tokens3) = parseClauses tokens2 in
			((c, id, e) :: clauses, tokens3)
		| _ -> ([(c, id, e)], tokens2))
	| (t :: tokens') -> raise (TokenSeenButExpected ("a clause", (print_token t)))

let rec parseBinding : tokenT list -> letL * tokenT list =
          (* called after the 'let' has been parsed *)
   fun tokens ->
    match tokens with
    | [] -> raise (InputEndsButExpected "a binding")
    | (IdT x) :: EqualT :: tokens1 -> 
           (* let I = E *)
           let (e, tokens2) = parseExp tokens1 in
           (LetVarL (x, e), tokens2)
    | (IdT f) :: LparenT :: (IdT x) :: ColonT :: tokens1 ->
           let (t, tokens2) = parseType tokens1 in
		   let (e, tokens3) = parseExp (expectToken EqualT (expectToken RparenT tokens2)) in
		   (LetFunL (f, x, t, e), tokens3)
    | RecT :: (IdT f) :: LparenT :: (IdT x) :: ColonT :: tokens1 ->
         let (t1, tokens2) = parseType tokens1 in
         let (e, tokens3) = parseExp 
                              (expectToken LparenT
                                (expectToken EqualT 
                                  (expectToken RparenT tokens2))) in
         let (t2, tokens4) = parseType (expectToken ColonT tokens3) in
       (LetRecL (f, x, t1, e, t2), expectToken RparenT tokens4)
    | (token :: _) -> raise (TokenSeenButExpected ("a binding", print_token token))

let rec parseBindings : tokenT list -> letL list * tokenT list =
   fun tokens ->
     match tokens with
     | [] -> ([], tokens)
     | (LetT :: tokens1) -> 
      let (b, tokens2) = parseBinding tokens1 in
      (match tokens2 with
        | SemisT :: tokens3 ->
          let (bnds, tokens4) = parseBindings tokens3 in
          (b :: bnds, tokens4)
        | _ -> ([b], tokens2))
     | _ -> ([], tokens)

let parseProg : tokenT list -> progP * tokenT list =
  fun tokens ->
    let (decls, tokens1) = parseDecls tokens in
    let (bindings, tokens2) = parseBindings tokens1 in
    let (main, tokens3) = parseExp tokens2 in
  ((decls, bindings, main), tokens3)

let parse : string -> progP =
  fun input_string ->
    let tokens = scan input_string in
    let (prog,tokens1) = parseProg tokens
    in if tokens1 = []
      then prog
      else raise ExtraInput
(*
let rec run () = 
	print_string "> ";
	let input = read_line () in
	match input with
	| "Q" -> print_string "Bye"
	| _ ->
		(let tokens = Lexer.scan input in
		let (parse_tree, tokens') = parse_expression tokens in
		if tokens' = []
			then print_parse_tree parse_tree
			else raise (Parse "Source ends too late")); 
		print_string "\n";
		run () ;;

run () ;;*)