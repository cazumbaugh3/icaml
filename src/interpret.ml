open Environment
open Syntax
open Parser
open Typing

exception OperandNotInteger
exception ApplyNotClosure
exception FstNotPair
exception SndNotPair
exception MatchWithNotConstructor
exception MatchNotFound
exception OutputClosure
exception InterpreterIncomplete


type value =
   NumV of int
 | StrV of string
 | BoolV of bool
 | PairV of value * value
 | ConstructV of constructor * value
 | ClosureV of identifier * expE * value environment
 | FixV of identifier * identifier * expE * value environment

let rec print_value : value -> string =
  fun v -> 
   match v with
   | NumV v -> string_of_int v
   | StrV v -> v
   | BoolV v -> string_of_bool v
   | PairV(v1,v2) ->
         "( "^(print_value v1)^" , "^(print_value v2)^" )"
   | ConstructV(c,v0) ->
         c^" "^(print_value v0)
   | ClosureV _ -> raise OutputClosure
   | FixV _ -> raise OutputClosure

let rec getClause con clauseL = 
	match clauseL with
	| [] -> None
	| (c, i, e1) :: t ->
		if c = con
			then Some (c, i, e1)
		else getClause con t

(* -- EVALUATING *)

let rec evalE : Syntax.expE -> (value environment) -> value =
  fun exp env ->
   match exp with
   | NumE n -> NumV n
   | StrE s -> StrV s
   | IdE x -> retrieveEnv env x
   | FunE (x, tx, exp0) -> ClosureV (x, exp0, env)
   | ApplyE(exp1, exp2) -> 
       (match (evalE exp1 env, evalE exp2 env) with
         | (ClosureV(x,exp0,env0), v2) ->
               evalE exp0 (insertEnv x v2 env0)
         | (FixV(f,x,exp0,env0), v2) ->
               evalE exp0
                 (insertEnv f (FixV (f,x,exp0,env0)) 
                    (insertEnv x v2 env0))
         | _ -> raise ApplyNotClosure)
   | IfE(e0, e1, e2) ->
      let test = evalE e0 env in
      (match test with
      | BoolV b ->
        if b
          then evalE e1 env
        else evalE e2 env
      | _ -> raise OperandNotInteger)
   | IfEqE(e0L,e0R,e1,e2) -> 
      let eqLHS = evalE e0L env in
      let eqRHS = evalE e0R env in
      if eqLHS = eqRHS
        then evalE e1 env
        else evalE e2 env
   | IfLtE(e0L,e0R,e1,e2) -> 
      let ltLHS = evalE e0L env in
      let ltRHS = evalE e0R env in
      if ltLHS < ltRHS 
        then evalE e1 env
        else evalE e2 env
   | PlusE(e1,e2) ->
      let lhs = evalE e1 env in
      let rhs = evalE e2 env in
      (match (lhs, rhs) with
        | (NumV n1, NumV n2) -> NumV (n1 + n2)
        | _ -> raise OperandNotInteger
      )
   | MinusE(e1,e2) -> 
      let lhs = evalE e1 env in
      let rhs = evalE e2 env in
      (match (lhs, rhs) with
        | (NumV n1, NumV n2) -> NumV (n1 - n2)
        | _ -> raise OperandNotInteger
      )
   | TimesE(e1,e2) -> 
      let lhs = evalE e1 env in
      let rhs = evalE e2 env in
      (match (lhs, rhs) with
        | (NumV n1, NumV n2) -> NumV (n1 * n2)
        | _ -> raise OperandNotInteger
      )
   | EqualE(e1, e2) ->
    let lhs = evalE e1 env in
    let rhs = evalE e2 env in
    BoolV (lhs = rhs)
   | LessE(e1, e2) ->
    let lhs = evalE e1 env in
    let rhs = evalE e2 env in
    BoolV(lhs < rhs)
   | GreaterE(e1, e2) ->
    let lhs = evalE e1 env in
    let rhs = evalE e2 env in
    BoolV(lhs > rhs)
   | ConcatE(e1, e2) ->
      let lhs = evalE e1 env in
      let rhs = evalE e2 env in
      (match (lhs, rhs) with
      | (StrV s1, StrV s2) -> StrV (s1 ^ s2)
      | _ -> raise OperandToConcatNotStringType)
   | PairE(e1,e2) -> 
	  let v1 = evalE e1 env in
	  let v2 = evalE e2 env in
	    PairV (v1, v2)
   | FstE(e0) -> 
	  let v0 = evalE e0 env in
	  (match v0 with
	  | PairV (v1, v2) -> v1
	  | _ -> raise FstNotPair)
   | SndE(e0) -> 
	  let v0 = evalE e0 env in
	  (match v0 with
	  | PairV(v1, v2) -> v2
	  | _ -> raise SndNotPair)
   | ConstructE(c,e0) -> 
	  let v0 = evalE e0 env in
	  ConstructV (c, v0)
   | MatchE(e0,clauses) -> 
	  (match evalE e0 env with
	  | ConstructV(c, v1) ->
		let mat = getClause c clauses in
		(match mat with
		| None -> raise MatchNotFound
		| Some (c', i, e1) -> 
			evalE e1 (insertEnv i v1 env)
		)
	  | _ -> raise MatchWithNotConstructor
	  )

let rec eval_binding : letL -> value environment -> value environment =
   fun binding env ->
    match binding with
    | LetVarL(x,e) ->
         insertEnv x (evalE e env) env
    | LetFunL(f,x,tx,e) -> 
		let funE = FunE(x, tx, e) in
			insertEnv f (evalE funE env) env
    | LetRecL(f,x,tx,e,t) -> 
		let fixed = FixV (f, x, e, env) in
		let funE = FunE(x, tx, e) in
		insertEnv f (evalE funE (insertEnv f fixed env)) env
		

let rec eval_bindings : letL list -> value environment -> value environment =
  fun bindings env ->
    match bindings with
    | [] -> env
    | (binding :: bindings') ->
         eval_bindings bindings' (eval_binding binding env)

let rec evalP : progP -> value =
   fun (_, bindings, main) -> 
  evalE main (eval_bindings bindings initEnv)

let run input = 
 try (
  let p = parse input in 
  let t = typeP p in
  let _ = print_string ("Type is: "^(print_type t)^"\n") in
  let v = evalP p in
 print_value v )
  with
   | InputEndsButExpected s ->
       "input ends though had expected '"^s^"'\n"
   | TokenSeenButExpected (s1,s2) ->
       "saw '"^s2^"' but had expected '"^s1^"'\n"
   | ExtraInput ->
       "input continues after program is parsed\n"
   | ParserIncomplete ->
       "the parser doesn't yet handle this construct\n"
   | NotDeclared s ->
        "identifier "^s^" used but not declared\n"
   | OperandNotIntegerType ->
       "operand not of integer type\n"
   | FunNotFunType ->
       "function part of application not of function type\n"
   | FunMismatchType ->
       "argument type does not match function type\n"
   | BranchesMismatch ->
       "types of branches in 'if' expression do not match\n"
   | FstNotPairType ->
       "argument to 'fst' not of product type\n"
   | SndNotPairType ->
       "argument to 'snd' not of product type\n"
   | ConstructorMismatch ->
       "argument to constructor not of appropriate type\n"
   | MatchWithNotSumType ->
       "what is being matched is not of a sum type\n"
   | MatchNoClauses ->
       "match expression has no clauses\n"
   | ClauseNotMatch ->
       "constructor in branch does not form type of matched expression\n"
   | ClausesMismatch ->
       "types of branches do not match\n"
   | RecConflictType ->
       "body of recursive function not of declared type\n"
   | TypeCheckerIncomplete ->
       "the type checker doesn't yet handle this construct\n"
   | OperandNotInteger ->
       "operand not integer\n"
   | OperandToConcatNotStringType ->
       "operand to concat function not string\n"
   | ApplyNotClosure ->
       "function part of application does not evaluate to closure\n"
   | FstNotPair ->
       "argument to 'fst' not a pair\n"
   | SndNotPair ->
       "argument to 'snd' not a pair\n"
   | MatchWithNotConstructor ->
       "what is being matched is not formed by constructor\n"
   | MatchNotFound ->
       "match fails: no case for the given constructor\n"
   | OutputClosure ->
       "a closure is part of what is being returned\n"
   | InterpreterIncomplete ->
       "the interpreter doesn't yet handle this construct\n"

let rec interp s = 
	print_string "> ";
	let input = read_line () in
	match input with
	| "Q" -> print_string "Bye"
	| "E" -> 
		let v = run s in
		print_string v; print_char '\n';
		interp ""
	| s' -> 
		interp (s ^ s') ;;

interp "" ;;