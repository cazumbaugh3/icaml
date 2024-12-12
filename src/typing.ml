open Environment
open Syntax

exception OperandNotIntegerType
exception OperandToConcatNotStringType
exception FunNotFunType
exception FunMismatchType
exception BranchesMismatch
exception FstNotPairType
exception SndNotPairType
exception ConstructorMismatch
exception MatchWithNotSumType
exception MatchNoClauses
exception ClauseNotMatch
exception ClausesMismatch
exception RecConflictType
exception TypeCheckerIncomplete

type constructorEnv = (identifier * typeY) environment

let updateCEnv : declareD -> constructorEnv -> constructorEnv =
   fun (tid, constrs) -> fun cenv0 ->
      List.fold_right 
          (fun (c1,t1) -> fun cenv ->
               insertEnv c1 (tid, t1) cenv)
          constrs
          cenv0
 
let rec updatesCEnv : declareD list -> constructorEnv -> constructorEnv =
   fun decls -> fun cenv0 ->
     match decls with
     | [] -> cenv0
     | d1 :: ds -> updatesCEnv ds (updateCEnv d1 cenv0)

let validateClauseConstructor expectedType con = 
	match expectedType with
	| DeclaredY t -> 
		if t = con
			then true
			else raise ClauseNotMatch
	| _ -> raise MatchWithNotSumType

  let rec typesEqual t1 t2 = 
    match (t1, t2) with
    | (IntY, IntY) -> true
    | (StrY, StrY) -> true
    | (BoolY, BoolY) -> true
    | (DeclaredY c1, DeclaredY c2) -> c1 = c2
    | (ProdY (p1, p2), ProdY(p1', p2')) ->
      (typesEqual p1 p1') && (typesEqual p2 p2')
    | (FunY (f1, f2), FunY(f1', f2')) ->
      (typesEqual f1 f1') && typesEqual f2 f2'
    | _ -> false

let rec typeE : expE -> constructorEnv -> (typeY environment) -> typeY =
   fun exp cenv tenv -> 
    match exp with
   | NumE n -> IntY
   | StrE s -> StrY
   | IdE x -> retrieveEnv tenv x
   | FunE (x, tx, e) ->
        let t = typeE e cenv (insertEnv x tx tenv) in
       FunY(tx, t)
   | ApplyE(e1, e2) -> 
        let t1 = typeE e1 cenv tenv in
        let t2 = typeE e2 cenv tenv in
      (match t1 with
       | FunY(t0,t) -> 
            if (typesEqual t2 t0) then t else raise FunMismatchType
       | _ -> raise FunNotFunType)
  | IfE(e0, e1, e2) ->
    let e0T = typeE e0 cenv tenv in
    let e1T = typeE e1 cenv tenv in
    let e2T = typeE e2 cenv tenv in
      if e0T != BoolY 
        then raise OperandNotIntegerType
      else if (typesEqual e1T e2T)
        then e1T
	      else raise BranchesMismatch
  | IfEqE(e0L,e0R,e1,e2) -> 
    typeIfE (e0L, e0R, e1, e2) cenv tenv
  | IfLtE(e0L,e0R,e1,e2) -> 
    typeIfE (e0L, e0R, e1, e2) cenv tenv
  | PlusE(e1,e2) -> 
    typeBinOpE (e1, e2) cenv tenv
  | MinusE(e1,e2) -> 
    typeBinOpE (e1, e2) cenv tenv
  | TimesE(e1,e2) -> 
    typeBinOpE (e1, e2) cenv tenv
  | EqualE(e1, e2) ->
    let e1t = typeE e1 cenv tenv in
    let e2t = typeE e2 cenv tenv in
    if (typesEqual e1t e2t)
      then BoolY
      else raise OperandNotIntegerType 
  | LessE(e1, e2) ->
    let e1t = typeE e1 cenv tenv in
    let e2t = typeE e2 cenv tenv in
    if (typesEqual e1t e2t)
      then BoolY
    else raise OperandNotIntegerType
  | GreaterE(e1, e2) ->
    let e1t = typeE e1 cenv tenv in
    let e2t = typeE e2 cenv tenv in
      if (typesEqual e1t e2t)
        then BoolY
      else raise OperandNotIntegerType
  | ConcatE(e1, e2) ->
    let t1 = typeE e1 cenv tenv in
    let t2 = typeE e2 cenv tenv in
      (match (t1, t2) with
      | (StrY, StrY) -> StrY
      | _ -> raise OperandToConcatNotStringType)
  | PairE(e1,e2) -> 
    let e1t = typeE e1 cenv tenv in
    let e2t = typeE e2 cenv tenv in
      ProdY(e1t, e2t)
  | FstE(e0) -> 
		let t = typeE e0 cenv tenv in
      (match t with
      | ProdY (t1, t2) -> t1
      | _ -> raise FstNotPairType)
  | SndE(e0) -> 
    let t = typeE e0 cenv tenv in
      (match t with
      | ProdY (t1, t2) -> t2
      | _ -> raise SndNotPairType)
  | ConstructE(c,e0) -> 
	let (con, cType) = retrieveEnv cenv c in
    let eT = typeE e0 cenv tenv in
      if (typesEqual eT cType)
        then DeclaredY con
        else raise ConstructorMismatch
  | MatchE(e,clauses) -> 
    let expType = typeE e cenv tenv in
    let clauseType = getClauseType expType clauses cenv tenv in
      (match clauseType with
      | None -> raise MatchNoClauses
      | Some t -> t)
	


and getClauseType expType clauses cenv tenv = 
	match clauses with
	| [] -> None
	| [(c, i, e)] -> 
		let (cName, cType) = retrieveEnv cenv c in
		let _ = validateClauseConstructor expType cName in
		  Some (typeE (FunE(i, cType, e)) cenv tenv)
	| (c, i, e) :: t ->
		let (cName, cType) = retrieveEnv cenv c in
		let _ = validateClauseConstructor expType cName in
		let t1 = typeE (FunE(i, cType, e)) cenv tenv in
		let t2 = getClauseType expType t cenv tenv in
      (match t2 with
      | None -> None
      | Some (v) ->
        match (t1, v) with
        | (FunY(i1, v1), FunY(i2, v2)) ->
          if (typesEqual v1 v2) then Some v1
          else
            raise ClausesMismatch
        | _ -> raise ClausesMismatch)
			
and typeIfE exps cenv tenv =
  match exps with (e0L, e0R, e1, e2) ->
    let e0Lt = typeE e0L cenv tenv in
    let e0Rt = typeE e0L cenv tenv in
      if e0Lt != IntY && e0Rt != e0Lt
        then raise OperandNotIntegerType
      else
        let e1t = typeE e1 cenv tenv in
        let e2t = typeE e2 cenv tenv in
        if (typesEqual e1t e2t)
          then e1t
        else
          raise BranchesMismatch

and typeBinOpE exps cenv tenv = 
  match exps with (e1, e2) ->
    let e1T = typeE e1 cenv tenv in
    let e2T = typeE e2 cenv tenv in
      match (e1T, e2T) with
      | (IntY, IntY) -> IntY
      | _ -> raise OperandNotIntegerType
  

let typeL : 
   letL -> constructorEnv -> (typeY environment) -> (typeY environment) =
  fun binding cenv tenv ->
    match binding with
    | LetVarL(x,e) -> 
      let t = typeE e cenv tenv in
        insertEnv x t tenv
    | LetFunL(f,x,tx,e) ->
        let t1 = typeE e cenv (insertEnv x tx tenv) in
           insertEnv f (FunY (tx, t1)) tenv 
    | LetRecL(f,x,tx,e,t) -> 
      let ft = FunY (tx, t) in
      let t1 = typeE e cenv (insertEnv f (FunY (tx, t)) (insertEnv x tx tenv)) in
        if t1 = t
          then insertEnv f ft tenv
          else raise RecConflictType

let typeLs :
   letL list -> constructorEnv -> (typeY environment) -> (typeY environment) =
  fun decls cenv tenv0 ->
    List.fold_left
        (fun tenv -> fun decl ->
             typeL decl cenv tenv)
        tenv0
        decls

let typeP : progP -> typeY =
   fun (decls, bindings, main) ->
     let cenv = updatesCEnv decls initEnv in
     let tenv = typeLs bindings cenv initEnv in
    typeE main cenv tenv