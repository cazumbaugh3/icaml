(* -- ABSTRACT SYNTAX *)

type identifier = string

type constructor = string

type typeY =
  | IntY
  | StrY
  | BoolY
  | DeclaredY of identifier
  | ProdY of typeY * typeY
  | FunY of typeY * typeY

let rec print_type : typeY -> string =
  fun t ->
   match t with
   | IntY -> "int"
   | StrY -> "string"
   | BoolY -> "bool"
   | DeclaredY s -> s
   | ProdY (t1,t2) ->
       "("^(print_type t1)^" * "^(print_type t2)^")"
   | FunY (t1,t2) ->
       "("^(print_type t1)^" -> "^(print_type t2)^")"

type declareD =
      identifier *
    (constructor * typeY) list

type expE =
  | NumE of int
  | StrE of string
  | IdE of identifier
  | FunE of identifier * typeY * expE
  | ApplyE of expE * expE
  | EqualE of expE * expE
  | LessE of expE * expE
  | GreaterE of expE * expE
  | IfE of expE * expE * expE
  | IfEqE of expE * expE * expE * expE
  | IfLtE of expE * expE * expE * expE
  | PlusE of expE * expE
  | MinusE of expE * expE
  | TimesE of expE * expE
  | ConcatE of expE * expE
  | PairE of expE * expE
  | FstE of expE
  | SndE of expE
  | ConstructE of constructor * expE
  | MatchE of expE * clauseC list

and clauseC = constructor * identifier * expE

type letL =
  | LetVarL of identifier * expE
  | LetFunL of identifier * identifier * typeY * expE
  | LetRecL of identifier * identifier * typeY * expE * typeY

type progP =
    (declareD list)
  * (letL list)
  * expE