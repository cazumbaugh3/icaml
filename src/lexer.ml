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

type identifier = string

type constructor = string

type tokenT = 
 | PlusT
 | MinusT
 | TimesT
 | EqualT
 | LessT
 | GreaterT
 | ConcatT
 | LparenT
 | RparenT
 | VbarT
 | ArrowT
 | IntT
 | StringT
 | BoolT
 | TypeT
 | OfT
 | FunT
 | ColonT
 | IfT
 | ThenT
 | ElseT
 | CommaT
 | FstT
 | SndT
 | MatchT
 | WithT
 | LetT
 | RecT
 | InT
 | SemisT
 | ConstructT of constructor
 | IdT of identifier
 | NumT of int
 | StrT of string

let print_token token = match token with
 | PlusT -> "+"
 | MinusT -> "-"
 | TimesT -> "*"
 | EqualT -> "="
 | ConcatT -> "^"
 | LessT -> "<"
 | GreaterT -> ">"
 | LparenT -> "("
 | RparenT -> ")"
 | VbarT -> "|"
 | ArrowT -> "->"
 | IntT -> "int"
 | StringT -> "string"
 | BoolT -> "bool"
 | TypeT -> "type"
 | OfT -> "of"
 | FunT -> "fun"
 | ColonT -> ":"
 | IfT -> "if"
 | ThenT -> "then"
 | ElseT -> "else"
 | CommaT -> ","
 | FstT -> "fst"
 | SndT -> "snd"
 | MatchT -> "match"
 | WithT -> "with"
 | LetT -> "let"
 | RecT -> "rec"
 | InT -> "in"
 | SemisT -> ";;"
 | (ConstructT id) -> ("constructor "^id)
 | (IdT id) -> ("identifier "^id)
 | (NumT n) -> "number"
 | (StrT s) -> "string"

let is_digit(ch) = 
   Char.code ch >= Char.code '0' && Char.code ch <= Char.code '9'

let char2digit(ch) = Char.code ch - Char.code '0'

let is_lower_case(ch) = 
   (Char.code ch >= Char.code 'a' && Char.code ch <= Char.code 'z')

let is_upper_case(ch) = 
   (Char.code ch >= Char.code 'A' && Char.code ch <= Char.code 'Z')

let is_letter(ch) = 
     is_lower_case(ch)
  || is_upper_case(ch)

let is_next : string -> char -> bool = fun str -> fun ch ->
  if str = ""
  then false
  else if String.get str 0 = ch
  then true
  else false

let scanNum : string -> (int * string) = fun str ->
  let rec get_num acc str = 
    if str = "" 
    then (acc, str)
    else 
      let c = String.get str 0 and 
          str' = String.sub str 1 (String.length str - 1) in
      if is_digit c
      then get_num (10 * acc + (char2digit c)) str' 
      else (acc, str)
 in get_num 0 str

let scanName : string -> (string * string) = fun str ->
  let rec get_id acc str = 
    if str = "" 
    then (acc, str)
    else 
      let c = String.get str 0 and 
          str' = String.sub str 1 (String.length str - 1) in
      if is_letter c || is_digit c || c = '_' 
      then get_id (acc ^ (String.make 1 c)) str'
      else (acc, str)
 in get_id "" str

let scanString : string -> (string * string) = fun str ->
  let rec get_str acc str =
    if str = ""
      then (acc, str)
      else
        let c = String.get str 0 and
          str' = String.sub str 1 (String.length str - 1) in
        if c = '\"'
          then (acc, str')
        else
          get_str (acc ^ (String.make 1 c)) str'
  in get_str "" str


let rec scan : string -> tokenT list = 
  fun str -> 
   if str = ""
   then []
   else let c = String.get str 0 
        and str1 = String.sub str 1 (String.length str - 1) in
   if is_digit c
   then let (n,str') = scanNum str
         in (NumT n :: (scan str'))
   else if c = '\"'
    then let (s, str') = scanString str1 in
      (StrT s :: (scan str'))
   else if is_upper_case c
   then let (s,str') = scanName str
     in (ConstructT s :: (scan str'))
   else if is_lower_case c
   then let (s,str') = scanName str
     in let token =
       if s = "int" then IntT
       else if s = "string" then StringT
       else if s = "bool" then BoolT
       else if s = "type" then TypeT
       else if s = "of" then OfT
       else if s = "fun" then FunT
       else if s = "if" then IfT
       else if s = "then" then ThenT
       else if s = "else" then ElseT
       else if s = "fst" then FstT
       else if s = "snd" then SndT
       else if s = "match" then MatchT
       else if s = "with" then WithT
       else if s = "let" then LetT
       else if s = "rec" then RecT
       else if s = "in" then InT
       else IdT s
     in (token :: scan str')
   else match c with
     | '+' -> PlusT :: (scan str1)
     | '*' -> TimesT :: (scan str1)
     | '=' -> EqualT :: (scan str1)
     | '^' -> ConcatT :: (scan str1)
     | '<' -> LessT :: (scan str1)
     | '>' -> GreaterT :: (scan str1)
     | '(' -> LparenT :: (scan str1)
     | ')' -> RparenT :: (scan str1)
     | '|' -> VbarT :: (scan str1)
     | ':' -> ColonT :: (scan str1)
     | ',' -> CommaT :: (scan str1)
     | '-' -> if is_next str1 '>'
              then ArrowT :: (scan (String.sub str1 1 (String.length str1 - 1)))
              else MinusT :: (scan str1)
     | ';' -> if is_next str1 ';'
              then SemisT :: (scan (String.sub str1 1 (String.length str1 - 1)))
              else scan str1
     | _ -> scan str1