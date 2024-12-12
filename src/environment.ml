(* -- ENVIRONMENTS *)

exception NotDeclared of string

type 'a environment = string -> 'a

let initEnv : 'a environment = 
  fun id -> raise (NotDeclared id)

let insertEnv : string -> 'a -> 'a environment -> 'a environment =
  fun new_str a env ->
    fun str -> if str = new_str then a else env str

let retrieveEnv : 'a environment -> string -> 'a =
  fun env str -> env str