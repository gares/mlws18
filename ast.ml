type pos = [%import: Lexing.position] [@@deriving show]
type position = pos * pos [@@deriving show]

type term =
 | Const of string
 | Int of int
 | App of ast * ast
 | Lam of string * ast
 | Let of string * ast * ast
 | Eq  of ast * ast
and ast = { loc : position; v : term }
[@@deriving show]

let rec pp_tree s { loc = ({ Lexing.pos_cnum = a }, { Lexing.pos_cnum = b });
                    v } =
  Printf.printf "%s\n" (String.sub s a (b-a));
  match v with
  | Eq(l,r) -> pp_tree s l; pp_tree s r
  | App(l,r) -> pp_tree s l; pp_tree s r
  | Let(_,l,r) -> pp_tree s l; pp_tree s r
  | Lam(_,l) -> pp_tree s l
  | _ -> ()
  
