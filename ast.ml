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

