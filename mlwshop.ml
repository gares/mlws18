(* terms: we use a uuid to refer to some specific nodes ******************** *)

type uuid = string

type term =
 | Const of string
 | Var of int (* De Bruijn indexes *)
 | App of term * term
 | Lam of term
 | Let of uuid * term * term
 | Eq  of uuid * term * term

(* {{{ examples *)

(* yes, one should have a parser to build these... *)

let comma, nil, cons, one, size =
  Const "comma", Const "xnil", Const "xcons", Const "one", Const "size"

let example0 =
 "let id x = (x,1) in id []",
  Let ("?id", Lam (App (App (comma, Var 0),one)),App(Var 0, nil))
;;

let example1 =
  "let id x = x in (id 1, size (id []))",
  Let ("?id", Lam (Var 0),
    (App (App (comma,
       App (Var 0, one)),
       App (size, App (Var 0, nil)))))
;;

let example2 =
  "let id x = x in id [1] = []",
  Let ("?id", Lam (Var 0),
       Eq("?eq",App (Var 0, App(App(cons,one), nil)),
               nil))
;;

let example3 =
  "[1] = (1,1)",
  Eq("?eq",App (App (cons, one), nil),
           App (App (comma, one), one))
;;

let example4 =
  "size 1",
  App(size, one)
;;
        
(* }}} *)                        

open Elpi_API
module E  = Extend.Data
module C  = Extend.Compile
module Pp = Extend.Pp
module M  = Data.StrMap
module BI = Extend.BuiltInPredicate
module CS = Extend.CustomState

(* terms -> elpi terms ***************************************************** *)

let appc = E.Constants.from_stringc "app"
let lamc = E.Constants.from_stringc "lam"
let letc = E.Constants.from_stringc "let"
let eqc  = E.Constants.from_stringc "eq"

let cs_uuid = C.State.declare ~name:"uuid-map"
  ~init:(fun _ -> M.empty)
  ~pp:(M.pp Format.pp_print_string)

let mkQ st uuid =
  let st, name, t = C.fresh_Arg st ~name_hint:uuid ~args:[] in
  let st = C.State.update cs_uuid st (M.add name uuid) in
  st, t

let rec term2elpi st ctx = function
  | Const s -> st, E.Constants.from_string s
  | Var x -> st, E.mkConst (ctx - x - 1)
  | App(h,a) ->
     let st, h = term2elpi st ctx h in
     let st, a = term2elpi st ctx a in
     st, E.mkApp appc h [a]
  | Lam t ->
     let st, t = term2elpi st (succ ctx) t in
     st, E.mkApp lamc (E.mkLam t) []
  | Let(uuid, t, b) ->
     let st, t = term2elpi st ctx t in
     let st, b = term2elpi st (succ ctx) b in
     let st, ty = mkQ st uuid in
     st, E.mkApp letc t [ty; E.mkLam b]
  | Eq(uuid, lhs, rhs) ->
     let st, lhs = term2elpi st ctx lhs in
     let st, rhs = term2elpi st ctx rhs in
     let st, cmpf = mkQ st uuid in
     st, E.mkApp eqc cmpf [lhs;rhs]

let rs_uuid = CS.declare ~name:"uuid-map"
  ~init:(CS.CompilerState (cs_uuid, fun x -> x))
  ~pp:(M.pp Format.pp_print_string)

(* builtin ***************************************************************** *)

exception TypeError of E.term * E.term * E.term

let pp_err t ty ety =
  Format.printf "Type error:@ the term %a@ has type %a@ but is expected to have type %a\n%!" (Pp.term 0) t (Pp.term 0) ty (Pp.term 0) ety

let extra_builtins = let open BI in [
  MLCode(Pred("type-error",
    In(any,"the term",
    In(any,"its type",
    In(any,"the type expected by its context",
    Easy("raise a fatal type inference error")))),
    (fun t ty ety ~depth:_ -> raise (TypeError(t,ty,ety)))),
  DocNext)
]

let _ =
  Format.printf "\n========= builtins ==========\n%!";
  BI.document Format.std_formatter extra_builtins
;;

(* w *********************************************************************** *)

let w =
  (* load the elpi program *)
  let elpi_flags =
    try
      let ic, _ as p = Unix.open_process "elpi -where 2>/dev/null" in
      let w = input_line ic in
      let _ = Unix.close_process p in ["-I";w]
    with _ -> [] in
  let builtins = BI.builtin_of_declaration
    (Elpi_builtin.std_declarations @ extra_builtins) in
  let header, _ = Setup.init ~builtins ~basedir:"./" elpi_flags in
  let p = Parse.program ["w.elpi"] in
  let p = Compile.program header [p] in

fun (text, ast) ->
  (* run w on a term *)
  let q = C.query p (fun ~depth st ->
    let st, ast = term2elpi st depth ast in
    let st, ty = mkQ st "?ty" in
    st, E.mkApp (E.Constants.from_stringc "w") ast [ty]) in
  
  if not (Compile.static_check header q) then
    failwith "w.elpi does not type check";

  let exe = Compile.link q in

  Format.printf "\n========= W: %s ==========\n%!" text;
  match Execute.once exe with
  | Execute.Success { Data.assignments; state } ->
      M.iter (fun k v ->
        Format.printf "%s := %a@\n" (M.find k (CS.get rs_uuid state))
                                    (Pp.term 0) (E.of_term v))
        assignments
  | Failure -> failwith "w.elpi is buggy"
  | NoMoreSteps -> assert false
  | exception TypeError(t,ty,ety) -> pp_err t ty ety
;;

(* main ******************************************************************** *)

let _ = w example0
let _ = w example1
let _ = w example2
let _ = w example3
let _ = w example4

(* vim:set foldmethod=marker: *)
