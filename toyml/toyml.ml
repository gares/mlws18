open Ast

open Elpi_API
module E  = Extend.Data
module C  = Extend.Compile
module Pp = Extend.Pp
module M  = Data.StrMap
module BI = Extend.BuiltInPredicate
module CS = Extend.CustomState

(* output from elpi  *************************************************** *)

let cs_output = C.State.declare ~name:"output-map"
  ~init:(fun _ -> M.empty) ~pp:(M.pp pp_position)
let rs_output = CS.declare ~name:"output-map"
  ~init:(CS.CompilerState (cs_output, fun x -> x)) ~pp:(M.pp pp_position)

let mkQ ?(name_hint="q") st loc =
  let st, name, t = C.fresh_Arg st ~name_hint ~args:[] in
  let st = C.State.update cs_output st (M.add name loc) in
  st, t

module P = Pmap.Make(struct type t = E.term let hash = Hashtbl.hash end)

let cs_positions = C.State.declare ~name:"positions"
  ~init:(fun _ -> P.empty) ~pp:(fun _ _ -> ())
let rs_positions = CS.declare ~name:"positions"
  ~init:(CS.CompilerState (cs_positions, fun x -> x)) ~pp:(fun _ _ -> ())

let save_position loc (st, t) =
  let st = C.State.update cs_positions st (P.add t loc) in
  st, t

(* terms -> elpi terms ************************************************** *)

let appc     = E.Constants.from_stringc "app"
let lamc     = E.Constants.from_stringc "lam"
let letc     = E.Constants.from_stringc "let"
let eqc      = E.Constants.from_stringc "eq"
let literalc = E.Constants.from_stringc "literal"
let globalc  = E.Constants.from_stringc "global"

let rec lookup x = function
  | [] -> E.mkApp globalc (E.C.of_string x) []
  | y :: ys when x = y -> E.mkConst (List.length ys)
  | _ :: ys -> lookup x ys

let rec embed st ctx { v; loc } = save_position loc begin
  match v with
  | Const s -> st, lookup s ctx
  | Int n -> st, E.mkApp literalc (E.C.of_int n) []
  | App(h,a) ->
     let st, h = embed st ctx h in
     let st, a = embed st ctx a in
     st, E.mkApp appc h [a]
  | Lam (n,t) ->
     let st, t = embed st (n :: ctx) t in
     st, E.mkApp lamc (E.mkLam t) []
  | Let(n, t, b) ->
     let st, ty = mkQ st t.loc in
     let st, t = embed st ctx t in
     let st, b = embed st (n :: ctx) b in
     st, E.mkApp letc t [ty; E.mkLam b]
  | Eq(lhs, rhs) ->
     let st, lhs = embed st ctx lhs in
     let st, rhs = embed st ctx rhs in
     st, E.mkApp eqc lhs [rhs]
end

(* builtin *************************************************************** *)

exception TypeError of {
  assignments : E.term M.t;
  state : E.custom_state;

  t : E.term;
  ty : E.term;
  ety : E.term;
}
exception NotEqType of {
  assignments : E.term M.t;
  state : Data.custom_state;

  t : E.term;
}

let extra_builtins = let open BI in [

  MLCode(Pred("type-error",
    In(any,"the term",
    In(any,"its type",
    In(any,"the type expected by its context",
    Read("raise a fatal type inference error")))),
    (fun t ty ety ~depth:_ _ { assignments; state } ->
       raise (TypeError{assignments; state; t; ty; ety }))),
  DocNext);

  MLCode(Pred("eqtype-error",
    In(any,"the term",
    Read("raise a fatal equality type error")),
    (fun t ~depth:_ _ { assignments; state } ->
       raise (NotEqType{assignments; state; t}))),
  DocNext);

]

let _ =
  Format.printf "\n========= builtins ==========\n%!";
  BI.document Format.std_formatter extra_builtins
;;

(* w ********************************************************************* *)

let subtext text fmt ( { Lexing.pos_cnum = a } , { Lexing.pos_cnum = b } ) =
  let open String in
  Format.fprintf fmt "@[<v 2>  %s@;%s@]" text
  (make a ' ' ^ make (b-a) '^' ^ make (length text - b) ' ')

let pp_result text assignments state =
  M.iter (fun k v ->
     let loc = M.find k (CS.get rs_output state) in
     Format.printf "@[<v>The term:@ %a@ has type: %a@]@\n@\n"
       (subtext text) loc (Pp.term 0) v)
    assignments

let pp_type_err text t ty ety state =
  let loc = P.find_opt t (CS.get rs_positions state) in
  match loc with
  | Some loc ->
      Format.printf "@[<v>Type error:@ %a@ has type %a@ but is expected to have type %a@]@\n%!" (subtext text) loc (Pp.term 0) ty (Pp.term 0) ety
  | None ->
      Format.printf "@[<v>Type error:@ the term: %a@ has type %a@ but is expected to have type %a@]@\n%!" (Pp.term 0) t (Pp.term 0) ty (Pp.term 0) ety

let pp_eqtype_err text t state =
  let loc = P.find_opt t (CS.get rs_positions state) in
  match loc with
  | Some loc ->
      Format.printf "@[<v>Equality type constraint unsatisfied at:@ %a@]@\n%!" (subtext text) loc
  | None ->
      Format.printf "@[<v>Equality type constraint unsatisfied at:@ %a@]@\n%!"(Pp.term 0) t

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
  let header, _ = Setup.init ~builtins ~basedir:"./"
    (elpi_flags @ List.tl (Array.to_list Sys.argv)) in

  let p = Parse.program ["w.elpi"] in
  let p = Compile.program header [p] in

fun (text, ast) ->
  (* run w on a term *)
  let q = C.query p (fun ~depth:_ st ->
    let st, ty = mkQ st ~name_hint:"Q" ast.loc in
    let st, ast = embed st [] ast in
    st, E.mkApp (E.Constants.from_stringc "main") ast [ty]) in
  
  if Array.mem "-typecheck" Sys.argv then begin
    if not (Compile.static_check header q) then
      failwith "w.elpi does not type check";
  end;

  let exe = Compile.link q in

  Format.printf "\n============= W: %s ==============\n%!" text;
  match Execute.once exe with
  | Execute.Success s ->
      let { E.assignments; state } = E.of_solution s in
      pp_result text assignments state
  | Failure -> failwith "w.elpi is buggy"
  | NoMoreSteps -> assert false
  | exception TypeError{assignments; state; t; ty; ety } ->
      pp_result text assignments state;
      pp_type_err text t ty ety state
  | exception NotEqType{assignments; state; t } ->
      pp_result text assignments state;
      pp_eqtype_err text t state
;;

(* main ****************************************************************** *)

let parse s = s, Parser.main Lexer.token (Lexing.from_string s)

let _ =
  try
    while true; do
      w @@ parse @@ input_line stdin;
    done
  with End_of_file -> ()

(* vim:set foldmethod=marker: *)
