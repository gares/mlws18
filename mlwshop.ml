type uuid = string

type term =
 | Const of string
 | Var of int
 | App of term * term
 | Lam of term
 | Let of uuid * term * term
 | Eq of uuid * term * term

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
                                

module EA = Elpi_API
module E = EA.Extend.Data
module C = EA.Extend.Compile


let appc = E.Constants.from_stringc "app"
let lamc = E.Constants.from_stringc "lam"
let letc = E.Constants.from_stringc "let"
let eqc = E.Constants.from_stringc "eq"

let cs_uuid = EA.Extend.Compile.State.declare ~name:"uuid-map"
  ~init:(fun _ -> EA.Data.StrMap.empty)
  ~pp:(fun fmt m -> ())

let rec term2elpi st ctx = function
  | Var x -> st, E.mkConst (ctx - x - 1)
  | App(h,a) ->
     let st, h = term2elpi st ctx h in
     let st, a = term2elpi st ctx a in
     st, E.mkApp appc h [a]
  | Lam t ->
     let st, t = term2elpi st (succ ctx) t in
     st, E.mkApp lamc (E.mkLam t) []
  | Let(uuid, t, b) ->
     let st, name, ty = C.fresh_Arg st ~name_hint:uuid ~args:[] in
     let st = EA.Extend.Compile.State.update cs_uuid st (EA.Data.StrMap.add name uuid) in
     let st, t = term2elpi st ctx t in
     let st, b = term2elpi st (succ ctx) b in
     st, E.mkApp letc t [ty; E.mkLam b]
  | Const s -> st, E.Constants.from_string s
  | Eq(uuid, lhs, rhs) ->
     let st, name, f = C.fresh_Arg st ~name_hint:uuid ~args:[] in
     let st = EA.Extend.Compile.State.update cs_uuid st (EA.Data.StrMap.add name uuid) in
     let st, lhs = term2elpi st ctx lhs in
     let st, rhs = term2elpi st ctx rhs in
     st, E.mkApp eqc f [lhs;rhs]

let rs_uuid = EA.Extend.CustomConstraint.declare ~name:"uuid-map"
  ~init:(EA.Extend.CustomConstraint.CompilerState (cs_uuid,fun x -> x))
  ~pp:(fun fmt m -> ())

exception TypeError of EA.Extend.Data.term * EA.Extend.Data.term * EA.Extend.Data.term

let extra_builtins = let open EA.Extend.BuiltInPredicate in [
  MLCode(Pred("type-error",
    In(any,"T",
    In(any,"TY",
    In(any,"ETY",
    Easy("raises a type error: the term T has type TY but is expected to have type ETY")))),
    (fun t ty ety ~depth:_ -> raise (TypeError(t,ty,ety)))),
  DocNext)
]

let _ =
  Format.printf "\n========= builtins ==========\n%!";
  EA.Extend.BuiltInPredicate.document Format.std_formatter extra_builtins
;;

let w =
  let elpi_flags =
    try
      let ic, _ as p = Unix.open_process "elpi -where 2>/dev/null" in
      let w = input_line ic in
      let _ = Unix.close_process p in ["-I";w]
    with _ -> [] in
  let builtins = EA.Extend.BuiltInPredicate.builtin_of_declaration
    (Elpi_builtin.std_declarations @ extra_builtins) in
  let header, _ = EA.Setup.init ~builtins ~basedir:"./" elpi_flags in
  let p = EA.Parse.program ["w.elpi"] in
  let p = EA.Compile.program header [p] in
fun (text, ast) ->
  let q = C.query p (fun ~depth st ->
     let st, name, ty = C.fresh_Arg st ~name_hint:"?ty" ~args:[] in
     let st = EA.Extend.Compile.State.update cs_uuid st (EA.Data.StrMap.add name "?ty") in
    let st, ast = term2elpi st depth ast in
    st, E.mkApp (E.Constants.from_stringc "w") ast [ty]) in
  let exe = EA.Compile.link q in
  
  if not (EA.Compile.static_check header q) then
    failwith "w.elpi does not type check";

  Format.printf "\n========= W: %s ==========\n%!" text;
  match EA.Execute.once exe with
  | EA.Execute.Success { EA.Data.assignments; EA.Data.custom_constraints = state } ->
      EA.Data.StrMap.iter (fun k v ->
         Format.printf "%s := %a@\n" (EA.Data.StrMap.find k (EA.Extend.CustomConstraint.get rs_uuid state)) EA.Pp.term v)
        assignments
  | EA.Execute.Failure -> failwith "w.elpi is buggy"
  | EA.Execute.NoMoreSteps -> assert false
  | exception TypeError(t,ty,ety) ->
      Format.printf "Type error:@ the term %a@ has type %a@ but is expected to have type %a\n%!" (EA.Extend.Pp.term 0) t (EA.Extend.Pp.term 0) ty (EA.Extend.Pp.term 0) ety
;;

let _ = w example0
let _ = w example1
let _ = w example2
let _ = w example3
let _ = w example4
