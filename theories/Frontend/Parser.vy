%{

From Coq Require Import List Arith.PeanoNat String.

From Mctt Require Import Syntax.

Parameter loc : Type.

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE ZERO LET IN REFL AS (* keywords *)
%token <loc> ARROW "->" AT "@" BAR "|" COLON ":" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" DOT "." DEF ":=" EQ "=" LANGLE "<" RANGLE ">" EOF (* symbols *)

%start <Cst.obj * Cst.obj> prog
%type <Cst.obj> obj eq_obj app_obj atomic_obj
%type <string * Cst.obj> param
%type <list (string * Cst.obj)> params
%type <string -> Cst.obj -> Cst.obj -> Cst.obj> fnbinder
%type <(string * Cst.obj) * Cst.obj> let_defn
%type <list ((string * Cst.obj) * Cst.obj)> let_defns
%type <unit> optional_as_nat

%on_error_reduce obj params eq_obj app_obj atomic_obj

%%

let prog :=
  exp = obj; ":"; typ = obj; EOF; <>

let fnbinder :=
  | PI; { Cst.pi }
  | LAMBDA; { Cst.fn }

let obj :=
  | ~ = fnbinder; ~ = params; "->"; ~ = obj; { List.fold_left (fun acc arg => fnbinder (fst arg) (snd arg) acc) params obj }
  | ~ = eq_obj; <>

  | REC; escr = obj; optional_as_nat; RETURN; mx = VAR; "."; em = obj;
    "|"; ZERO; "=>"; ez = obj;
    "|"; SUCC; sx = VAR; ","; sr = VAR; "=>"; es = obj;
    END; { Cst.natrec escr (snd mx) em ez (snd sx) (snd sr) es }

  | REC; escr = obj; AS; "("; lhs = app_obj; "="; "<"; typ = obj; ">"; rhs = app_obj; ")"; RETURN; mx = VAR; my = VAR; mz = VAR; "."; em = obj;
    "|"; REFL; rx = VAR; "=>"; er = obj;
    END; { Cst.eqrec escr (snd mx) (snd my) (snd mz) em (snd rx) er lhs typ rhs }

  | REFL; typ = atomic_obj; e = atomic_obj; { Cst.refl typ e }

  | SUCC; ~ = atomic_obj; { Cst.succ atomic_obj }
  
  | LET; ds = let_defns; IN; body = obj; { List.fold_left (fun acc arg => Cst.app acc (snd arg)) (List.rev ds) (List.fold_left (fun acc arg => Cst.fn (fst (fst arg)) (snd (fst arg)) acc) ds body) }

let eq_obj :=
  | lhs = app_obj; "="; "<"; typ = obj; ">"; rhs = app_obj; { Cst.prop_eq lhs typ rhs }
  | ~ = app_obj; <>

let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { Cst.app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  | TYPE; "@"; n = INT; { Cst.typ (snd n) }

  | NAT; { Cst.nat }
  | ZERO; { Cst.zero }
  | n = INT; { nat_rect (fun _ => Cst.obj) Cst.zero (fun _ => Cst.succ) (snd n) }

  | x = VAR; { Cst.var (snd x) }

  | "("; ~ = obj; ")"; <>

(* Reversed nonempty list of parameters *)
let params :=
  | ~ = params; ~ = param; { param :: params }
  | ~ = param; { [param] }

(* (x : A) *)
let param :=
  | "("; x = VAR; ":"; ~ = obj; ")"; { (snd x, obj) }

(* Reversed nonempty list of definitions *)
let let_defns :=
  | ~ = let_defns; ~ = let_defn; { let_defn :: let_defns }
  | ~ = let_defn; { [let_defn] }

(* (x : A) := t *)
let let_defn :=
  | "("; ~ = param; ":="; ~ = obj; ")"; { (param, obj) }

let optional_as_nat :=
  | AS; NAT; { tt }
  | { tt }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
