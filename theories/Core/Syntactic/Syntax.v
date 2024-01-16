From Coq Require Import List.
From Coq Require Import String.

From Mcltt Require Import Base.

(* CST term *)
Module Cst.
Inductive obj : Set :=
| typ : nat -> obj
| nat : obj
| zero : obj
| succ : obj -> obj
| natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
| app : obj -> obj -> obj
| fn : string -> obj -> obj -> obj
| pi : string -> obj -> obj -> obj
| var : string -> obj.
End Cst.

(* AST term *)
Inductive exp : Set :=
(* Natural numbers *)
| a_zero : exp
| a_succ : exp -> exp
| a_natrec : exp -> exp -> exp -> exp -> exp
(* Type constructors *)
| a_nat : exp
| a_typ : nat -> exp
| a_var : nat -> exp
(* Functions *)
| a_fn : exp -> exp -> exp
| a_app : exp -> exp -> exp
| a_pi : exp -> exp -> exp
(* Substitutions *)
| a_sub : exp -> sub -> exp
with sub : Set :=
| a_id : sub
| a_weaken : sub
| a_compose : sub -> sub -> sub
| a_extend : sub -> exp -> sub.

Notation ctx := (list exp).
Notation typ := exp.

Fixpoint nat_to_exp n : exp :=
  match n with
  | 0 => a_zero
  | S m => a_succ (nat_to_exp m)
  end.
Definition num_to_exp n := nat_to_exp (Nat.of_num_uint n).

Fixpoint exp_to_nat e : option nat :=
  match e with
  | a_zero => Some 0
  | a_succ e' =>
      match exp_to_nat e' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.
Definition exp_to_num e :=
  match exp_to_nat e with
  | Some n => Some (Nat.to_num_uint n)
  | None => None
  end.

#[global] Bind Scope exp_scope with exp.
#[global] Bind Scope exp_scope with sub.
Open Scope exp_scope.

#[global] Declare Custom Entry exp.

Notation "{{{ x }}}" := x (at level 0, x custom exp at level 99, format "'{{{'  x  '}}}'") : exp_scope.
Notation "( x )" := x (in custom exp at level 0, x custom exp at level 60) : exp_scope.
Notation "~ x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "x" := x (in custom exp at level 0, x global) : exp_scope.
Notation "e [ s ]" := (a_sub e s) (in custom exp at level 0, s custom exp at level 60) : exp_scope.
Notation "'λ' A e" := (a_fn A e) (in custom exp at level 0, A custom exp at level 0, e custom exp at level 60) : exp_scope.
Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom exp at level 40, f custom exp, x custom exp at next level, y custom exp at next level) : exp_scope.
Notation "'ℕ'" := a_nat (in custom exp) : exp_scope.
Notation "'Type' @ n" := (a_typ n) (in custom exp at level 0, n constr at level 0) : exp_scope.
Notation "'Π' A B" := (a_pi A B) (in custom exp at level 0, A custom exp at level 0, B custom exp at level 60) : exp_scope.
Notation "'zero'" := a_zero (in custom exp at level 0) : exp_scope.
Notation "'succ' e" := (a_succ e) (in custom exp at level 0, e custom exp at level 0) : exp_scope.
Notation "'rec' e 'return' A | 'zero' -> ez | 'succ' -> es 'end'" := (a_natrec A ez es e) (in custom exp at level 0, A custom exp at level 60, ez custom exp at level 60, es custom exp at level 60, e custom exp at level 60) : exp_scope.
Notation "'#' n" := (a_var n) (in custom exp at level 0, n constr at level 0) : exp_scope.
Notation "'Id'" := a_id (in custom exp at level 0) : exp_scope.
Notation "'Wk'" := a_weaken (in custom exp at level 0) : exp_scope.

Infix "∘" := a_compose (in custom exp at level 40) : exp_scope.
Infix ",," := a_extend (in custom exp at level 50) : exp_scope.
Notation "'q' σ" := ({{{ σ ∘ Wk ,, # 0 }}}) (in custom exp at level 30) : exp_scope.

Notation "⋅" := nil (in custom exp at level 0) : exp_scope.
Notation "x , y" := (cons y x) (in custom exp at level 50) : exp_scope.

Inductive nf : Set :=
| nf_typ : nat -> nf
| nf_nat : nf
| nf_zero : nf
| nf_succ : nf -> nf
| nf_pi : nf -> nf -> nf
| nf_fn : nf -> nf -> nf
| nf_neut : ne -> nf
with ne : Set :=
| ne_natrec : nf -> nf -> nf -> ne -> ne
| ne_app : ne -> nf -> ne
| ne_var : nat -> ne
.

#[global] Declare Custom Entry nf.

#[global] Bind Scope exp_scope with nf.
#[global] Bind Scope exp_scope with ne.

Notation "n{{{ x }}}" := x (at level 0, x custom nf at level 99, format "'n{{{'  x  '}}}'") : exp_scope.
Notation "( x )" := x (in custom nf at level 0, x custom nf at level 60) : exp_scope.
Notation "~ x" := x (in custom nf at level 0, x constr at level 0) : exp_scope.
Notation "x" := x (in custom nf at level 0, x global) : exp_scope.
Notation "'λ' A e" := (nf_fn A e) (in custom nf at level 0, A custom nf at level 0, e custom nf at level 60) : exp_scope.
Notation "f x .. y" := (ne_app .. (ne_app f x) .. y) (in custom nf at level 40, f custom nf, x custom nf at next level, y custom nf at next level) : exp_scope.
Notation "'ℕ'" := nf_nat (in custom nf) : exp_scope.
Notation "'Type' @ n" := (nf_typ n) (in custom nf at level 0, n constr at level 0) : exp_scope.
Notation "'Π' A B" := (nf_pi A B) (in custom nf at level 0, A custom nf at level 0, B custom nf at level 60) : exp_scope.
Notation "'zero'" := nf_zero (in custom nf at level 0) : exp_scope.
Notation "'succ' M" := (nf_succ M) (in custom nf at level 0, M custom nf at level 0) : exp_scope.
Notation "'rec' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (ne_natrec A MZ MS M) (in custom nf at level 0, A custom nf at level 60, MZ custom nf at level 60, MS custom nf at level 60, M custom nf at level 60) : exp_scope.
Notation "'#' n" := (ne_var n) (in custom nf at level 0, n constr at level 0) : exp_scope.
Notation "'⇑' M" := (nf_neut M) (in custom nf at level 0, M custom nf at level 0) : exp_scope.

Fixpoint nf_to_exp (M : nf) : exp :=
  match M with
  | nf_typ i => a_typ i
  | nf_nat => a_nat
  | nf_zero => a_zero
  | nf_succ M => a_succ (nf_to_exp M)
  | nf_pi A B => a_pi (nf_to_exp A) (nf_to_exp B)
  | nf_fn A M => a_fn (nf_to_exp A) (nf_to_exp M)
  | nf_neut M => ne_to_exp M
  end
with ne_to_exp (M : ne) : exp :=
  match M with
  | ne_natrec A MZ MS M => a_natrec (nf_to_exp A) (nf_to_exp MZ) (nf_to_exp MS) (ne_to_exp M)
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_var x => a_var x
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.
