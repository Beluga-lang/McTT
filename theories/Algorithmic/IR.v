From Mctt.Core.Syntactic Require Import Syntax.

(** * Intermediate Representation (IR) *)

(** Note that IR does not have substitution application.
    It is not needed as we never directly NbE on IR.
    (NbE is always done on Core syntax).
 *)
Inductive ir : Set :=
(** Universe *)
| ir_typ : nat -> ir
(** Natural numbers *)
| ir_nat : ir
| ir_zero : ir
| ir_succ : ir -> ir
| ir_natrec : ir -> ir -> ir -> ir -> ir
(** Functions *)
| ir_pi : ir -> ir -> ir
| ir_fn : ir -> ir -> ir
| ir_app : ir -> ir -> ir
(** Propositional equality *)
| ir_eq : ir -> ir -> ir -> ir
| ir_refl : ir -> ir -> ir
| ir_eqrec : ir -> ir -> ir -> ir -> ir -> ir -> ir
(** Variable *)
| ir_var : nat -> ir
(** Annotation *)
| ir_ann : ir -> ir -> ir.

#[global] Declare Custom Entry ir.
#[global] Bind Scope mctt_scope with ir.

(** ** IR Notations *)
Module IR_Notations.
  Notation "i{{{ x }}}" := x (at level 0, x custom ir at level 99, format "'i{{{'  x  '}}}'") : mctt_scope.
  Notation "( x )" := x (in custom ir at level 0, x custom ir at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom ir at level 0, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom ir at level 0, x ident) : mctt_scope.

  Notation "'Type' @ n" := (ir_typ n) (in custom ir at level 0, n constr at level 0, format "'Type' @ n") : mctt_scope.
  Notation "'ℕ'" := ir_nat (in custom ir) : mctt_scope.
  Notation "'zero'" := ir_zero (in custom ir at level 0) : mctt_scope.
  Notation "'succ' e" := (ir_succ e) (in custom ir at level 1, e custom ir at level 0) : mctt_scope.
  Notation "'rec' e 'return' A | 'zero' -> ez | 'succ' -> es 'end'" := (ir_natrec A ez es e) (in custom ir at level 0, A custom ir at level 60, ez custom ir at level 60, es custom ir at level 60, e custom ir at level 60) : mctt_scope.
  Notation "'Π' A B" := (ir_pi A B) (in custom ir at level 1, A custom ir at level 0, B custom ir at level 60) : mctt_scope.
  Notation "'λ' A e" := (ir_fn A e) (in custom ir at level 1, A custom ir at level 0, e custom ir at level 60) : mctt_scope.
  Notation "f x .. y" := (ir_app .. (ir_app f x) .. y) (in custom ir at level 40, f custom ir, x custom ir at next level, y custom ir at next level) : mctt_scope.
  Notation "'Eq' A M N" := (ir_eq A M N) (in custom ir at level 1, A custom ir at level 30, M custom ir at level 35, N custom ir at level 40) : mctt_scope.
  Notation "'refl' A M" := (ir_refl A M) (in custom ir at level 1, A custom ir at level 30, M custom ir at level 40) : mctt_scope.
  Notation "'eqrec' N 'as' 'Eq' A M1 M2 'return' B | 'refl' -> BR 'end'" := (ir_eqrec A B BR M1 M2 N) (in custom ir at level 0, A custom ir at level 30, B custom ir at level 60, BR custom ir at level 60, M1 custom ir at level 35, M2 custom ir at level 40, N custom ir at level 60) : mctt_scope.

  Notation "'#' n" := (ir_var n) (in custom ir at level 0, n constr at level 0, format "'#' n") : mctt_scope.
  Notation "M : A" := (ir_ann A M) (in custom ir at level 60, M custom ir, A custom ir at level 0) : mctt_scope.
End IR_Notations.

Import Syntax_Notations.
Import IR_Notations.

(** ** Erasure *)
Fixpoint ir_to_exp m : exp :=
  match m with
  | i{{{ Type@i }}} => {{{ Type@i }}}
  | i{{{ ℕ }}} => {{{ ℕ }}}
  | i{{{ zero }}} => {{{ zero }}}
  | i{{{ succ m }}} => {{{ succ ^(ir_to_exp m) }}}
  | i{{{ rec n return a | zero -> mz | succ -> ms end }}} => {{{ rec ^(ir_to_exp n) return ^(ir_to_exp a) | zero -> ^(ir_to_exp mz) | succ -> ^(ir_to_exp ms) end }}}
  | i{{{ Π a b }}} => {{{ Π ^(ir_to_exp a) ^(ir_to_exp b) }}}
  | i{{{ λ a m }}} => {{{ λ ^(ir_to_exp a) ^(ir_to_exp m) }}}
  | i{{{ m n }}} => {{{ ^(ir_to_exp m) ^(ir_to_exp n) }}}
  | i{{{ Eq a m0 m1 }}} => {{{ Eq ^(ir_to_exp a) ^(ir_to_exp m0) ^(ir_to_exp m1) }}}
  | i{{{ refl a m }}} => {{{ refl ^(ir_to_exp a) ^(ir_to_exp m) }}}
  | i{{{ eqrec n as Eq a m1 m2 return b | refl -> r end }}} => {{{ eqrec ^(ir_to_exp n) as Eq ^(ir_to_exp a) ^(ir_to_exp m1) ^(ir_to_exp m2) return ^(ir_to_exp b) | refl -> ^(ir_to_exp r) end }}}

  | i{{{ # x }}} => {{{ # x }}}
  | i{{{ m : a }}} => ir_to_exp m
  end.
