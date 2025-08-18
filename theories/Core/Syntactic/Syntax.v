From Coq Require Import List String.

From Mctt.Core Require Import Base.

(** * Concrete Syntax Tree *)
Module Cst.
Inductive obj : Set :=
| typ : nat -> obj
| nat : obj
| zero : obj
| succ : obj -> obj
| natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
| pi : string -> obj -> obj -> obj
| fn : string -> obj -> obj -> obj
| app : obj -> obj -> obj
| sigma : string -> obj -> obj -> obj
| pair : obj -> obj -> obj
| fst : obj -> obj
| snd : obj -> obj
| prop_eq : obj -> obj -> obj -> obj
| refl : obj -> obj -> obj
| eqrec : obj ->                 (** A : eq domain type *)
          string -> string -> string -> obj -> (** x y (z : Eq A x y). M *)
          string -> obj ->                   (** x. Pf : M[x/x, x/y, refl A x/z] *)
          obj -> obj -> obj -> obj
| var : string -> obj.
End Cst.

(** * Abstract Syntac Tree *)
Inductive exp : Set :=
(** Universe *)
| a_typ : nat -> exp
(** Natural numbers *)
| a_nat : exp
| a_zero : exp
| a_succ : exp -> exp
| a_natrec : exp -> exp -> exp -> exp -> exp
(** Functions *)
| a_pi : exp -> exp -> exp
| a_fn : exp -> exp -> exp
| a_app : exp -> exp -> exp
(** Pairs *)
| a_sigma : exp -> exp -> exp
| a_pair : exp -> exp -> exp
| a_fst : exp -> exp
| a_snd : exp -> exp
(** Propositional equality *)
| a_eq : exp -> exp -> exp -> exp
| a_refl : exp -> exp -> exp
| a_eqrec : exp -> exp -> exp -> exp -> exp -> exp -> exp
(** Variable *)
| a_var : nat -> exp
(** Substitution Application *)
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

(** ** Syntactic Normal/Neutral Form *)
Inductive nf : Set :=
| nf_typ : nat -> nf
| nf_nat : nf
| nf_zero : nf
| nf_succ : nf -> nf
| nf_pi : nf -> nf -> nf
| nf_fn : nf -> nf -> nf
| nf_sigma : nf -> nf -> nf
| nf_pair : nf -> nf -> nf
| nf_eq : nf -> nf -> nf -> nf
| nf_refl : nf -> nf -> nf
| nf_neut : ne -> nf
with ne : Set :=
| ne_natrec : nf -> nf -> nf -> ne -> ne
| ne_app : ne -> nf -> ne
| ne_fst : ne -> ne
| ne_snd : ne -> ne
| ne_var : nat -> ne
| ne_eqrec : nf -> nf -> nf -> nf -> nf -> ne -> ne
.

Fixpoint nf_to_exp (M : nf) : exp :=
  match M with
  | nf_typ i => a_typ i
  | nf_nat => a_nat
  | nf_zero => a_zero
  | nf_succ M => a_succ (nf_to_exp M)
  | nf_pi A B => a_pi (nf_to_exp A) (nf_to_exp B)
  | nf_fn A M => a_fn (nf_to_exp A) (nf_to_exp M)
  | nf_sigma A B => a_sigma (nf_to_exp A) (nf_to_exp B)
  | nf_pair M N => a_pair (nf_to_exp M) (nf_to_exp N)
  | nf_eq A M N => a_eq (nf_to_exp A) (nf_to_exp M) (nf_to_exp N)
  | nf_refl A M => a_refl (nf_to_exp A) (nf_to_exp M)
  | nf_neut M => ne_to_exp M
  end
with ne_to_exp (M : ne) : exp :=
  match M with
  | ne_natrec A MZ MS M => a_natrec (nf_to_exp A) (nf_to_exp MZ) (nf_to_exp MS) (ne_to_exp M)
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_fst M => a_fst (ne_to_exp M)
  | ne_snd M => a_snd (ne_to_exp M)
  | ne_var x => a_var x
  | ne_eqrec A B BR M M' N =>
      a_eqrec (nf_to_exp A) (nf_to_exp B) (nf_to_exp BR) (nf_to_exp M) (nf_to_exp M') (ne_to_exp N)
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

Fact nf_eq_dec : forall (M M' : nf),
    ({M = M'} + {M <> M'})%type
with ne_eq_dec : forall (M M' : ne),
    ({M = M'} + {M <> M'})%type.
Proof.
  all: intros; decide equality;
    apply PeanoNat.Nat.eq_dec.
Defined.

Definition q σ := a_extend (a_compose σ a_weaken) (a_var 0).
Arguments q σ/.


#[global] Declare Custom Entry exp.
#[global] Declare Custom Entry nf.

#[global] Bind Scope mctt_scope with exp.
#[global] Bind Scope mctt_scope with sub.
#[global] Bind Scope mctt_scope with nf.
#[global] Bind Scope mctt_scope with ne.
Open Scope mctt_scope.

(** ** Syntactic Notations *)
Module Syntax_Notations.
  (** We need to define substitution notation first to assert [left associativity] of level 0. *)
  Notation "e [ s ]" := (a_sub e s) (in custom exp at level 0, e custom exp, s custom exp at level 60, left associativity, format "e [ s ]") : mctt_scope.

  Notation "{{{ x }}}" := x (at level 0, x custom exp at level 99, format "'{{{'  x  '}}}'") : mctt_scope.
  Notation "( x )" := x (in custom exp at level 0, x custom exp at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom exp at level 0, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom exp at level 0, x ident) : mctt_scope.

  Notation "'Type' @ n" := (a_typ n) (in custom exp at level 0, n constr at level 0, format "'Type' @ n") : mctt_scope.
  Notation "'ℕ'" := a_nat (in custom exp) : mctt_scope.
  Notation "'zero'" := a_zero (in custom exp at level 0) : mctt_scope.
  Notation "'succ' e" := (a_succ e) (in custom exp at level 1, e custom exp at level 0) : mctt_scope.
  Notation "'rec' e 'return' A | 'zero' -> ez | 'succ' -> es 'end'" := (a_natrec A ez es e) (in custom exp at level 0, A custom exp at level 60, ez custom exp at level 60, es custom exp at level 60, e custom exp at level 60) : mctt_scope.
  Notation "'Π' A B" := (a_pi A B) (in custom exp at level 1, A custom exp at level 0, B custom exp at level 60) : mctt_scope.
  Notation "'λ' A e" := (a_fn A e) (in custom exp at level 1, A custom exp at level 0, e custom exp at level 60) : mctt_scope.
  Notation "'Σ' A B" := (a_sigma A B) (in custom exp at level 1, A custom exp at level 0, B custom exp at level 60) : mctt_scope.
  Notation "⟨ M ; N ⟩" := (a_pair M N) (in custom exp at level 1, M custom exp at next level, N custom exp at next level) : mctt_scope.
  Notation "'fst' M" := (a_fst M) (in custom exp at level 1, M custom exp at level 0) : mctt_scope.
  Notation "'snd' M" := (a_snd M) (in custom exp at level 1, M custom exp at level 0) : mctt_scope.
  Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom exp at level 40, f custom exp, x custom exp at next level, y custom exp at next level) : mctt_scope.
  Notation "'Eq' A M N" := (a_eq A M N) (in custom exp at level 1, A custom exp at level 30, M custom exp at level 35, N custom exp at level 40) : mctt_scope.
  Notation "'refl' A M" := (a_refl A M) (in custom exp at level 1, A custom exp at level 30, M custom exp at level 40) : mctt_scope.
  Notation "'eqrec' N 'as' 'Eq' A M1 M2 'return' B | 'refl' -> BR 'end'" := (a_eqrec A B BR M1 M2 N) (in custom exp at level 0, A custom exp at level 30, B custom exp at level 60, BR custom exp at level 60, M1 custom exp at level 35, M2 custom exp at level 40, N custom exp at level 60) : mctt_scope.

  Notation "'#' n" := (a_var n) (in custom exp at level 0, n constr at level 0, format "'#' n") : mctt_scope.

  Notation "'Id'" := a_id (in custom exp at level 0) : mctt_scope.
  Notation "'Wk'" := a_weaken (in custom exp at level 0) : mctt_scope.
  Notation "σ ∘ τ" := (a_compose σ τ) (in custom exp at level 40, right associativity, format "σ ∘ τ") : mctt_scope.
  Notation "σ ,, e" := (a_extend σ e) (in custom exp at level 50, left associativity, format "σ ,, e") : mctt_scope.
  Notation "'q' σ" := (q σ) (in custom exp at level 30) : mctt_scope.

  Notation "⋅" := nil (in custom exp at level 0) : mctt_scope.
  Notation "x , y" := (cons y x) (in custom exp at level 50, left associativity, format "x ,  y") : mctt_scope.

  Notation "n{{{ x }}}" := x (at level 0, x custom nf at level 99, format "'n{{{'  x  '}}}'") : mctt_scope.
  Notation "( x )" := x (in custom nf at level 0, x custom nf at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom nf at level 0, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom nf at level 0, x ident) : mctt_scope.

  Notation "'Type' @ n" := (nf_typ n) (in custom nf at level 0, n constr at level 0, format "'Type' @ n") : mctt_scope.
  Notation "'ℕ'" := nf_nat (in custom nf) : mctt_scope.
  Notation "'zero'" := nf_zero (in custom nf at level 0) : mctt_scope.
  Notation "'succ' M" := (nf_succ M) (in custom nf at level 2, M custom nf at level 1) : mctt_scope.
  Notation "'rec' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (ne_natrec A MZ MS M) (in custom nf at level 0, A custom nf at level 60, MZ custom nf at level 60, MS custom nf at level 60, M custom nf at level 60) : mctt_scope.
  Notation "'Π' A B" := (nf_pi A B) (in custom nf at level 2, A custom nf at level 1, B custom nf at level 60) : mctt_scope.
  Notation "'λ' A e" := (nf_fn A e) (in custom nf at level 2, A custom nf at level 1, e custom nf at level 60) : mctt_scope.
  Notation "'Σ' A B" := (nf_sigma A B) (in custom nf at level 2, A custom nf at level 1, B custom nf at level 60) : mctt_scope.
  Notation "⟨ M ; N ⟩" := (nf_pair M N) (in custom nf at level 2, M custom nf at level 1, N custom nf at level 60) : mctt_scope.
  Notation "f x .. y" := (ne_app .. (ne_app f x) .. y) (in custom nf at level 40, f custom nf, x custom nf at next level, y custom nf at next level) : mctt_scope.
  Notation "'fst' M" := (ne_fst M) (in custom nf at level 2, M custom nf at level 1) : mctt_scope.
  Notation "'snd' M" := (ne_snd M) (in custom nf at level 2, M custom nf at level 1) : mctt_scope.
  Notation "'Eq' A M N" := (nf_eq A M N) (in custom nf at level 1, A custom nf at level 30, M custom nf at level 35, N custom nf at level 40) : mctt_scope.
  Notation "'refl' A M" := (nf_refl A M) (in custom nf at level 1, A custom nf at level 30, M custom nf at level 40) : mctt_scope.
  Notation "'eqrec' N 'as' 'Eq' A M1 M2 'return' B | 'refl' -> BR 'end'" := (ne_eqrec A B BR M1 M2 N) (in custom nf at level 0, A custom nf at level 30, B custom nf at level 60, BR custom nf at level 60, M1 custom nf at level 35, M2 custom nf at level 40, N custom nf at level 60) : mctt_scope.

  Notation "'#' n" := (ne_var n) (in custom nf at level 0, n constr at level 0, format "'#' n") : mctt_scope.
  Notation "'⇑' M" := (nf_neut M) (in custom nf at level 0, M custom nf at level 99, format "'⇑'  M") : mctt_scope.
End Syntax_Notations.
