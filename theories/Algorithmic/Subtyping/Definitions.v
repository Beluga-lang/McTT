From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Reserved Notation "Γ ⊢a A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "⊢anf A ⊆ A'" (in custom judg at level 80, A custom nf, A' custom nf).

Definition not_univ_pi_sigma (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_pi _ _ | nf_sigma _ _ => False
  | _ => True
  end.

Inductive alg_subtyping_nf : nf -> nf -> Prop :=
| asnf_refl : forall A A',
    not_univ_pi_sigma A ->
    A = A' ->
    {{ ⊢anf A ⊆ A' }}
| asnf_univ : forall i j,
    i <= j ->
    {{ ⊢anf Type@i ⊆ Type@j }}
| asnf_pi : forall A B A' B',
    A = A' ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Π A B ⊆ Π A' B' }}
| asnf_sigma : forall A B A' B',
    A = A' ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Σ A B ⊆ Σ A' B' }}
where "⊢anf A ⊆ A'" := (alg_subtyping_nf A A') (in custom judg) : type_scope.

Inductive alg_subtyping : ctx -> typ -> typ -> Prop :=
| alg_subtyp_run : forall Γ A B A' B',
    nbe_ty Γ A A' ->
    nbe_ty Γ B B' ->
    {{ ⊢anf A' ⊆ B' }} ->
    {{ Γ ⊢a A ⊆ B }}
where "Γ ⊢a A ⊆ B" := (alg_subtyping Γ A B) (in custom judg) : type_scope.

#[export]
Hint Constructors alg_subtyping_nf alg_subtyping: mctt.
