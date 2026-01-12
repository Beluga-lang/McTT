From Mctt.Core.Syntactic.System Require Export Definitions Lemmas Tactics.

From Coq Require Import List Classes.RelationClasses Setoid Morphisms.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
Import Syntax_Notations.

Lemma weakening_lookup : forall Γ Γ' A x,
    {{ # x : A ∈ Γ }} ->
    {{ ⊢ Γ' }} ->
    {{ # x : A ∈ ^(Γ ++ Γ') }}.
Proof.
  induction 1; intros.
  - econstructor.
  - econstructor; mauto 3.
Qed.

#[local]
Hint Resolve weakening_lookup : mctt.

Ltac simplify_ihs Γ' :=
  repeat match goal with
  | H: forall {G' : ctx}, {{ ⊢ ^?G }} -> ?H' |- _ =>
      pose proof (H Γ' ltac:(mauto 3));
      fail_if_dup
  end.

Lemma weakening_gen :
  (forall Γ, {{ ⊢ Γ }} -> (forall Γ', {{ ⊢ Γ' }} -> {{ ⊢ ^(Γ ++ Γ') }}))
  /\ (forall Γ Γ', {{ ⊢ Γ ⊆ Γ' }} -> (forall Γ'', {{ ⊢ Γ'' }} -> {{ ⊢ ^(Γ ++ Γ'') ⊆ ^(Γ' ++ Γ'') }}))
  /\ (forall Γ A M, {{ Γ ⊢ M : A }} -> (forall Γ', {{ ⊢ Γ' }} -> {{ ^(Γ ++ Γ') ⊢ M : A }}))
  /\ (forall Γ A M M', {{ Γ ⊢ M ≈ M' : A }} -> (forall Γ', {{ ⊢ Γ' }} -> {{ ^(Γ ++ Γ') ⊢ M ≈ M' : A }}))
  /\ (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> (forall Γ', {{ ⊢ Γ' }} -> {{ ^(Γ ++ Γ') ⊢s σ : ^(Δ ++ Γ') }}))
  /\ (forall Γ Δ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> (forall Γ', {{ ⊢ Γ' }} -> {{ ^(Γ ++ Γ') ⊢s σ ≈ σ' : ^(Δ ++ Γ') }}))
  /\ (forall Γ A A', {{ Γ ⊢ A ⊆ A' }} -> (forall Γ', {{ ⊢ Γ' }} -> {{ ^(Γ ++ Γ') ⊢ A ⊆ A' }})).
Proof.
  apply syntactic_wf_mut_ind; intros; simpl; simplify_ihs Γ'; mauto 3.
  - simplify_ihs Γ''; mauto 3.
  - simplify_ihs Γ'0; mauto 3.
  - simplify_ihs Γ'0; mauto 3.
  - simplify_ihs Γ'0; mauto 3.
  - simplify_ihs Γ'0; mauto 3.
  - simplify_ihs Γ'0; mauto 3.
Qed.

Lemma weakening : forall Γ Γ' A M,
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ' }} ->
    {{ ^(Γ ++ Γ') ⊢ M : A }}.
Proof.
  intros.
  gen Γ' M A Γ.
  eapply weakening_gen.
Qed.
