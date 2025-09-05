From Coq Require Import RelationClasses.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Completeness.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma ctxeq_nbe_eq : forall Γ Γ' M A,
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    exists W, nbe Γ M A W /\ nbe Γ' M A W.
Proof.
  intros * [envR [Henv [i]]]%completeness_fundamental_exp [envR' Henv']%completeness_fundamental_ctx_eq.
  handle_per_ctx_env_irrel.
  destruct (per_ctx_then_per_env_initial_env Henv') as [p [p' [? []]]].
  deepexec H ltac:(fun H => destruct H as [R [? ?]]).
  progressive_inversion.
  deepexec @per_elem_then_per_top ltac:(fun H => destruct H as [W []]).
  exists W.
  split; econstructor; eauto.
  erewrite per_ctx_respects_length; try eassumption.
  eexists. symmetry.
  eassumption.
Qed.

Corollary ctxeq_nbe_eq' : forall Γ Γ' M A W,
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    nbe Γ M A W ->
    nbe Γ' M A W.
Proof.
  intros.
  assert (exists W, nbe Γ M A W /\ nbe Γ' M A W) as [? []] by mauto 3 using ctxeq_nbe_eq.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Corollary ctxeq_nbe_ty_eq : forall Γ Γ' A i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    exists W, nbe_ty Γ A W /\ nbe_ty Γ' A W.
Proof.
  intros.
  assert (exists W, nbe Γ A {{{ Type@i }}} W /\ nbe Γ' A {{{ Type@i }}} W) as [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]] by mauto 3 using ctxeq_nbe_eq.
  firstorder.
Qed.

Corollary ctxeq_nbe_ty_eq' : forall Γ Γ' A i W,
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    nbe_ty Γ A W ->
    nbe_ty Γ' A W.
Proof.
  intros.
  assert (exists W, nbe_ty Γ A W /\ nbe_ty Γ' A W) as [? []] by mauto 3 using ctxeq_nbe_ty_eq.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.
