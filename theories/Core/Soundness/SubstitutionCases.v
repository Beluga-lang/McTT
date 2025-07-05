From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation SubtypingCases TermStructureCases UniverseCases.
Import Domain_Notations.

Lemma presup_glu_rel_sub : forall {Γ σ Δ},
    {{ Γ ⊩s σ : Δ }} ->
    {{ ⊩ Γ }} /\ {{ ⊩ Δ }}.
Proof.
  intros * [].
  destruct_conjs.
  split; eexists; eassumption.
Qed.

Lemma presup_left_glu_rel_sub : forall {Γ σ Δ},
    {{ Γ ⊩s σ : Δ }} ->
    {{ ⊩ Γ }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_left_glu_rel_sub : mctt.

Lemma presup_right_glu_rel_sub : forall {Γ σ Δ},
    {{ Γ ⊩s σ : Δ }} ->
    {{ ⊩ Δ }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_right_glu_rel_sub : mctt.

Lemma glu_rel_sub_id : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩s Id : Γ }}.
Proof.
  intros * [Sb].
  do 2 eexists; repeat split; mauto.
  intros.
  econstructor; mauto.
  enough {{ Δ ⊢s σ ≈ Id∘σ : Γ }} as <-; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_id : mctt.

Lemma glu_rel_sub_weaken : forall {Γ A},
    {{ ⊩ Γ, A }} ->
    {{ Γ, A ⊩s Wk : Γ }}.
Proof.
  intros * [SbΓA].
  match_by_head1 glu_ctx_env invert_glu_ctx_env.
  handle_functional_glu_ctx_env.
  do 2 eexists; repeat split; [econstructor | |]; try reflexivity; mauto.
  intros.
  destruct_by_head cons_glu_sub_pred.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_weaken : mctt.

Lemma glu_rel_sub_compose : forall {Γ1 σ2 Γ2 σ1 Γ3},
    {{ Γ1 ⊩s σ2 : Γ2 }} ->
    {{ Γ2 ⊩s σ1 : Γ3 }} ->
    {{ Γ1 ⊩s σ1 ∘ σ2 : Γ3 }}.
Proof.
  intros * Hσ2 Hσ1.
  assert {{ Γ2 ⊢s σ1 : Γ3 }} by mauto.
  assert {{ Γ1 ⊢s σ2 : Γ2 }} by mauto.
  destruct Hσ2 as [SbΓ1 [SbΓ2]].
  destruct_conjs.
  invert_glu_rel_sub Hσ1.
  do 2 eexists; repeat split; mauto.
  intros.
  destruct_glu_rel_sub_with_sub.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env.
  econstructor; mauto.
  enough {{ Δ ⊢s (σ1 ∘ σ2) ∘ σ ≈ σ1 ∘ (σ2 ∘ σ) : Γ3 }} as -> by eassumption.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_compose : mctt.

Lemma glu_rel_sub_extend : forall {Γ σ Δ M A i},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A[σ] }} ->
    {{ Γ ⊩s (σ ,, M) : Δ , A }}.
Proof.
  intros * Hσ HA HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ A : Type@i }} by mauto 3.
  assert {{ Γ ⊢ M : A[σ] }} by mauto 3.
  assert {{ Γ ⊩ Type@i : Type@(S i) }} by mauto 3.
  assert {{ Γ ⊢ Type@i[σ] ⊆ Type@i }} by mauto 3.
  assert {{ Γ ⊩ A[σ] : Type@i }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  assert {{ Δ ⊩ Type@i : Type@(S i) }} by mauto 3.
  destruct_conjs.
  invert_glu_rel_exp HA.
  invert_glu_rel_exp HM.
  do 2 eexists; repeat split; mauto.
  - econstructor; mauto 3; try reflexivity.
  - intros.
    destruct_glu_rel_sub_with_sub_nouip.
    destruct_glu_rel_exp_with_sub_nouip.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    rename m0 into a.
    assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 4.
    econstructor; mauto 3.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 ≈ (σ∘σ0),,M[σ0] : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ Wk∘((σ∘σ0),,M[σ0]) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ][σ0] }} by mauto 3.
    assert {{ Δ0 ⊢ M[σ0] : A[σ∘σ0] }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ∘σ0),,M[σ0]) ≈ σ∘σ0 : Δ }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} by mauto 3.
    econstructor; mauto 4.
    + assert {{ Δ, A ⊢s Wk : Δ }} by mauto 4.
      assert {{ Δ0 ⊢ A[Wk][(σ,,M)∘σ0] ≈ A[Wk][(σ∘σ0),,M[σ0]] : Type@i }} as -> by mauto 3.
      assert {{ Δ0 ⊢ A[Wk][(σ∘σ0),,M[σ0]] ≈ A[σ∘σ0] : Type@i }} as -> by mauto 3.
      assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Type@i }} as -> by mauto 3.
      assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[Wk][(σ,,M)∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[σ][σ0] }} as -> by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ∘σ0] }} by mauto.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ][σ0] }} as -> by (eapply wf_exp_eq_conv; mauto 3).
      mautosolve 3.
    + enough {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} as ->; eassumption.
Qed.

#[export]
Hint Resolve glu_rel_sub_extend : mctt.
