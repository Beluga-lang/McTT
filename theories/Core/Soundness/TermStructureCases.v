From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma presup_glu_rel_exp : forall {Γ M A},
    {{ Γ ⊩ M : A }} ->
    {{ ⊩ Γ }} /\ (exists i, {{ Γ ⊩ A : Type@i }}).
Proof.
  intros * [? [? []]].
  split; [eexists; eassumption |].
  do 2 eexists; intuition.
  eexists; mauto 4.
Qed.

Lemma presup_ctx_glu_rel_exp : forall {Γ M A},
    {{ Γ ⊩ M : A }} ->
    {{ ⊩ Γ }}.
Proof.
  intros * []%presup_glu_rel_exp.
  eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mctt.

Lemma presup_typ_glu_rel_exp : forall {Γ M A},
    {{ Γ ⊩ M : A }} ->
    exists i, {{ Γ ⊩ A : Type@i }}.
Proof.
  intros * []%presup_glu_rel_exp.
  eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp : mctt.

Lemma glu_rel_exp_vlookup : forall {Γ x A},
    {{ ⊩ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊩ #x : A }}.
Proof.
  intros * [Sb] Hx. gen Sb.
  induction Hx; intros;
    match_by_head1 glu_ctx_env ltac:(fun H => invert_glu_ctx_env H).
  - eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists.
    intros.
    destruct_by_head cons_glu_sub_pred.
    econstructor; mauto.
  - assert {{ Γ ⊩ #n : A }} as Hn by mauto.
    assert (exists i, {{ Γ ⊢ A : Type@i }}) as [j] by (gen_presups; mauto 3).
    invert_glu_rel_exp Hn.
    rename i0 into k.
    eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists (max j k).
    intros.
    destruct_by_head cons_glu_sub_pred.
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    rename a into b.
    rename a0 into a.
    assert {{ Dom a ≈ a ∈ per_univ k }} as [] by mauto.
    eapply mk_glu_rel_exp_with_sub''; intuition mauto using per_univ_elem_cumu_max_right.
    assert {{ ⊢ Γ, B }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Type@j }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Type@(max j k) }} as -> by mauto 3 using lift_exp_eq_max_left.
    assert {{ Γ ⊢ #n : A }} by mauto 4.
    assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 3.
    assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
    assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv; mauto 3).
    assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 3.
    eapply glu_univ_elem_exp_cumu_max_right; revgoals; mautosolve 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mctt.

Lemma glu_rel_exp_sub : forall {Γ σ Δ M A},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ M : A }} ->
    {{ Γ ⊩ M[σ] : A[σ] }}.
Proof.
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  assert (exists i, {{ Δ ⊩ A : Type@i }}) as [i] by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  invert_glu_rel_exp HM.
  assert {{ Δ ⊢ A : Type@i }} by mauto 3.
  eexists; split; mauto.
  eexists.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  destruct_glu_rel_exp_with_sub.
  assert {{ Dom a ≈ a ∈ per_univ i }} as [] by mauto.
  econstructor; mauto.
  assert {{ Δ' ⊢s τ : Γ }} by mauto 3.
  assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }} as -> by mauto 3.
  assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} as ->; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub : mctt.
