From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations.


Lemma glu_rel_eq : forall Γ A i M N,
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ Eq A M N : Type@i }}.
Proof.
  intros * HA HM HN.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  saturate_syn_judge.
  invert_sem_judge.

  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  split; mauto 3.
  apply_glu_rel_judge.
  saturate_glu_typ_from_el.
  unify_glu_univ_lvl i.
  deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => destruct H).
  do 2 deepexec glu_univ_elem_per_elem ltac:(fun H => pose proof H; fail_at_if_dup ltac:(4)).

  eexists; repeat split; mauto.
  - eexists. per_univ_elem_econstructor; mauto. reflexivity.
  - intros.
    match_by_head1 glu_univ_elem invert_glu_univ_elem.
    handle_per_univ_elem_irrel.
    handle_functional_glu_univ_elem.
    econstructor; mauto 3;
      intros Δ' τ **;
      assert {{ Δ' ⊢s τ : Δ }} by mauto 2;
      assert {{ Δ' ⊢s σ ∘ τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption);
      assert {{ Δ' ⊢s σ ∘ τ : Γ }} by mauto 2;
      apply_glu_rel_judge;
      handle_functional_glu_univ_elem;
      unify_glu_univ_lvl i.
    + bulky_rewrite.
    + assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ ∘ τ] : A[σ ∘ τ] }} by mauto.
      bulky_rewrite.
    + assert {{ Δ' ⊢ N[σ][τ] ≈ N[σ ∘ τ] : A[σ ∘ τ] }} by mauto.
      bulky_rewrite.
Qed.

#[export]
  Hint Resolve glu_rel_eq : mctt.

Lemma glu_rel_eq_refl : forall Γ A M,
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ refl A M : Eq A M M }}.
Proof.
  intros * HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  saturate_syn_judge.
  invert_sem_judge.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  eexists; split; eauto.
  exists i; intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  apply_glu_rel_judge.
  saturate_glu_typ_from_el.
  deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => unfold per_univ in H; deex_once_in H).
  deepexec glu_univ_elem_per_elem ltac:(fun H => pose proof H; fail_at_if_dup ltac:(4)).
  saturate_glu_info.
  eexists; repeat split; mauto.
  - glu_univ_elem_econstructor; mauto 3; reflexivity.
  - do 2 try econstructor; mauto 3;
    intros Δ' τ **;
      assert {{ Δ' ⊢s τ : Δ }} by mauto 2;
    assert {{ Δ' ⊢s σ ∘ τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption);
    assert {{ Δ' ⊢s σ ∘ τ : Γ }} by mauto 2;
    assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ ∘ τ] : A[σ ∘ τ] }} by mauto;
    apply_glu_rel_judge;
    saturate_glu_typ_from_el;
    bulky_rewrite.
Qed.

#[export]
  Hint Resolve glu_rel_eq_refl : mctt.


Lemma glu_rel_eq_eqrec : forall Γ A i M1 M2 B j BR N,
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M1 : A }} ->
    {{ Γ ⊩ M2 : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊩ B : Type@j }} ->
    {{ Γ, A ⊩ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊩ N : Eq A M1 M2 }} ->
    {{ Γ ⊩ eqrec N as Eq A M1 M2 return B | refl -> BR end : B[Id,,M1,,M2,,N] }}.
Proof.
  intros * HA HM1 HM2 HB HBR HN.
Admitted.

#[export]
  Hint Resolve glu_rel_eq_eqrec : mctt.
