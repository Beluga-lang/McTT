From Coq Require Import Morphisms_Relations RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import LogicalRelation FunctionCases PairCases.
Import Domain_Notations.

Lemma subtyp_refl : forall Γ M M' i,
    {{ Γ ⊨ M ≈ M' : Type@i }} ->
    {{ Γ ⊨ M ⊆ M' }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_subtyp.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  do 2 eexists.
  repeat split; econstructor; mauto 3;
    etransitivity; try eassumption; symmetry; eassumption.
Qed.

Lemma subtyp_trans : forall Γ M M' M'',
    {{ Γ ⊨ M ⊆ M' }} ->
    {{ Γ ⊨ M' ⊆ M'' }} ->
    {{ Γ ⊨ M ⊆ M'' }}.
Proof.
  intros * [env_relΓ [? [i]]] [? [? [j]]].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_subtyp_with (max i j).
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  do 2 eexists.
  repeat split; econstructor;
    eauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
  etransitivity;
    eauto using per_subtyp_cumu_left, per_subtyp_cumu_right.
Qed.

#[export]
Instance subtyp_Transitive Γ : Transitive (subtyp_under_ctx Γ).
Proof. eauto using subtyp_trans. Qed.

Lemma subtyp_univ : forall Γ i j,
    {{ ⊨ Γ }} ->
    i < j ->
    {{ Γ ⊨ Type@i ⊆ Type@j }}.
Proof.
  intros * [env_relΓ] ?.
  eexists_subtyp.
  intros.
  assert (i < S (max i j)) by lia.
  assert (j < S (max i j)) by lia.
  do 2 eexists.
  repeat split; econstructor;
    try apply per_univ_elem_core_univ'; try reflexivity;
    mauto 3.
  econstructor; lia.
Qed.

Lemma subtyp_pi : forall Γ A A' B B' i,
  {{ Γ ⊨ A ≈ A' : Type@i }} ->
  {{ Γ , A' ⊨ B ⊆ B' }} ->
  {{ Γ ⊨ Π A B ⊆ Π A' B' }}.
Proof.
  intros * [env_relΓ] [? [? [k]]].
  destruct_conjs.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΓ ?x |- _ =>
      rename x into head_relA'
  end.
  handle_per_ctx_env_irrel.
  eexists_subtyp.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  match goal with
  | _: env_relΓ ρ ?ρ0 |- _ =>
      assert_fails (unify ρ ρ0);
      rename ρ0 into ρ'
  end.

  assert (forall c c', head_relA' ρ ρ' equiv_ρ_ρ' c c' -> cons_per_ctx_env env_relΓ head_relA' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as HΓA'
      by (intros; unshelve econstructor; eassumption).

  (** The proofs for the next two assertions are basically the same *)
  exvar (relation domain)
    ltac:(fun R => assert ({{ DF Π m0 ρ B ≈ Π m1 ρ' B ∈ per_univ_elem (Nat.max i k) ↘ R }})).
  {
    intros.
    per_univ_elem_econstructor; [| | solve_refl].
    - etransitivity; [| symmetry]; mauto using per_univ_elem_cumu_max_left.
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_relA' }} as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
      destruct_conjs.
      destruct_by_head rel_typ.
      econstructor; mauto using per_univ_elem_cumu_max_right.
  }
  exvar (relation domain)
    ltac:(fun R => assert ({{ DF Π a0 ρ B' ≈ Π a ρ' B' ∈ per_univ_elem (Nat.max i k) ↘ R }})).
  {
    intros.
    per_univ_elem_econstructor; [| | solve_refl].
    - etransitivity; [symmetry |]; mauto using per_univ_elem_cumu_max_left.
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_relA' }} as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
      simpl in *.
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
      destruct_conjs.
      destruct_by_head rel_mod_eval.
      econstructor; mauto using per_univ_elem_cumu_max_right.
  }

  do 2 eexists.
  repeat split; econstructor; mauto 2.
  econstructor; only 3-4: try (saturate_refl; mautosolve 2).
  - eauto using per_univ_elem_cumu_max_left.
  - intros.
    assert (cons_per_ctx_env env_relΓ head_relA' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
    simpl in *.
    (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
    destruct_conjs.
    destruct_by_head rel_exp.
    simplify_evals.
    mauto 2 using per_subtyp_cumu_right.
Qed.

Lemma subtyp_sigma : forall Γ A A' B B' i,
  {{ Γ ⊨ A ≈ A' : Type@i }} ->
  {{ Γ , A' ⊨ B ⊆ B' }} ->
  {{ Γ ⊨ Σ A B ⊆ Σ A' B' }}.
Proof.
  intros * [env_relΓ] [? [? [k]]].
  destruct_conjs.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΓ ?x |- _ =>
      rename x into head_relA'
  end.
  handle_per_ctx_env_irrel.
  eexists_subtyp.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  match goal with
  | _: env_relΓ ρ ?ρ0 |- _ =>
      assert_fails (unify ρ ρ0);
      rename ρ0 into ρ'
  end.

  assert (forall c c', head_relA' ρ ρ' equiv_ρ_ρ' c c' -> cons_per_ctx_env env_relΓ head_relA' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as HΓA'
      by (intros; unshelve econstructor; eassumption).

  (** The proofs for the next two assertions are basically the same *)
  exvar (relation domain)
    ltac:(fun R => assert ({{ DF Σ m0 ρ B ≈ Σ m1 ρ' B ∈ per_univ_elem (Nat.max i k) ↘ R }})).
  {
    intros.
    per_univ_elem_econstructor; [| | solve_refl].
    - etransitivity; [| symmetry]; mauto using per_univ_elem_cumu_max_left.
    - admit.
  }
  exvar (relation domain)
    ltac:(fun R => assert ({{ DF Σ a0 ρ B' ≈ Σ a ρ' B' ∈ per_univ_elem (Nat.max i k) ↘ R }})).
  {
    intros.
    per_univ_elem_econstructor; [| | solve_refl].
    - etransitivity; [symmetry |]; mauto using per_univ_elem_cumu_max_left.
    - admit.
  }

  do 2 eexists.
  repeat split; econstructor; mauto 2.
  econstructor; only 3-4: try (saturate_refl; mautosolve 2).
  - eauto using per_univ_elem_cumu_max_left.
  - intros.
    assert (cons_per_ctx_env env_relΓ head_relA' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
    simpl in *.
    (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
    destruct_conjs.
    destruct_by_head rel_exp.
    simplify_evals.
    mauto 2 using per_subtyp_cumu_right.
Admitted.

#[export]
Hint Resolve subtyp_refl subtyp_trans subtyp_univ subtyp_pi subtyp_sigma : mctt.
