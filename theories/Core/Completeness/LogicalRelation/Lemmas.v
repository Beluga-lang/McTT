From Coq Require Import Morphisms Morphisms_Relations RelationClasses Relation_Definitions.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions Tactics.
Import Domain_Notations.

Add Parametric Morphism M ρ M' ρ' : (rel_exp M ρ M' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism σ ρ σ' ρ' : (rel_sub σ ρ σ' ρ')
    with signature (@relation_equivalence env) ==> iff as rel_sub_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Lemma rel_exp_implies_rel_typ : forall {i A ρ A' ρ'},
    rel_exp A ρ A' ρ' (per_univ i) ->
    exists R, rel_typ i A ρ A' ρ' R.
Proof.
  intros.
  destruct_by_head rel_exp.
  destruct_by_head per_univ.
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_implies_rel_typ : mctt.

Lemma rel_typ_implies_rel_exp : forall {i A ρ A' ρ' R},
    rel_typ i A ρ A' ρ' R ->
    rel_exp A ρ A' ρ' (per_univ i).
Proof.
  intros.
  destruct_by_head rel_typ.
  mauto.
Qed.

#[export]
Hint Resolve rel_typ_implies_rel_exp : mctt.

Lemma rel_exp_clean_inversion_left : forall {Γ Γ' env_relΓ A M M'},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    exists i,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
    exists (elem_rel : relation domain),
      rel_typ i A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  eassumption.
Qed.

Lemma rel_exp_clean_inversion_right : forall {Γ Γ' env_relΓ A M M'},
    {{ EF Γ' ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    exists i,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
    exists (elem_rel : relation domain),
      rel_typ i A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  eassumption.
Qed.

Ltac invert_rel_exp_clean H :=
  let H' := fresh "H" in 
  (unshelve (epose proof (rel_exp_clean_inversion_left _ H) as H'; deex_in H'); shelve_unifiable; [eassumption |]; clear H)
  + (unshelve (epose proof (rel_exp_clean_inversion_right _ H) as H'; deex_in H'); shelve_unifiable; [eassumption |]; clear H).

Tactic Notation "invert_rel_exp" hyp(H) :=
  invert_rel_exp_clean H
  + (simpl in H; unfold rel_exp_under_ctx in H; deex_in H; destruct H as [? H]; deex_in H).

Tactic Notation "invert_rel_exp" hyp(H) simple_intropattern(l) :=
  invert_rel_exp_clean H
  + (destruct H as [l [? H]]; deex_in H).

Lemma rel_sub_clean_inversion1_left : forall {Γ Γ' env_relΓ σ σ' Δ},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    exists env_relΔ,
      {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub σ ρ σ' ρ' env_relΔ).
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion1_right : forall {Γ Γ' env_relΓ σ σ' Δ},
    {{ EF Γ' ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    exists env_relΔ,
      {{ EF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub σ ρ σ' ρ' env_relΔ).
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion2_left : forall {Γ σ σ' Δ Δ' env_relΔ},
    {{ EF Δ ≈ Δ' ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    exists env_relΓ,
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub σ ρ σ' ρ' env_relΔ).
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion2_right : forall {Γ σ σ' Δ Δ' env_relΔ},
    {{ EF Δ' ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    exists env_relΓ,
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub σ ρ σ' ρ' env_relΔ).
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_left_left : forall {Γ Γ' env_relΓ σ σ' Δ Δ' env_relΔ},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Δ ≈ Δ' ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
      rel_sub σ ρ σ' ρ' env_relΔ.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_left HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_left_right : forall {Γ Γ' env_relΓ σ σ' Δ Δ' env_relΔ},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Δ' ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
      rel_sub σ ρ σ' ρ' env_relΔ.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_left HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_right_left : forall {Γ Γ' env_relΓ σ σ' Δ Δ' env_relΔ},
    {{ EF Γ' ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Δ ≈ Δ' ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
      rel_sub σ ρ σ' ρ' env_relΔ.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_right HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_right_right : forall {Γ Γ' env_relΓ σ σ' Δ Δ' env_relΔ},
    {{ EF Γ' ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Δ' ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
      rel_sub σ ρ σ' ρ' env_relΔ.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_right HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Ltac invert_rel_sub_clean H :=
  let H' := fresh "H" in 
  (unshelve (epose proof (rel_sub_clean_inversion3_left_left _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion3_left_right _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion3_right_left _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion3_right_right _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion2_left _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion2_right _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion1_left _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion1_right _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H).

Tactic Notation "invert_rel_sub" hyp(H) :=
  invert_rel_sub_clean H
  + (simpl in H; unfold rel_sub_under_ctx in H; do 2 (deex_in H; destruct H as [? H])).

Tactic Notation "invert_rel_sub" hyp(H) simple_intropattern(l) :=
  invert_rel_sub_clean H
  + (destruct H as [l [? H]]; deex_in H; destruct H as []).
