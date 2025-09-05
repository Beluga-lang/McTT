From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Subtyping Require Import Definitions.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Completeness.Consequences Require Import Rules.
Import Syntax_Notations.

#[local]
Ltac apply_subtyping :=
  repeat match goal with
    | H : {{ ^?Γ ⊢ ^?M : ^?A }},
        H1 : {{ ^?Γ ⊢ ^?A ⊆ ^?B }} |- _ =>
        assert {{ Γ ⊢ M : B }} by mauto; clear H
    end.

Lemma alg_subtyping_nf_sound : forall A B,
    {{ ⊢anf A ⊆ B }} ->
    forall Γ i,
      {{ Γ ⊢ A : Type@i }} ->
      {{ Γ ⊢ B : Type@i }} ->
      {{ Γ ⊢ A ⊆ B }}.
Proof.
  induction 1; intros; subst; simpl in *.
  - eapply wf_subtyp_refl'; mauto.
  - assert (i < j \/ i = j) as [] by lia; mauto 3.
  - on_all_hyp: fun H => apply wf_pi_inversion in H; destruct H as [? ?].
    destruct_all.
    gen_presups.
    repeat match goal with
           | H : {{ ^?Γ ⊢ ^?A ⊆ ^?B }}, H1: {{ ⊢ ^?Γ , ^_ }} |- _ =>
               pose proof (wf_subtyp_univ_weaken _ _ _ _ H H1);
               fail_if_dup
           end.
    apply_subtyping.
    assert {{ Γ, ^(nf_to_exp A') ⊢ B : Type@(max x x0) }} by mauto using lift_exp_max_right.
    assert {{ Γ, ^(nf_to_exp A') ⊢ B' : Type@(max x x0) }} by mauto using lift_exp_max_left.
    deepexec IHalg_subtyping_nf ltac:(fun H => pose proof H).
    mauto 3.
  - on_all_hyp: fun H => apply wf_sigma_inversion in H; destruct H as [? ?].
    destruct_all.
    gen_presups.
    repeat match goal with
           | H : {{ ^?Γ ⊢ ^?A ⊆ ^?B }}, H1: {{ ⊢ ^?Γ , ^_ }} |- _ =>
               pose proof (wf_subtyp_univ_weaken _ _ _ _ H H1);
               fail_if_dup
           end.
    apply_subtyping.
    assert {{ Γ, ^(nf_to_exp A') ⊢ B : Type@(max x x0) }} by mauto using lift_exp_max_right.
    assert {{ Γ, ^(nf_to_exp A') ⊢ B' : Type@(max x x0) }} by mauto using lift_exp_max_left.
    deepexec IHalg_subtyping_nf ltac:(fun H => pose proof H).
    mauto 3.
Qed.

Lemma alg_subtyping_nf_trans : forall A0 A1 A2,
    {{ ⊢anf A0 ⊆ A1 }} ->
    {{ ⊢anf A1 ⊆ A2 }} ->
    {{ ⊢anf A0 ⊆ A2 }}.
Proof.
  intros * H1; gen A2.
  induction H1; subst; intros ? H2;
    dependent destruction H2;
    simpl in *;
    try contradiction;
    mauto 3.

  constructor; lia.
Qed.

Lemma alg_subtyping_nf_refl : forall A,
    {{ ⊢anf A ⊆ A }}.
Proof.
  induction A;
    solve [constructor; simpl; trivial].
Qed.

#[local]
Hint Resolve alg_subtyping_nf_trans alg_subtyping_nf_refl : mctt.

Lemma alg_subtyping_trans : forall Γ A0 A1 A2,
    {{ Γ ⊢a A0 ⊆ A1 }} ->
    {{ Γ ⊢a A1 ⊆ A2 }} ->
    {{ Γ ⊢a A0 ⊆ A2 }}.
Proof.
  intros. progressive_inversion.
  functional_nbe_rewrite_clear.
  mauto.
Qed.

#[local]
Hint Resolve alg_subtyping_trans : mctt.

Lemma alg_subtyping_complete : forall Γ A B,
    {{ Γ ⊢ A ⊆ B }} ->
    {{ Γ ⊢a A ⊆ B }}.
Proof.
  induction 1; mauto.
  - apply completeness in H0 as [W [? ?]].
    econstructor; mauto.
  - assert {{ Γ ⊢ Type@i : Type@(S i) }} by mauto.
    assert {{ Γ ⊢ Type@j : Type@(S j) }} by mauto.
    on_all_hyp: fun H => apply soundness in H.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    mauto.
  - assert {{ ⊢ Γ , A ≈ Γ , A' }} by mauto.
    eapply ctxeq_nbe_eq in H5; [ |eassumption].
    match goal with
    | H : _ |- _ => apply completeness in H
    end.
    assert {{ Γ ⊢ Π A B : Type@i }} as ?%soundness by mauto.
    assert {{ Γ ⊢ Π A' B' : Type@i }} as ?%soundness by mauto.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    functional_read_rewrite_clear.
    mauto 2.
  - assert {{ ⊢ Γ , A ≈ Γ , A' }} by mauto.
    eapply ctxeq_nbe_eq in H5; [ |eassumption].
    match goal with
    | H : _ |- _ => apply completeness in H
    end.
    assert {{ Γ ⊢ Σ A B : Type@i }} as ?%soundness by mauto.
    assert {{ Γ ⊢ Σ A' B' : Type@i }} as ?%soundness by mauto.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    functional_read_rewrite_clear.
    mauto 2.
Qed.

Lemma alg_subtyping_sound : forall Γ A B i,
    {{ Γ ⊢a A ⊆ B }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros. destruct H.
  on_all_hyp: fun H => apply soundness in H.
  destruct_all.
  on_all_hyp: fun H => apply nbe_type_to_nbe_ty in H.
  functional_nbe_rewrite_clear.
  gen_presups.
  assert {{ Γ ⊢ A' ⊆ B' }} by mauto 3 using alg_subtyping_nf_sound.
  transitivity A'; [mauto |].
  transitivity B'; [eassumption |].
  mauto.
Qed.
