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

Lemma glu_rel_exp_nat : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ ℕ : Type@i }}.
Proof.
  intros * [Sb].
  assert {{ ⊢ Γ }} by mauto.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 3.
  eexists; repeat split; mauto 3.
  - eexists; per_univ_elem_econstructor; reflexivity.
  - intros.
    match_by_head1 glu_univ_elem invert_glu_univ_elem_nouip.
    apply_predicate_equivalence.
    unfold nat_glu_typ_pred.
    mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_nat : mctt.

Lemma glu_rel_exp_sub_nat : forall {Γ σ Δ M},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ M : ℕ }} ->
    {{ Γ ⊩ M[σ] : ℕ }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] ⊆ ℕ }} by mautosolve 3.
  assert {{ Γ ⊩ M[σ] : ℕ[σ] }} by mauto 3.
  mautosolve 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_nat : mctt.

Lemma glu_rel_exp_clean_inversion2'' : forall {Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊩ M : ℕ }} ->
    glu_rel_exp_resp_sub_env 0 Sb M {{{ ℕ }}}.
Proof.
  intros * ? HM.
  assert {{ Γ ⊩ ℕ : Type@0 }} by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

Ltac invert_glu_rel_exp H ::=
  (unshelve eapply (glu_rel_exp_clean_inversion2'' _) in H; shelve_unifiable; [eassumption |];
   unfold glu_rel_exp_resp_sub_env in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2' _) in H; shelve_unifiable; [eassumption |];
     unfold glu_rel_exp_resp_sub_env in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
     unfold glu_rel_exp_resp_sub_env in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

Lemma glu_rel_exp_of_nat : forall {Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ Sb }} -> exists m, {{ ⟦ M ⟧ ρ ↘ m }} /\ glu_nat Δ {{{ M[σ] }}} m) ->
    {{ Γ ⊩ M : ℕ }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto 3.
  exists 0.
  intros.
  edestruct Hbody as [? []]; mauto 3.
  econstructor; mauto 3.
  - glu_univ_elem_econstructor; mauto 3; reflexivity.
  - simpl; split; mauto 3.
Qed.

Lemma glu_rel_exp_zero : forall {Γ},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ zero : ℕ }}.
Proof.
  intros * [Sb].
  eapply glu_rel_exp_of_nat; mauto 3.
  intros.
  eexists; split; mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mctt.

Lemma glu_rel_exp_succ : forall {Γ M},
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ succ M : ℕ }}.
Proof.
  intros * HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊢ M : ℕ }} by mauto 3.
  invert_glu_rel_exp HM.
  eapply glu_rel_exp_of_nat; mauto.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head1 glu_univ_elem invert_glu_univ_elem_nouip.
  apply_predicate_equivalence.
  inversion_clear_by_head nat_glu_exp_pred.
  eexists; split; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_succ : mctt.

Lemma glu_rel_sub_extend_nat : forall {Γ σ Δ M},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩s σ,,M : Δ, ℕ }}.
Proof.
  intros.
  assert {{ ⊩ Δ }} by mauto 2.
  assert {{ Γ ⊩ ℕ[σ] : Type@0 }} by mauto 3.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mautosolve 4.
  assert {{ Γ ⊩ M : ℕ[σ] }}; mautosolve 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_extend_nat : mctt.

Lemma glu_rel_exp_natrec_zero_helper : forall {i Γ SbΓ A MZ MS Δ M σ ρ am P El},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊩ A[Id,,zero] : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M ≈ zero : ℕ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ zero ↘ am }} ->
    {{ DG am ∈ glu_univ_elem i ↘ P ↘ El }} ->
    exists r,
      {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? ? ? HMZ **.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
  invert_glu_rel_exp HMZ.
  assert {{ Γ ⊩ ℕ : Type@0 }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred 0 Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  rename m into mz.
  eexists mz; split; mauto 3.
  handle_functional_glu_univ_elem.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢s Id : Δ }} by mauto 2.
  assert {{ Δ ⊢s σ,,M ≈ σ,,zero : Γ, ℕ }} as -> by mauto 3.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk : Δ, ℕ }} by mauto 2.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Type@i }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Type@i }} by (symmetry; mauto 4).
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Type@i }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Type@i }} as <- by mauto 2.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by bulky_rewrite.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by mauto 4.
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by (rewrite @exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1; mauto 3).
  pose (R := {{{ rec zero return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert
    {{ Δ ⊢ R ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,zero] }} as <-
      by (econstructor; try eapply exp_eq_refl; mauto 3).
  assert
    {{ Δ ⊢ R ≈ MZ[σ] : A[q σ][Id,,zero] }} as ->
      by (econstructor; mauto 3).
  bulky_rewrite.
Qed.

Lemma cons_glu_sub_pred_nat_helper : forall {Γ SbΓ Δ σ ρ i M m},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    glu_nat Δ M m ->
    {{ Δ ⊢s σ,,M ® ρ ↦ m ∈ cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ }}.
Proof.
  intros * ? HM ?.
  assert {{ DG ℕ ∈ glu_univ_elem i ↘ nat_glu_typ_pred i ↘ nat_glu_exp_pred i }} by (glu_univ_elem_econstructor; reflexivity).
  eapply cons_glu_sub_pred_helper; mauto 3.
  econstructor; [unfold nat_glu_typ_pred |]; mauto 3.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_nat_helper : mctt.

Lemma glu_rel_exp_natrec_succ_helper : forall {i Γ SbΓ A MZ MS Δ M M' m' σ ρ am P El},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Γ, ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊩ A[Wk∘Wk,,succ #1] : Type@i }} ->
    {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M ≈ succ M' : ℕ }} ->
    glu_nat Δ M' m' ->
    (forall σ ρ am P El,
        {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m' ↘ am }} ->
        {{ DG am ∈ glu_univ_elem i ↘ P ↘ El }} ->
        exists r,
          {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
            {{ Δ ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M'] ® r ∈ El }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ succ m' ↘ am }} ->
    {{ DG am ∈ glu_univ_elem i ↘ P ↘ El }} ->
    exists r,
      {{ rec succ m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? HA ? ? HMS **.
  assert {{ ⊩ Γ }} by (eexists; eassumption).
  assert {{ Γ ⊩ ℕ : Type@0 }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred 0 Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 2.
  invert_glu_rel_exp HA.
  pose (SbΓℕA := cons_glu_sub_pred i {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp HMS.
  assert {{ Δ ⊢s σ,,M' ® ρ ↦ m' ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  match goal with
  | _: {{ ⟦ A ⟧ ρ ↦ m' ↘ ^?m }}, _: {{ DG ^?m ∈ glu_univ_elem i ↘ ?P ↘ ?El }} |- _ =>
      rename m into am';
      rename P into P';
      rename El into El'
  end.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  assert {{ Δ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 2.
  assert {{ Δ ⊢ M' : ℕ }} by mauto 3.
  assert {{ Δ ⊢ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ ⊢ M' : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Type@i }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Type@i }} by (symmetry; mauto 4).
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Type@i }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by bulky_rewrite.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by (rewrite @exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1; mauto 3).
  pose (R := {{{ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert (exists r, {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\ {{ Δ ⊢ R : A[σ,,M'] ® r ∈ El' }}) as [r' []] by mauto 3.
  assert {{ Δ ⊢ R : A[σ,,M'] }} by (erewrite <- @exp_eq_elim_sub_rhs_typ; mauto 3).
  assert {{ Δ ⊢s σ,,M',,R ® ρ ↦ m' ↦ r' ∈ SbΓℕA }} by (unfold SbΓℕA; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  clear_dups.
  unfold univ_glu_exp_pred' in *.
  destruct_all.
  handle_functional_glu_univ_elem.
  match goal with
  | _: {{ ⟦ MS ⟧ ρ ↦ m' ↦ r' ↘ ^?m }} |- _ =>
      rename m into ms
  end.
  exists ms; split; mauto 3.
  assert {{ Δ ⊢s σ,,M ≈ σ,,succ M' : Γ, ℕ }} as -> by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ }} by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] : Type@i }} as -> by mauto 3.
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,succ M'] }} as <- by (econstructor; mauto 3).
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[q (q σ)][Id,,M',,R] : A[q σ][Id,,succ M'] }} as -> by mauto 2.
  assert {{ Δ ⊢ R : A[q σ][Id,,M'] }} by bulky_rewrite.
  assert {{ Δ ⊢s Id,,M',,R : Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] : Type@i }} as <- by mauto 3.
  assert {{ Δ ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,,succ M'] : Type@i }} as <- by mauto 3.
  assert {{ Δ ⊢ MS[q (q σ)][Id,,M',,R] ≈ MS[σ,,M',,R] : A[Wk∘Wk,,succ #1][σ,,M',,R] }} as -> by mauto 4.
  eassumption.
Qed.

Lemma cons_glu_sub_pred_q_helper : forall {Γ SbΓ Δ σ ρ i A a},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ Γ ⊩ A : Type@i }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ Δ, A[σ] ⊢s q σ ® ρ ↦ ⇑! a (length Δ) ∈ cons_glu_sub_pred i Γ A SbΓ }}.
Proof.
  intros * ? ? HA ?.
  assert {{ Γ ⊢ A : Type@i }} by mauto 2.
  invert_glu_rel_exp HA.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ ⊢ Δ, A[σ] }} by mauto 3.
  assert {{ Δ, A[σ] ⊢w Wk : Δ }} by mauto 2.
  eapply cons_glu_sub_pred_helper; mauto 2.
  - eapply glu_ctx_env_sub_monotone; eassumption.
  - assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 2.
    assert {{ Δ, A[σ] ⊢ A[σ∘Wk] ≈ A[σ][Wk] : Type@i }} as -> by mauto 3.
    eapply var0_glu_elem; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_helper : mctt.

Lemma cons_glu_sub_pred_q_nat_helper : forall {Γ SbΓ Δ σ ρ i},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ Δ, ℕ ⊢s q σ ® ρ ↦ ⇑! ℕ (length Δ) ∈ cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ }}.
Proof.
  intros.
  assert {{ ⊩ Γ }} by (eexists; eassumption).
  assert {{ Γ ⊩ ℕ : Type@i }} as Hℕ by mauto 3.
  assert {{ ⟦ ℕ ⟧ ρ ↘ ℕ }} by mauto 3.
  assert {{ Δ, ℕ[σ] ⊢s q σ ® ρ ↦ ⇑! ℕ (length Δ) ∈ cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Type@i }} by mauto 4.
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ }}
    by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  assert {{ ⊢ Δ }} by mauto 2.
  cbn.
  assert {{ ⊢ Δ, ℕ[σ] ≈ Δ, ℕ }} as <- by mauto 3.
  eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_nat_helper : mctt.

Lemma glu_rel_exp_natrec_neut_helper : forall {i Γ SbΓ A MZ MS Δ M a m σ ρ am P El},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Γ, ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ A[Id,,zero] : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊩ A[Wk∘Wk,,succ #1] : Type@i }} ->
    {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Δ' τ V, {{ Δ' ⊢w τ : Δ }} -> {{ Rne m in length Δ' ↘ V }} -> {{ Δ' ⊢ M[τ] ≈ V : ℕ }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ ⇑ a m ↘ am }} ->
    {{ DG am ∈ glu_univ_elem i ↘ P ↘ El }} ->
    exists r,
      {{ rec ⇑ a m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? HA ? HMZ ? HMS **.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 2.
  invert_glu_rel_exp HMZ.
  assert {{ ⊩ Γ }} by (eexists; eassumption).
  assert {{ Γ ⊩ ℕ : Type@0 }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred 0 Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 2.
  pose proof HA.
  invert_glu_rel_exp HA.
  pose (SbΓℕA := cons_glu_sub_pred i {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Δ ⊢s σ,,M ® ρ ↦ ⇑ a m ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp HMS.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  match goal with
  | _: {{ ⟦ MZ ⟧ ^?ρ0 ↘ ^?m }}, _: {{ ⟦ A ⟧ ^?ρ0 ↦ zero ↘ ^?a }} |- _ =>
      rename ρ0 into ρ;
      rename m into mz;
      rename a into az
  end.
  eexists; split; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 2.
  assert {{ Δ ⊢ M : ℕ }} by mautosolve 3.
  assert {{ Δ ⊢ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ ⊢ M : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Type@i }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Type@i }} by (symmetry; mauto 4).
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Type@i }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by bulky_rewrite.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by (rewrite @exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1; mauto 3).
  pose (R := {{{ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  enough {{ Δ ⊢ R : A[σ,,M] ® rec m under ρ return A | zero -> mz | succ -> MS end ∈ glu_elem_bot i am }} by (eapply realize_glu_elem_bot; mauto 3).
  econstructor; mauto 3.
  - erewrite <- @exp_eq_elim_sub_rhs_typ; mauto 3.
  - assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top i az }} as [] by (eapply realize_glu_elem_top; eassumption).
    handle_functional_glu_univ_elem.
    assert {{ ⊨ Γ }} as [env_relΓ] by mauto 3 using completeness_fundamental_ctx.
    assert {{ Γ, ℕ ⊨ A : Type@i }} as [env_relΓℕ] by mauto 3 using completeness_fundamental_exp.
    assert {{ Γ, ℕ, A ⊨ MS : A[Wk∘Wk,,succ #1] }} as [env_relΓℕA] by mauto 3 using completeness_fundamental_exp.
    destruct_conjs.
    pose env_relΓℕA.
    match_by_head (per_ctx_env env_relΓℕA) ltac:(fun H => invert_per_ctx_env H).
    match_by_head (per_ctx_env env_relΓℕ) ltac:(fun H => invert_per_ctx_env H).
    intros s.
    enough (exists r, {{ Rne rec m under ρ return A | zero -> mz | succ -> MS end in s ↘ r }}) as [] by (eexists; split; eassumption).
    assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    destruct_rel_typ.
    invert_rel_typ_body_nouip.
    assert {{ Dom ! s ≈ ! s ∈ per_bot }} by mauto 3.
    assert {{ Dom ρ ↦ ⇑! ℕ s ≈ ρ ↦ ⇑! ℕ s ∈ env_relΓℕ }} by (apply_relation_equivalence; unshelve eexists; simpl; intuition).
    assert {{ Dom ρ ↦ succ ⇑! ℕ s ≈ ρ ↦ succ ⇑! ℕ s ∈ env_relΓℕ }} by (apply_relation_equivalence; unshelve eexists; simpl; intuition).
    destruct_rel_typ.
    invert_rel_typ_body_nouip.
    match goal with
    | _: {{ ⟦ A ⟧ ρ ↦ ⇑! ℕ s ↘ ^?a }}, _: {{ ⟦ A ⟧ ρ ↦ (succ ⇑! ℕ s) ↘ ^?a' }} |- _ =>
        rename a into as'; (** We cannot use [as] as a name *)
        rename a' into asucc
    end.
    assert {{ Dom ρ ↦ ⇑! ℕ s ↦ ⇑! as' (S s) ≈ ρ ↦ ⇑! ℕ s ↦ ⇑! as' (S s) ∈ env_relΓℕA }} as HΓℕA
        by (apply_relation_equivalence; unshelve eexists; simpl; intuition; eapply per_bot_then_per_elem; mauto 3).
    apply_relation_equivalence.
    (on_all_hyp_rev: fun H => destruct (H _ _ HΓℕA)).
    destruct_conjs.
    destruct_by_head rel_typ.
    invert_rel_typ_body_nouip.
    destruct_by_head rel_exp.
    functional_eval_rewrite_clear.
    match goal with
    | _: {{ ⟦ MS ⟧ ρ ↦ ⇑! ℕ s ↦ ⇑! as' (S s) ↘ ^?m }} |- _ =>
        rename m into ms
    end.
    assert {{ Dom as' ≈ as' ∈ per_top_typ }} as [? []]%(fun {a} (f : per_top_typ a a) => f (S s)) by mauto 3.
    assert {{ Dom ⇓ asucc ms ≈ ⇓ asucc ms ∈ per_top }} as [? []]%(fun {a} (f : per_top a a) => f (S (S s))) by mauto 3.
    match_by_head1 (per_top d{{{ ⇓ az mz }}} d{{{ ⇓ az mz }}}) ltac:(fun H => destruct (H s) as [? []]).
    match_by_head1 (per_bot m m) ltac:(fun H => destruct (H s) as [? []]).
    eexists.
    mauto.
  - intros Δ' τ w **.
    assert {{ ⊢ Δ' }} by mauto 3.
    assert {{ ⊢ Δ', ℕ }} by mauto 3.
    assert {{ Δ' ⊢s τ : Δ }} by mauto 3.
    assert {{ Δ' ⊢s σ∘τ : Γ }} by mauto 3.
    assert {{ Δ' ⊢s σ∘τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption).
    clear_glu_ctx Δ.
    assert {{ Δ', ℕ ⊢s q (σ∘τ) ® ρ ↦ ⇑! ℕ (length Δ') ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    match_by_head read_ne ltac:(fun H => directed inversion_clear H).
    handle_functional_glu_univ_elem.
    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ ⇑! ℕ (length Δ') ↘ ^?a }} |- _ =>
        rename ρ' into ρ;
        rename a into aΔ'
    end.
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) ® ρ ↦ ⇑! ℕ (length Δ') ↦ ⇑! aΔ' (length {{{ Δ', ℕ }}}) ∈ SbΓℕA }}
      by (unfold SbΓℕA; mauto 3).
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    clear_dups.
    handle_functional_glu_univ_elem.
    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ succ (⇑! ℕ (length Δ')) ↘ ^?a }},
        _: {{ Rtyp aΔ' in S (length Δ') ↘ ^?A }},
        _: {{ Rnf ⇓ az mz in length Δ' ↘ ^?MZ }},
            _: {{ Rne m in length Δ' ↘ ^?M }} |- _ =>
        rename A into A';
        rename ρ' into ρ;
        rename a into asucc;
        rename MZ into MZ';
        rename M into M'
    end.
    assert {{ Δ', ℕ ⊢ A[q (σ∘τ)] ® glu_typ_top i aΔ' }} as [] by (eapply realize_glu_typ_top; eassumption).
    assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top i az }} as [] by (eapply realize_glu_elem_top; eassumption).
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] ® ms ∈ glu_elem_top i asucc }} as []
        by (eapply realize_glu_elem_top; eassumption).
    assert {{ Δ ⊢s σ,,M : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢s σ∘τ,,M[τ] : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢ A[σ,,M][τ] ≈ A[(σ,,M)∘τ] : Type@i }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[(σ,,M)∘τ] ≈ A[σ∘τ,,M[τ]] : Type@i }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[σ∘τ,,M[τ]] ≈ A[q σ][τ,,M[τ]] : Type@i }} as -> by (eapply sub_decompose_q_typ; mauto 2).
    assert {{ Δ' ⊢ R[τ] ≈ rec M[τ] return A[q σ][q τ] | zero -> MZ[σ][τ] | succ -> MS[q (q σ)][q (q τ)] end : A[q σ][τ,,M[τ]] }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[q σ][q τ][Id,,M[τ]] ≈ A[q σ][τ,,M[τ]] : Type@i }} as <- by mauto 3.
    assert {{ Δ', ℕ ⊢w Id : Δ', ℕ }} by mauto 3.
    eapply wf_exp_eq_natrec_cong'; fold ne_to_exp nf_to_exp; [| | | mautosolve 3].
    + assert {{ Δ', ℕ ⊢s q σ∘q τ : Γ, ℕ }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q (σ∘τ)][Id] ≈ A' : Type@i }} as <- by mauto 3.
      transitivity {{{ A[q σ∘q τ] }}}; mauto 3.
      transitivity {{{ A[q σ∘q τ][Id] }}}; mauto 3.
      eapply exp_eq_sub_cong_typ1; mauto 3.
    + assert {{ Δ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][q τ][Id,,zero] ≈ A[q σ][τ,,zero] : Type@i }} as -> by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ[τ] }} by mauto 4.
      assert {{ Δ' ⊢s τ,,zero ≈ τ,,zero[τ] : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][τ,,zero[τ]] : Type@i }} by (symmetry; mauto 4).
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][Id,,zero][τ] : Type@i }} as -> by mauto 4.
      assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] : Type@i }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][Id,,zero][τ] ≈ A[Id,,zero][σ][τ] : Type@i }} as -> by mauto 3.
      mauto 3.
    + assert {{ Δ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 2.
      assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 2.
      assert {{ Δ', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q (σ∘τ)] }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ][q τ] ≈ A[q σ∘q τ] : Type@i }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] ≈ A[q (σ∘τ)] : Type@i }} by mauto 2.
      assert {{ ⊢ Δ', ℕ, A[q σ∘q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 3.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} as -> by eassumption.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s Wk∘Wk,,succ #1 : Δ', ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q σ][q τ][Wk∘Wk,,succ #1] ≈ A[q (σ∘τ)][Wk∘Wk,,succ #1] : Type@i }} as -> by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q (σ∘τ)][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Type@i }} as -> by mauto 3 using exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1.
      assert {{ Δ', ℕ ⊢s q (σ∘τ) : Γ, ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 2.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Δ', ℕ, A[q σ∘q τ] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ∘q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Type@i }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as -> by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))][Id] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q (σ∘τ))][Id] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Type@i }} as <- by mauto 3.
      mauto 3.
Qed.

Lemma glu_rel_exp_natrec_helper : forall {i Γ SbΓ A MZ MS},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ Γ, ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    forall {Δ M m},
      glu_nat Δ M m ->
      forall {σ ρ am P El},
        {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m ↘ am }} ->
        {{ DG am ∈ glu_univ_elem i ↘ P ↘ El }} ->
        exists r,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
            {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? HA ? ?.
  assert {{ ⊩ Γ }} by mauto 2.
  assert {{ Γ ⊩ ℕ : Type@0 }} as Hℕ by mauto 3.
  assert {{ Γ ⊩ A[Id,,zero] : Type@i }}.
  {
    assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 2.
    assert {{ Γ ⊢ ℕ ⊆ ℕ[Id] }} by mauto 4.
    mauto.
  }
  pose (SbΓℕ := cons_glu_sub_pred 0 Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  pose proof HA.
  invert_glu_rel_exp HA.
  assert {{ Γ, ℕ, A ⊩ A[Wk∘Wk,,succ #1] : Type@i }}.
  {
    assert {{ ⊩ Γ, ℕ, A }} by mauto 3.
    assert {{ Γ, ℕ ⊩s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊩s Wk : Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }} by mauto 3.
    assert {{ Γ, ℕ, A ⊩ #1 : ℕ[Wk][Wk] }} by mauto 3.
    assert {{ Γ, ℕ, A ⊩ #1 : ℕ }} by mauto 3.
    mauto.
  }
  induction 1; intros; rename Γ0 into Δ.
  - (** [glu_nat_zero] *)
    mauto 4 using glu_rel_exp_natrec_zero_helper.
  - (** [glu_nat_succ] *)
    mauto 3 using glu_rel_exp_natrec_succ_helper.
  - (** [glu_nat_neut] *)
    mauto 3 using glu_rel_exp_natrec_neut_helper.
Qed.

Lemma glu_rel_exp_natrec : forall {Γ i A MZ MS M},
    {{ Γ, ℕ ⊩ A : Type@i }} ->
    {{ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊩ M : ℕ }} ->
    {{ Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Proof.
  intros * HA HMZ HMS HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 2.
  assert {{ Γ ⊩ ℕ : Type@0 }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred 0 Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity).
  assert {{ Γ, ℕ ⊩ Type@i : Type@(S i) }} by mauto 3.
  pose proof HM.
  invert_glu_rel_exp HM.
  pose proof HA.
  invert_glu_rel_exp HA.
  eexists; split; [eassumption |].
  eexists.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  clear_dups.
  inversion_clear_by_head nat_glu_exp_pred.
  assert {{ Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 2).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  inversion_clear_by_head nat_glu_exp_pred.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  clear_dups.
  match_by_head nat_glu_typ_pred ltac:(fun H => clear H).
  match goal with
  | _: {{ ⟦ A ⟧ ρ ↦ m ↘ ^?a' }},
      _: {{ DG ^?a' ∈ glu_univ_elem i ↘ ?P' ↘ ?El' }} |- _ =>
      rename a' into a;
      rename P' into P;
      rename El' into El
  end.
  assert (exists r, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\ El Δ {{{ A[σ,, M[σ]] }}} {{{ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}} r) as [? []] by (eapply glu_rel_exp_natrec_helper; revgoals; mauto 4).
  econstructor; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ ⊢ M : ℕ }} by mauto 2.
  assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,M[σ]] ≈ A[Id,,M][σ] : Type@i }} as <- by (symmetry; mauto 2).
  assert {{ Δ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} as -> by (econstructor; mauto 3).
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_natrec : mctt.
