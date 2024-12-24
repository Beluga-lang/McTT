From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation SubtypingCases TermStructureCases.
Import Domain_Notations.

Lemma glu_rel_exp_of_typ : forall {Γ Sb A i},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        {{ Δ ⊢ A[σ] : Type@i }} /\
          exists a,
            {{ ⟦ A ⟧ ρ ↘ a }} /\
              {{ Dom a ≈ a ∈ per_univ i }} /\
              forall P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ A[σ] ® P }}) ->
    {{ Γ ⊩ A : Type@i }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto.
  exists (S i).
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
Qed.

Lemma glu_rel_exp_typ : forall {Γ i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ Type@i : Type@(S i) }}.
Proof.
  intros * [].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem invert_glu_univ_elem.
  apply_predicate_equivalence.
  cbn.
  mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_typ : mctt.

Lemma glu_rel_exp_clean_inversion2' : forall {i Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊩ M : Type@i }} ->
    glu_rel_exp_resp_sub_env (S i) Sb M {{{ Type@i }}}.
Proof.
  intros * ? HM.
  assert {{ Γ ⊩ Type@i : Type@(S i) }} by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.


Lemma glu_rel_exp_sub_typ : forall {Γ σ Δ i A},
    {{ Γ ⊩s σ : Δ }} ->
    {{ Δ ⊩ A : Type@i }} ->
    {{ Γ ⊩ A[σ] : Type@i }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Γ ⊢ Type@i[σ] ⊆ Type@i }} by mauto 3.
  assert {{ Γ ⊩ A[σ] : Type@i[σ] }} by mauto 4.
  mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_typ : mctt.


Lemma glu_rel_exp_typ_sub_clean_inversion : forall {Γ σ Δ Sb M A i},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Δ ⊩ A : Type@i }} ->
    {{ Γ ⊩s σ : Δ }} ->
    {{ Γ ⊩ M : A[σ] }} ->
    glu_rel_exp_resp_sub_env i Sb M {{{A[σ]}}}.
Proof.
  intros * ? ? ? HM.
  assert {{ Γ ⊩ A[σ] : Type@i }} by mauto.
  eapply glu_rel_exp_clean_inversion2 in HM; eassumption.
Qed.


#[global]
  Ltac universe_invert_glu_rel_exp H :=
  directed (unshelve eapply (glu_rel_exp_typ_sub_clean_inversion _) in H; shelve_unifiable; try eassumption;
   simpl in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2' _) in H; shelve_unifiable; [eassumption |];
   simpl in H)
  + basic_invert_glu_rel_exp H.


#[global]
  Ltac invert_glu_rel_exp H ::= universe_invert_glu_rel_exp H.
