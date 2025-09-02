From Coq Require Import Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.

Lemma wf_typ_inversion : forall {Γ i A},
    {{ Γ ⊢ Type@i : A }} ->
    {{ Γ ⊢ Type@(S i) ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H...
Qed.

#[export]
Hint Resolve wf_typ_inversion : mctt.

Lemma wf_nat_inversion : forall Γ A,
    {{ Γ ⊢ ℕ : A }} ->
    {{ Γ ⊢ Type@0 ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  assert (forall i, 0 <= i) by lia.
  dependent induction H...
Qed.

#[export]
Hint Resolve wf_nat_inversion : mctt.

Corollary wf_zero_inversion : forall Γ A,
    {{ Γ ⊢ zero : A }} ->
    {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl)...
Qed.

#[export]
Hint Resolve wf_zero_inversion : mctt.

Corollary wf_succ_inversion : forall Γ A M,
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ eq_refl);
    destruct_conjs...
Qed.

#[export]
Hint Resolve wf_succ_inversion : mctt.

Lemma wf_natrec_inversion : forall Γ A M A' MZ MS,
    {{ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} ->
    {{ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Γ, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ A'[Id,,M] ⊆ A }}.
Proof with mautosolve.
  intros * H.
  pose (A0 := A).
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split...
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mctt.

Lemma wf_pi_inversion : forall {Γ A B C},
    {{ Γ ⊢ Π A B : C }} ->
    exists i, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }} /\ {{ Γ ⊢ Type@i ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups; eexists...
Qed.

#[export]
Hint Resolve wf_pi_inversion : mctt.

Corollary wf_pi_inversion' : forall {Γ A B i},
    {{ Γ ⊢ Π A B : Type@i }} ->
    {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}.
Proof with mautosolve 4.
  intros * [j [? []]]%wf_pi_inversion.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A ⊢ Type@j ⊆ Type@j[Wk] }} by (econstructor; mauto 4).
  assert {{ Γ, A ⊢ Type@j[Wk] ⊆ Type@i[Wk] }} by mauto 4.
  assert {{ Γ, A ⊢ Type@i[Wk] ⊆ Type@i }} by (econstructor; mauto 4).
  enough {{ Γ, A ⊢ Type@j ⊆ Type@i }}...
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mctt.

Corollary wf_fn_inversion : forall {Γ A M C},
    {{ Γ ⊢ λ A M : C }} ->
    exists B, {{ Γ, A ⊢ M : B }} /\ {{ Γ ⊢ Π A B ⊆ C }}.
Proof with solve [mauto using lift_exp_max_left, lift_exp_max_right].
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; split...
Qed.

#[export]
Hint Resolve wf_fn_inversion : mctt.

Lemma wf_app_inversion : forall {Γ M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B, {{ Γ ⊢ M : Π A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ B[Id,,N] ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    do 2 eexists; repeat split...
Qed.

#[export]
Hint Resolve wf_app_inversion : mctt.

Lemma wf_sigma_inversion : forall {Γ A B C},
    {{ Γ ⊢ Σ A B : C }} ->
    exists i, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }} /\ {{ Γ ⊢ Type@i ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups; eexists...
Qed.

#[export]
Hint Resolve wf_sigma_inversion : mctt.

Corollary wf_sigma_inversion' : forall {Γ A B i},
    {{ Γ ⊢ Σ A B : Type@i }} ->
    {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}.
Proof with mautosolve 4.
  intros * [j [? []]]%wf_sigma_inversion.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A ⊢ Type@j ⊆ Type@j[Wk] }} by (econstructor; mauto 4).
  assert {{ Γ, A ⊢ Type@j[Wk] ⊆ Type@i[Wk] }} by mauto 4.
  assert {{ Γ, A ⊢ Type@i[Wk] ⊆ Type@i }} by (econstructor; mauto 4).
  enough {{ Γ, A ⊢ Type@j ⊆ Type@i }}...
Qed.

#[export]
Hint Resolve wf_sigma_inversion' : mctt.

Lemma wf_vlookup_inversion : forall {Γ x A},
    {{ Γ ⊢ #x : A }} ->
    exists A', {{ #x : A' ∈ Γ }} /\ {{ Γ ⊢ A' ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ eq_refl));
    destruct_conjs; gen_core_presups; eexists; split...
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mctt.

Lemma wf_exp_sub_inversion : forall {Γ M σ A},
    {{ Γ ⊢ M[σ] : A }} ->
    exists Δ A', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\ {{ Γ ⊢ A'[σ] ⊆ A }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ eq_refl));
    destruct_conjs;
    do 2 eexists; repeat split; mauto 3.
  assert (exists j, {{ Δ ⊢ A : Type@j }}) as [] by mauto 2 using presup_exp_typ...
Qed.

#[export]
Hint Resolve wf_exp_sub_inversion : mctt.

(** We omit [wf_conv] and [wf_cumu] as they do not give useful inversions *)

Lemma wf_sub_id_inversion : forall Γ Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ⊆ Δ }}.
Proof.
  intros * H.
  dependent induction H; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mctt.

Lemma wf_sub_weaken_inversion : forall {Γ Δ},
    {{ Γ ⊢s Wk : Δ }} ->
    exists Γ' A, {{ ⊢ Γ ≈ Γ', A }} /\ {{ ⊢ Γ' ⊆ Δ }}.
Proof.
  intros * H.
  dependent induction H;
    firstorder;
    progressive_inversion;
    repeat eexists; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_weaken_inversion : mctt.

Lemma wf_sub_compose_inversion : forall {Γ1 σ1 σ2 Γ3},
    {{ Γ1 ⊢s σ1 ∘ σ2 : Γ3 }} ->
    exists Γ2, {{ Γ1 ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Γ3 }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H; mauto 3.
  specialize (IHwf_sub _ _ eq_refl).
  destruct_conjs.
  eexists.
  repeat split...
Qed.

#[export]
Hint Resolve wf_sub_compose_inversion : mctt.

Lemma wf_sub_extend_inversion : forall {Γ σ M Δ},
    {{ Γ ⊢s σ,,M : Δ }} ->
    exists Δ' A', {{ ⊢ Δ', A' ⊆ Δ }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_sub _ _ eq_refl);
    destruct_conjs;
    repeat eexists...
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mctt.
