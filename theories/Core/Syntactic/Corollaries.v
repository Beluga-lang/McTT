From Coq Require Import Setoid Nat.
From Mcltt Require Import Base LibTactics CtxSub.
From Mcltt.Core Require Export SystemOpt CoreInversions.
Import Syntax_Notations.

Corollary sub_id_typ : forall Γ M A,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A [ Id ] }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve sub_id_typ : mcltt.

Corollary invert_sub_id : forall Γ M A,
    {{ Γ ⊢ M [ Id ] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_sub_id : mcltt.

Corollary invert_sub_id_typ : forall Γ M A,
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  autorewrite with mcltt in *; eassumption.
Qed.

#[export]
Hint Resolve invert_sub_id_typ : mcltt.

Lemma invert_compose_id : forall {Γ σ Δ},
    {{ Γ ⊢s σ ∘ Id : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  intros * [? []]%wf_sub_compose_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_compose_id : mcltt.

Add Parametric Morphism i Γ Δ : a_sub
    with signature wf_exp_eq Δ {{{ Type@i }}} ==> wf_sub_eq Γ Δ ==> wf_exp_eq Γ {{{ Type@i }}} as sub_typ_cong.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.

Add Parametric Morphism Γ1 Γ2 Γ3 : a_compose
    with signature wf_sub_eq Γ2 Γ3 ==> wf_sub_eq Γ1 Γ2 ==> wf_sub_eq Γ1 Γ3 as sub_compose_cong.
Proof. mauto. Qed.

Lemma wf_ctx_sub_length : forall Γ Δ,
    {{ ⊢ Γ ⊆ Δ }} ->
    length Γ = length Δ.
Proof. induction 1; simpl; auto. Qed.

Open Scope list_scope.

Lemma app_ctx_lookup : forall Δ T Γ n,
    length Δ = n ->
    {{ #n : ~(iter (S n) (fun T => {{{T [ Wk ]}}}) T) ∈ ~(Δ ++ T :: Γ) }}.
Proof.
  induction Δ; intros; simpl in *; subst; mauto.
Qed.

Lemma ctx_lookup_functional : forall n T Γ,
    {{ #n : T ∈ Γ }} ->
    forall T',
      {{ #n : T' ∈ Γ }} ->
      T = T'.
Proof.
  induction 1; intros; progressive_inversion; eauto.
  erewrite IHctx_lookup; eauto.
Qed.

Lemma app_ctx_vlookup : forall Δ T Γ n,
    {{ ⊢ ~(Δ ++ T :: Γ) }} ->
    length Δ = n ->
    {{ ~(Δ ++ T :: Γ) ⊢ #n : ~(iter (S n) (fun T => {{{T [ Wk ]}}}) T) }}.
Proof.
  intros. econstructor; auto using app_ctx_lookup.
Qed.

Lemma sub_q_eq : forall Δ A i Γ σ σ',
                   {{ Δ ⊢ A : Type@i }} ->
                   {{ Γ ⊢s σ ≈ σ' : Δ }} ->
                   {{ Γ, A[σ] ⊢s q σ ≈ q σ' : Δ, A }}.
Proof.
  intros. gen_presup H0.
  econstructor; mauto 3.
  - econstructor; mauto 4.
  - rewrite <- @exp_eq_sub_compose_typ; mauto 4.
Qed.
#[export]
 Hint Resolve sub_q_eq : mcltt.

Lemma wf_subtyp_subst_eq : forall Δ A B,
    {{ Δ ⊢ A ⊆ B }} ->
    forall Γ σ σ',
      {{ Γ ⊢s σ ≈ σ' : Δ }} ->
      {{ Γ ⊢ A [σ] ⊆ B[σ'] }}.
Proof.
  induction 1; intros * Hσσ'; gen_presup Hσσ'.
  - eapply wf_subtyp_refl'.
    eapply wf_exp_eq_conv; mauto 4.
  - etransitivity; mauto 4.
  - autorewrite with mcltt.
    mauto 2.
  - autorewrite with mcltt.
    eapply wf_subtyp_pi'; mauto.
Qed.

Lemma wf_subtyp_subst : forall Δ A B,
    {{ Δ ⊢ A ⊆ B }} ->
    forall Γ σ,
      {{ Γ ⊢s σ : Δ }} ->
      {{ Γ ⊢ A [σ] ⊆ B[σ] }}.
Proof.
  intros; mauto 2 using wf_subtyp_subst_eq.
Qed.
#[export]
 Hint Resolve wf_subtyp_subst_eq wf_subtyp_subst : mcltt.

Lemma sub_decompose_q : forall Γ S i σ Δ Δ' τ t,
  {{Γ ⊢ S : Type@i}} ->
  {{Δ ⊢s σ : Γ}} ->
  {{Δ' ⊢s τ : Δ}} ->
  {{Δ' ⊢ t : S [ σ ] [ τ ]}} ->
  {{Δ' ⊢s q σ ∘ (τ ,, t) ≈ σ ∘ τ ,, t : Γ, S}}.
Proof.
  intros. gen_presups.
  simpl. autorewrite with mcltt.
  symmetry.
  rewrite wf_sub_eq_extend_compose; mauto 3;
    [| mauto
    | rewrite <- @exp_eq_sub_compose_typ; mauto 4].
  eapply wf_sub_eq_extend_cong; eauto.
  - rewrite wf_sub_eq_compose_assoc; mauto 3; mauto 4.
    rewrite wf_sub_eq_p_extend; eauto; mauto 4.
  - rewrite <- @exp_eq_sub_compose_typ; mauto 4.
Qed.

Lemma sub_decompose_q_typ : forall Γ S T i σ Δ Δ' τ t,
  {{Γ, S ⊢ T : Type@i}} ->
  {{Δ ⊢s σ : Γ}} ->
  {{Δ' ⊢s τ : Δ}} ->
  {{Δ' ⊢ t : S [ σ ] [ τ ]}} ->
  {{Δ' ⊢ T [ σ ∘ τ ,, t ] ≈ T [ q σ ] [ τ ,, t ] : Type@i}}.
Proof.
  intros. gen_presups.
  autorewrite with mcltt.
  eapply exp_eq_sub_cong_typ2'; [mauto 2 | econstructor; mauto 4 |].
  symmetry. mauto using sub_decompose_q.
Qed.

Lemma sub_eq_p_q_sigma_compose_tau_extend : forall {Δ' τ Δ M A i σ Γ},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ' ⊢s τ : Δ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Δ' ⊢ M : A[σ][τ] }} ->
    {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ σ∘τ : Γ }}.
Proof.
  intros.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 4.
  assert {{ Δ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ }} by mauto 4.
  assert {{ Δ' ⊢s τ,,M : Δ, A[σ] }} by mauto 4.
  assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 4.
  assert {{ Δ' ⊢s Wk∘(τ,,M) ≈ τ : Δ }} by mauto 4.
  assert {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ (Wk∘q σ)∘(τ,,M) : Γ }} by mauto 4.
  assert {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ (σ∘Wk)∘(τ,,M) : Γ }} by mauto 4.
  assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘(Wk∘(τ,,M)) : Γ }} by mauto 4.
  assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘τ : Γ }} by mauto 4.
  mauto 4.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_compose_tau_extend : mcltt.
