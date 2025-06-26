From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import Syntax_Notations.

(** ** Basic Context Properties *)

Lemma ctx_lookup_lt : forall {Γ A x},
    {{ #x : A ∈ Γ }} ->
    x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.
#[export]
Hint Resolve ctx_lookup_lt : mctt.

Lemma functional_ctx_lookup : forall {Γ A A' x},
    {{ #x : A ∈ Γ }} ->
    {{ #x : A' ∈ Γ }} ->
    A = A'.
Proof with mautosolve.
  intros * Hx Hx'; gen A'.
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx';
    f_equal;
    intuition.
Qed.

Lemma ctx_decomp : forall {Γ A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
Proof with now eauto.
  inversion 1...
Qed.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left : forall {Γ A}, {{ ⊢ Γ , A }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right : forall {Γ A}, {{ ⊢ Γ, A }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.

(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_ctx_eq_left : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

Corollary presup_ctx_eq_right : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mctt.

Lemma presup_sub : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_sub_left : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

Corollary presup_sub_right : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

#[export]
Hint Resolve presup_sub presup_sub_left presup_sub_right : mctt.

(** With [presup_sub], we can prove similar for [exp]. *)

Lemma presup_exp_ctx : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_ctx : mctt.

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_sub_eq_ctx_left : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

Corollary presup_sub_eq_ctx_right : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

#[export]
Hint Resolve presup_sub_eq_ctx presup_sub_eq_ctx_left presup_sub_eq_ctx_right : mctt.

Lemma presup_exp_eq_ctx : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mctt.

(** *** Immediate Results of Context Presuppositions *)

(** Recover some rules we had before adding subtyping.
    Rest are recovered after presupposition lemmas (in SystemOpt). *)

Lemma wf_cumu : forall Γ A i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A : Type@(S i) }}.
Proof with mautosolve.
  intros.
  enough {{ ⊢ Γ }}...
Qed.

Lemma wf_exp_eq_cumu : forall Γ A A' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@(S i) }}.
Proof with mautosolve.
  intros.
  enough {{ ⊢ Γ }}...
Qed.

#[export]
Hint Resolve wf_cumu wf_exp_eq_cumu : mctt.

Lemma wf_ctx_sub_refl : forall Γ Δ,
    {{ ⊢ Γ ≈ Δ }} ->
    {{ ⊢ Γ ⊆ Δ }}.
Proof. induction 1; mauto. Qed.

#[export]
Hint Resolve wf_ctx_sub_refl : mctt.

Lemma wf_conv : forall Γ M A i A',
    {{ Γ ⊢ M : A }} ->
    (** The next argument will be removed in SystemOpt *)
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_conv : mctt.

Lemma wf_sub_conv : forall Γ σ Δ Δ',
  {{ Γ ⊢s σ : Δ }} ->
  {{ ⊢ Δ ≈ Δ' }} ->
  {{ Γ ⊢s σ : Δ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_conv : mctt.

Lemma wf_exp_eq_conv : forall Γ M M' A A' i,
   {{ Γ ⊢ M ≈ M' : A }} ->
   (** The next argument will be removed in SystemOpt *)
   {{ Γ ⊢ A' : Type@i }} ->
   {{ Γ ⊢ A ≈ A' : Type@i }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_conv : mctt.

Lemma wf_sub_eq_conv : forall Γ σ σ' Δ Δ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_eq_conv : mctt.

Add Parametric Morphism Γ : (wf_sub_eq Γ)
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  intros Δ Δ' H **; split; [| symmetry in H]; mauto.
Qed.

(** We can prove some additional lemmas for type presuppositions as well. *)

Lemma lift_exp_ge : forall {Γ A n m},
    n <= m ->
    {{ Γ ⊢ A : Type@n }} ->
    {{ Γ ⊢ A : Type@m }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve lift_exp_ge : mctt.

Corollary lift_exp_max_left : forall {Γ A n} m,
    {{ Γ ⊢ A : Type@n }} ->
    {{ Γ ⊢ A : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (n <= max n m) by lia...
Qed.

Corollary lift_exp_max_right : forall {Γ A} n {m},
    {{ Γ ⊢ A : Type@m }} ->
    {{ Γ ⊢ A : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (m <= max n m) by lia...
Qed.

Lemma lift_exp_eq_ge : forall {Γ A A' n m},
    n <= m ->
    {{ Γ ⊢ A ≈ A': Type@n }} ->
    {{ Γ ⊢ A ≈ A' : Type@m }}.
Proof with mautosolve.
  induction 1; subst...
Qed.

#[export]
Hint Resolve lift_exp_eq_ge : mctt.

Corollary lift_exp_eq_max_left : forall {Γ A A' n} m,
    {{ Γ ⊢ A ≈ A' : Type@n }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (n <= max n m) by lia...
Qed.

Corollary lift_exp_eq_max_right : forall {Γ A A'} n {m},
    {{ Γ ⊢ A ≈ A' : Type@m }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (m <= max n m) by lia...
Qed.

(** *** Additional Lemmas for Syntactic PERs *)

Lemma exp_eq_refl : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M ≈ M : A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_refl : mctt.

Lemma exp_eq_trans_typ_max : forall {Γ i i' A A' A''},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A' ≈ A'' : Type@i' }} ->
    {{ Γ ⊢ A ≈ A'' : Type@(max i i') }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i i') }} by eauto using lift_exp_eq_max_left.
  assert {{ Γ ⊢ A' ≈ A'' : Type@(max i i') }} by eauto using lift_exp_eq_max_right...
Qed.

#[export]
Hint Resolve exp_eq_trans_typ_max : mctt.

Lemma sub_eq_refl : forall {Γ σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof. mauto. Qed.

#[export]
Hint Resolve sub_eq_refl : mctt.

Lemma ctx_eq_refl : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ≈ Γ }}.
Proof.
  induction 1; mauto 4.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mctt.

(** *** Lemmas for [exp] of [{{{ Type@i }}}] *)

Lemma exp_sub_typ : forall {Δ Γ A σ i},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
  econstructor...
Qed.

#[export]
Hint Resolve exp_sub_typ : mctt.

Lemma presup_ctx_lookup_typ : forall {Γ A x},
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    exists i, {{ Γ ⊢ A : Type@i }}.
Proof with mautosolve 4.
  intros * HΓ.
  induction 1; inversion_clear HΓ;
    [assert {{ Γ, A ⊢ Type@i[Wk] ≈ Type@i : Type@(S i) }} by mauto 4
    | assert (exists i, {{ Γ ⊢ A : Type@i }}) as [] by eauto]; econstructor...
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mctt.

Lemma exp_eq_sub_cong_typ1 : forall {Δ Γ A A' σ i},
    {{ Δ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_cong_typ2' : forall {Δ Γ A σ τ i},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_compose_typ : forall {Ψ Δ Γ A σ τ i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mctt.

Lemma exp_eq_sub_compose_weaken_extend_typ : forall {Γ σ Δ i A j B M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; [mautosolve 4 |].
  eapply exp_eq_sub_cong_typ2'...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mctt.

Lemma exp_eq_sub_compose_weaken_id_extend_typ : forall {Γ i A j B M},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ A[Wk][Id,,M] ≈ A : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mctt.

Lemma exp_eq_sub_compose_double_weaken_double_extend_typ : forall {Γ σ Δ i A j B M k C N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Δ, B ⊢ C : Type@k }} ->
    {{ Γ ⊢ N : C[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  assert {{ Δ, B, C ⊢s Wk : Δ, B }} by mauto 4.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply exp_eq_sub_cong_typ1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_typ : mctt.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_typ : forall {Γ i A j B M k C N},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B ⊢ C : Type@k }} ->
    {{ Γ ⊢ N : C[Id,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_typ : mctt.

Lemma exp_eq_typ_sub_sub : forall {Γ Δ Ψ σ τ i},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ Type@i[σ][τ] ≈ Type@i : Type@(S i) }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_typ_sub_sub : mctt.
#[export]
Hint Rewrite -> @exp_eq_sub_compose_typ @exp_eq_typ_sub_sub using mauto 4 : mctt.

Lemma vlookup_0_typ : forall {Γ i},
    {{ ⊢ Γ }} ->
    {{ Γ, Type@i ⊢ #0 : Type@i }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv; mauto 4.
  econstructor...
Qed.

Lemma vlookup_1_typ : forall {Γ i A j},
    {{ Γ, Type@i ⊢ A : Type@j }} ->
    {{ Γ, Type@i, A ⊢ #1 : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, Type@i ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Type@i, A ⊢s Wk : Γ, Type@i }} by mauto 4.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mctt.

Lemma exp_sub_typ_helper : forall {Γ σ Δ M i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Type@i }} ->
    {{ Γ ⊢ M : Type@i[σ] }}.
Proof.
  intros.
  do 2 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve exp_sub_typ_helper : mctt.

Lemma exp_eq_var_0_sub_typ : forall {Γ σ Δ M i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Type@i }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : Type@i }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor...
Qed.

Lemma exp_eq_var_1_sub_typ : forall {Γ σ Δ A i M j},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : Type@j[Wk] ∈ Δ }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : Type@j }}.
Proof with mautosolve 4.
  inversion 4 as [? Δ'|]; subst.
  assert {{ ⊢ Δ' }} by mauto 4.
  assert {{ Δ', Type@j ⊢s Wk : Δ' }} by mauto 4.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_typ exp_eq_var_1_sub_typ : mctt.
#[export]
Hint Rewrite -> @exp_eq_var_0_sub_typ @exp_eq_var_1_sub_typ : mctt.

Lemma exp_eq_var_0_weaken_typ : forall {Γ A i},
    {{ ⊢ Γ, A }} ->
    {{ #0 : Type@i[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : Type@i }}.
Proof with mautosolve 3.
  inversion_clear 1.
  inversion 1 as [? Γ'|]; subst.
  assert {{ ⊢ Γ' }} by mauto.
  assert {{ Γ', Type@i ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Γ', Type@i, A ⊢s Wk : Γ', Type@i }} by mauto 4.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_typ : mctt.

Lemma sub_extend_typ : forall {Γ σ Δ M i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Type@i }} ->
    {{ Γ ⊢s σ,,M : Δ, Type@i }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_extend_typ : mctt.

Lemma sub_eq_extend_cong_typ : forall {Γ σ σ' Δ M M' i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : Type@i }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, Type@i }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma sub_eq_extend_compose_typ : forall {Γ τ Γ' σ Γ'' A i M j},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A : Type@i }} ->
    {{ Γ' ⊢ M : Type@j }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', Type@j }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_typ : forall {Γ σ Γ' M i},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : Type@i }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ Type@i : Type@(S i) }} by mauto.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_typ sub_eq_extend_compose_typ sub_eq_p_extend_typ : mctt.


Lemma exp_eq_sub_sub_compose_cong_typ : forall {Γ Δ Δ' Ψ σ τ σ' τ' A i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }} by mauto.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Type@i }} by mauto.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] : Type@i }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mctt.

(** *** Lemmas for [exp] of [{{{ ℕ }}}] *)

Lemma exp_sub_nat : forall {Δ Γ M σ},
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
  econstructor...
Qed.

#[export]
Hint Resolve exp_sub_nat : mctt.

Lemma exp_eq_sub_cong_nat1 : forall {Δ Γ M M' σ},
    {{ Δ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] ≈ M'[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_cong_nat2 : forall {Δ Γ M σ τ},
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ M[σ] ≈ M[τ] : ℕ }}.
Proof with mautosolve.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_compose_nat : forall {Ψ Δ Γ M σ τ},
    {{ Ψ ⊢ M : ℕ }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_sub_nat exp_eq_sub_cong_nat1 exp_eq_sub_cong_nat2 exp_eq_sub_compose_nat : mctt.

Lemma exp_eq_nat_sub_sub : forall {Γ Δ Ψ σ τ},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ : Type@0 }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub : mctt.

Lemma exp_eq_nat_sub_sub_to_nat_sub : forall {Γ Δ Ψ Ψ' σ τ σ'},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s σ' : Ψ' }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ[σ'] : Type@0 }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub_to_nat_sub : mctt.

Lemma exp_eq_sub_compose_weaken_extend_nat : forall {Γ σ Δ M i B N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Δ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Γ ⊢ M[Wk][σ,,N] ≈ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  transitivity {{{ M[Wk∘(σ,,N)] }}}; [mauto 4 |].
  eapply exp_eq_sub_cong_nat2...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_nat : mctt.

Lemma exp_eq_sub_compose_weaken_id_extend_nat : forall {Γ M i B N},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ ⊢ M[Wk][Id,,N] ≈ M : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ N : B[Id] }} by mauto 2.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_nat : mctt.

Lemma exp_eq_sub_compose_double_weaken_double_extend_nat : forall {Γ σ Δ M i B N j C L},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Δ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Δ, B ⊢ C : Type@j }} ->
    {{ Γ ⊢ L : C[σ,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][σ,,N,,L] ≈ M[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  assert {{ Δ, B, C ⊢s Wk : Δ, B }} by mauto 4.
  transitivity {{{ M[Wk][Wk][σ,,N,,L] }}}; [eapply exp_eq_sub_cong_nat1; mautosolve 3 |].
  transitivity {{{ M[Wk][σ,,N] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_nat : mctt.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_nat : forall {Γ M i B N j C L},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ, B ⊢ C : Type@j }} ->
    {{ Γ ⊢ L : C[Id,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][Id,,N,,L] ≈ M : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ N : B[Id] }} by mauto 2.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_nat : mctt.

Lemma vlookup_0_nat : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ Γ, ℕ ⊢ #0 : ℕ }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv; mauto 4.
  econstructor...
Qed.

Lemma vlookup_1_nat : forall {Γ A i},
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ Γ, ℕ, A ⊢ #1 : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 4.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve vlookup_0_nat vlookup_1_nat : mctt.

Lemma exp_sub_nat_helper : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M : ℕ[σ] }}.
Proof.
  intros.
  do 2 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve exp_sub_nat_helper : mctt.

Lemma exp_eq_var_0_sub_nat : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor...
Qed.

Lemma exp_eq_var_1_sub_nat : forall {Γ σ Δ A i M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : ℕ[Wk] ∈ Δ }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ }}.
Proof with mautosolve 4.
  inversion 4 as [? Δ'|]; subst.
  assert {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ[Wk][σ] }} by mauto 4.
  assert {{ Γ ⊢ ℕ[Wk][σ] ≈ ℕ : Type@0 }}...
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_nat exp_eq_var_1_sub_nat : mctt.

Lemma exp_eq_var_0_weaken_nat : forall {Γ A},
    {{ ⊢ Γ, A }} ->
    {{ #0 : ℕ[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : ℕ }}.
Proof with mautosolve 4.
  inversion 1; subst.
  inversion 1 as [? Γ'|]; subst.
  assert {{ Γ', ℕ, A ⊢ #0[Wk] ≈ #1 : ℕ[Wk][Wk] }} by mauto 4.
  assert {{ Γ', ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }}...
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_nat : mctt.

Lemma sub_extend_nat : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ,,M : Δ, ℕ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_extend_nat : mctt.

Lemma sub_eq_extend_cong_nat : forall {Γ σ σ' Δ M M'},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma sub_eq_extend_compose_nat : forall {Γ τ Γ' σ Γ'' M},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', ℕ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_nat : forall {Γ σ Γ' M},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ ℕ : Type@0 }} by mauto.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_nat sub_eq_extend_compose_nat sub_eq_p_extend_nat : mctt.

Lemma exp_eq_sub_sub_compose_cong_nat : forall {Γ Δ Δ' Ψ σ τ σ' τ' M},
    {{ Ψ ⊢ M : ℕ }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : ℕ }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : ℕ }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_nat : mctt.

(** *** Other Tedious Lemmas *)

Lemma sub_eq_weaken_var0_id : forall {Γ A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof with mautosolve 4.
  intros * ?.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s (Wk∘Id),,#0[Id] ≈ Id : Γ, A }} by mauto.
  assert {{ Γ, A ⊢s Wk ≈ Wk∘Id : Γ }} by mauto.
  enough {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }}...
Qed.

#[export]
Hint Resolve sub_eq_weaken_var0_id : mctt.
#[export]
Hint Rewrite -> @sub_eq_weaken_var0_id using mauto 4 : mctt.

Lemma exp_eq_sub_sub_compose_cong : forall {Γ Δ Δ' Ψ σ τ σ' τ' M A i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Ψ ⊢ M : A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Type@i }} by mauto.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mctt.

Lemma ctxeq_ctx_lookup : forall {Γ Δ A x},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ #x : A ∈ Γ }} ->
    exists B i,
      {{ #x : B ∈ Δ }} /\
        {{ Γ ⊢ A ≈ B : Type@i }} /\
        {{ Δ ⊢ A ≈ B : Type@i }}.
Proof with mautosolve.
  intros * HΓΔ Hx; gen Δ.
  induction Hx as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? ? HΓΔ'];
    [|specialize (IHHx _ HΓΔ')]; destruct_conjs; repeat eexists...
Qed.

#[export]
Hint Resolve ctxeq_ctx_lookup : mctt.

Lemma sub_id_on_typ : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve sub_id_on_typ : mctt.

Lemma sub_id_extend : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_id_extend : mctt.

Lemma sub_eq_id_on_typ : forall {Γ M M' A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve sub_eq_id_on_typ : mctt.

Lemma sub_eq_id_extend_cong : forall {Γ M M' A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_id_extend_cong : mctt.

Lemma sub_eq_p_id_extend : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_p_id_extend : mctt.
#[export]
Hint Rewrite -> @sub_eq_p_id_extend using mauto 4 : mctt.

Lemma sub_q : forall {Γ A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s q σ : Δ, A }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 4.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  econstructor; mauto 3.
  eapply wf_conv...
Qed.

Lemma sub_q_typ : forall {Γ σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, Type@i ⊢s q σ : Δ, Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ, Type@i ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Type@i ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, Type@i ⊢ #0 : Type@i }}...
Qed.

Lemma sub_q_nat : forall {Γ σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ ⊢s q σ : Δ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_q sub_q_typ sub_q_nat : mctt.

Lemma exp_eq_var_1_sub_q_sigma_nat : forall {Γ A i σ Δ},
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto.
  assert {{ ⊢ Γ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ, ℕ ⊢ #0 : ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 4.
  assert {{ Γ, ℕ, A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] : Type@i }} by mauto 4.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ∘Wk] }} by (eapply wf_conv; mauto 4).
  assert {{ Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Δ, ℕ }} by mauto 4.
  assert {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : ℕ }} by mauto 4.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : ℕ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ[σ∘Wk] }} by (eapply wf_conv; mauto 4).
  assert {{ Γ, ℕ ⊢ #0[q σ] ≈ #0 : ℕ }} by mauto 4.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : ℕ }} by mauto 4.
  econstructor...
Qed.

#[export]
Hint Resolve exp_eq_var_1_sub_q_sigma_nat : mctt.

Lemma sub_id_extend_zero : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s Id,,zero : Γ, ℕ }}.
Proof. mauto. Qed.

Lemma sub_weak_compose_weak_extend_succ_var_1 : forall {Γ A i},
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 4.
  enough {{ Γ, ℕ, A ⊢s Wk∘Wk : Γ }}...
Qed.

Lemma sub_eq_id_extend_nat_compose_sigma : forall {Γ M σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Δ, ℕ }} by mauto 4.
  enough {{ Γ ⊢s (Id∘σ),,M[σ] ≈ σ,,M[σ] : Δ, ℕ }} by mauto 4.
  eapply sub_eq_extend_cong_nat...
Qed.

Lemma sub_eq_id_extend_compose_sigma : forall {Γ M A σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ⊢s Id : Δ }} by mauto.
  assert {{ Δ ⊢ M : A[Id] }} by mauto.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : A[Id][σ] }} by mauto.
  assert {{ Γ ⊢ A[Id][σ] ≈ A[Id∘σ] : Type@i }} by mauto.
  assert {{ Γ ⊢ M[σ] : A[Id∘σ] }} by mauto 4.
  enough {{ Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve sub_id_extend_zero sub_weak_compose_weak_extend_succ_var_1 sub_eq_id_extend_nat_compose_sigma sub_eq_id_extend_compose_sigma : mctt.

Lemma sub_eq_sigma_compose_weak_id_extend : forall {Γ M A i σ Δ},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }}.
Proof with mautosolve.
  intros.
  assert {{ Γ ⊢s Id,,M : Γ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ∘(Wk∘(Id,,M)) : Δ }} by mauto 4.
  assert {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }} by mauto.
  enough {{ Γ ⊢s σ∘(Wk∘ (Id,,M)) ≈ σ∘Id : Δ }} by mauto.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_sigma_compose_weak_id_extend : mctt.

Lemma sub_eq_q_sigma_id_extend : forall {Γ M A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto.
  assert {{ Γ ⊢ M : A[σ] }} by mauto.
  assert {{ Γ ⊢s Id,,M : Γ, A[σ] }} by mauto.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by (eapply wf_conv; mauto 3).
  assert {{ Γ ⊢s q σ∘(Id,,M) ≈ ((σ∘Wk)∘(Id,,M)),,#0[Id,,M] : Δ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }} by mauto.
  assert {{ Γ ⊢ M : A[σ][Id] }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ][Id] }} by mauto 3.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ] }} by mauto.
  enough {{ Γ ⊢ #0[Id,,M] ≈ M : A[(σ∘Wk)∘(Id,,M)] }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_id_extend : mctt.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_id_extend using mauto 4 : mctt.

Lemma sub_eq_p_q_sigma : forall {Γ A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  enough {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma : mctt.

Lemma sub_eq_p_q_sigma_nat : forall {Γ σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with mautosolve.
  intros.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_nat : mctt.

Lemma sub_eq_p_p_q_q_sigma_nat : forall {Γ A i σ Δ},
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, ℕ ⊢ A[q σ] : Type@i }} by mauto.
  assert {{ ⊢ Γ, ℕ, A[q σ] }} by mauto 3.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘q (q σ) ≈ q σ∘Wk : Δ, ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ Wk∘(q σ∘Wk) : Δ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘(q σ∘Wk) ≈ (Wk∘q σ)∘Wk : Δ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Δ }} by mauto.
  enough {{ Γ, ℕ, A[q σ] ⊢s (Wk∘q σ)∘Wk ≈ (σ∘Wk)∘Wk : Δ }}...
Qed.

#[export]
Hint Resolve sub_eq_p_p_q_q_sigma_nat : mctt.

Lemma sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : forall {Γ A i σ Δ},
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Δ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ, ℕ, A }} by mauto 3.
  assert {{ ⊢ Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Δ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
  set (Γ' := {{{ Γ, ℕ, A[q σ] }}}).
  set (WkWksucc := {{{ (Wk∘Wk),,succ #1 }}}).
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢s Wk∘Wk : Γ }} by mauto 4.
  assert {{ Γ' ⊢s WkWksucc : Γ, ℕ }} by mauto.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }} by mauto.
  assert {{ Γ' ⊢s q σ∘WkWksucc ≈ ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] : Δ, ℕ }} by mautosolve 3.
  assert {{ Γ' ⊢ #1 : ℕ[Wk][Wk] }} by mauto.
  assert {{ Γ' ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ Γ' ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Γ' ⊢ succ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢s Wk∘WkWksucc : Γ }} by mauto 4.
  assert {{ Γ' ⊢s Wk∘WkWksucc ≈ Wk∘Wk : Γ }} by mauto 4.
  assert {{ Γ ⊢s σ ≈ σ : Δ }} by mauto.
  assert {{ Γ' ⊢s σ∘(Wk∘WkWksucc) ≈ σ∘(Wk∘Wk) : Δ }} by mauto 3.
  assert {{ Γ' ⊢s (σ∘Wk)∘WkWksucc ≈ σ∘(Wk∘Wk) : Δ }} by mauto 3.
  assert {{ Γ' ⊢s σ∘(Wk∘Wk) ≈ (σ∘Wk)∘Wk : Δ }} by mauto 4.
  assert {{ Γ' ⊢s (σ∘Wk)∘Wk ≈ Wk∘(Wk∘q (q σ)) : Δ }} by mauto.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢s Wk : Δ, ℕ }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk : Δ }} by mauto 4.
  assert {{ Γ' ⊢s q (q σ) : Δ, ℕ, A }} by mauto.
  assert {{ Γ' ⊢s Wk∘(Wk∘q (q σ)) ≈ (Wk∘Wk)∘q (q σ) : Δ }} by mauto 3.
  assert {{ Γ' ⊢s σ∘(Wk∘Wk) ≈ (Wk∘Wk)∘q (q σ) : Δ }} by mauto 3.
  assert {{ Γ' ⊢ #0[WkWksucc] ≈ succ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢ succ #1[q (q σ)] ≈ succ #1 : ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Γ' ⊢ succ #1 ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 4.
  assert {{ Γ' ⊢ #0[WkWksucc] ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 2.
  assert {{ Γ' ⊢s (σ∘Wk)∘WkWksucc : Δ }} by mauto 3.
  assert {{ Γ' ⊢s ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] ≈ ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] : Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢ succ #1 : ℕ }} by mauto.
  enough {{ Γ' ⊢s ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] ≈ WkWksucc∘q (q σ) : Δ, ℕ }}...
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : mctt.

(** *** Lemmas for [wf_subtyp] *)

Fact wf_subtyp_refl : forall {Γ A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A ⊆ A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_subtyp_refl : mctt.

Lemma wf_subtyp_ge : forall {Γ i j},
    {{ ⊢ Γ }} ->
    i <= j ->
    {{ Γ ⊢ Type@i ⊆ Type@j }}.
Proof.
  induction 2; mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_ge : mctt.

Lemma wf_subtyp_sub : forall {Δ A A'},
    {{ Δ ⊢ A ⊆ A' }} ->
    forall Γ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  induction 1; intros; mauto 4.
  - transitivity {{{ Type@i }}}; [econstructor; mauto 4 |].
    transitivity {{{ Type@j }}}; [| econstructor; mauto 4].
    mauto 3.
  - transitivity {{{ Π (A[σ]) (B[q σ]) }}}; [econstructor; mauto |].
    transitivity {{{ Π (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4].
    eapply wf_subtyp_pi with (i := i); mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_sub : mctt.

Lemma wf_subtyp_univ_weaken : forall {Γ i j A},
    {{ Γ ⊢ Type@i ⊆ Type@j }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ Type@i ⊆ Type@j }}.
Proof.
  intros.
  eapply wf_subtyp_sub with (σ := {{{ Wk }}}) in H.
  - transitivity {{{ Type@i[Wk] }}}; [econstructor; mauto |].
    etransitivity; mauto.
  - mauto.
Qed.

Lemma ctx_sub_ctx_lookup : forall {Γ Δ},
    {{ ⊢ Δ ⊆ Γ }} ->
    forall {A x},
      {{ #x : A ∈ Γ }} ->
      exists B,
        {{ #x : B ∈ Δ }} /\
          {{ Δ ⊢ B ⊆ A }}.
Proof with (do 2 eexists; repeat split; mautosolve).
  induction 1; intros * Hx; progressive_inversion.
  dependent destruction Hx.
  - idtac...
  - edestruct IHwf_ctx_sub as [? []]; try eassumption...
Qed.

#[export]
Hint Resolve ctx_sub_ctx_lookup : mctt.

Lemma var_compose_subs : forall {Γ τ Δ σ Ψ i A x},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ #x : A[σ][τ] ∈ Γ }} ->
    {{ Γ ⊢ #x : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
Qed.

#[export]
Hint Resolve var_compose_subs : mctt.

Lemma sub_lookup_var0 : forall Δ Γ σ M1 M2 B i,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #0[σ,,M1,,M2] ≈ M2 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] : Type @ i }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] : Type @ i }}.
  {
    transitivity {{{ B[Wk∘(σ,,M1)] }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
    - eapply exp_eq_sub_cong_typ2'; mauto 4.
  }
  eapply wf_exp_eq_conv;
    [eapply wf_exp_eq_var_0_sub with (A := {{{ B[Wk] }}}) | |];
    mauto 4.
Qed.

Lemma id_sub_lookup_var0 : forall Γ M1 M2 B i,
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var0 | |];
    mauto 3.
Qed.

Lemma sub_lookup_var1 : forall Δ Γ σ M1 M2 B i,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #1[σ,,M1,,M2] ≈ M1 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] : Type @ i }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] : Type @ i }}.
  {
    transitivity {{{ B[Wk∘(σ,,M1)] }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
    - eapply exp_eq_sub_cong_typ2'; mauto 4.
  }
  transitivity {{{ #0[σ,,M1] }}}.
  - eapply wf_exp_eq_conv;
      [eapply wf_exp_eq_var_S_sub | |];
      mauto 4.
  - eapply wf_exp_eq_conv;
    [eapply wf_exp_eq_var_0_sub with (A := B) | |];
    mauto 2.
    mauto.
Qed.

Lemma id_sub_lookup_var1 : forall Γ M1 M2 B i,
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var1 | |];
    mauto 3.
Qed.

Lemma exp_eq_var_1_sub_q_sigma : forall {Γ A i B j σ Δ},
    {{ Δ ⊢ B : Type@j }} ->
    {{ Δ, B ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s q σ : Δ, B }} by mauto 2.
  assert {{ ⊢ Γ, B[σ] }} by mauto 3.
  assert {{ ⊢ Γ, B[σ], A[q σ] }} by mauto 3.
  assert {{ Δ, B ⊢ B[Wk] : Type@j }} by mauto 4.
  assert {{ Δ, B ⊢ #0 : B[Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] : Type@i }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢s q σ∘Wk : Δ, B }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ∘Wk] }} by mauto 3.
  assert {{ Γ ⊢ B[σ] : Type@j }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk : Γ, B[σ] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[σ][Wk] : Type@j }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk] : Type@j }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk] : Type@j }} by (eapply exp_eq_sub_sub_compose_cong_typ; mauto 3).
  assert {{ Γ, B[σ],A[q σ] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk] : Type@j }} by (transitivity {{{ B[Wk][q σ][Wk] }}}; mauto 3).
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ] ⊢s σ∘Wk : Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ∘Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ∘Wk][Wk] ≈ B[σ][Wk][Wk] : Type@j }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ][Wk][Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk][Wk] }} by (do 2 etransitivity; mauto 2).
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk∘Wk] : Type@j }} by mauto 2.
  eapply wf_exp_eq_conv; mauto 2.
Qed.

(** *** Type Presuppositions *)

Lemma presup_exp_typ : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  induction 1; assert {{ ⊢ Γ }} by mauto 3; destruct_conjs; mauto 3.

  - enough {{ Γ ⊢s Id,,M : Γ, ℕ }}; mauto 3.

  - eexists; mauto 4 using lift_exp_max_left, lift_exp_max_right.

  - enough {{ Γ ⊢s Id,,N : Γ, A }}; mauto 3.

  - enough {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }} by mauto 4.
    assert {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4).

    assert {{ Γ ⊢s Id,,M1 : Γ, A }} by mauto 3.
    assert {{ Γ ⊢ M2 : A[Wk][Id,,M1] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
    assert {{ Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }} by mauto 3.
    econstructor; [mautosolve 3 | mautosolve 3 |].
    eapply wf_conv; [| | symmetry]; mauto 3.
    transitivity {{{ Eq A[Wk∘Wk][Id,,M1,,M2] #1[Id,,M1,,M2] #0[Id,,M1,,M2] }}}.
    + econstructor; mauto 3 using id_sub_lookup_var0, id_sub_lookup_var1; eapply wf_conv; mauto 4.
    + assert {{ Γ ⊢ M2 : A }} by eassumption. (* re-assert to help search process *)
      assert {{ Γ ⊢ M1 : A[Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
      assert {{ Γ ⊢ M2 : A[Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
      econstructor; mauto 3 using id_sub_lookup_var0, id_sub_lookup_var1.
Qed.

Lemma presup_exp : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  mauto 4 using presup_exp_typ.
Qed.

(** *** Consistency Helper *)

Lemma no_closed_neutral : forall {A} {W : ne},
    ~ {{ ⋅ ⊢ W : A }}.
Proof.
  intros * H.
  dependent induction H; destruct W;
    try (simpl in *; congruence);
    autoinjections;
    intuition.
  inversion_by_head ctx_lookup.
Qed.
#[export]
Hint Resolve no_closed_neutral : mctt.
