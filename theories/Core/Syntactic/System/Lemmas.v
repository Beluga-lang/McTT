From Coq Require Import List.

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

Lemma gctx_decomp : forall {Δ x M A}, {{ ⊢ Δ, x := [ M ] :: A }} -> {{ ⊢ Δ }} /\ exists i, {{ Δ ;; ⋅ ⊢ A : Type@i }}.
Proof with now eauto. 
  inversion 1...
Qed.

Lemma ctx_decomp : forall {Δ Γ A}, {{ ⊢ Δ ;; Γ, A }} -> {{ ⊢ Δ ;; Γ }} /\ exists i, {{ Δ ;; Γ ⊢ A : Type@i }}.
Proof with now eauto.
  inversion 1...
Qed.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left : forall {Δ Γ A}, {{ ⊢ Δ ;; Γ, A }} -> {{ ⊢ Δ ;; Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right : forall {Δ Γ A}, {{ ⊢ Δ ;; Γ, A }} -> exists i, {{ Δ ;; Γ ⊢ A : Type@i }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.

(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq : forall {Δ Γ Γ'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ ⊢ Δ ;; Γ }} /\ {{ ⊢ Δ ;; Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_ctx_eq_left : forall {Δ Γ Γ'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ ⊢ Δ ;; Γ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

Corollary presup_ctx_eq_right : forall {Δ Γ Γ'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ ⊢ Δ ;; Γ' }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mctt.

Lemma presup_sub : forall {Δ Γ Γ' σ}, {{ Δ ;; Γ ⊢s σ : Γ' }} -> {{ ⊢ Δ ;; Γ }} /\ {{ ⊢ Δ ;; Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_sub_left : forall {Δ Γ Γ' σ}, {{ Δ ;; Γ ⊢s σ : Γ' }} -> {{ ⊢ Δ ;; Γ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

Corollary presup_sub_right : forall {Δ Γ Γ' σ}, {{ Δ ;; Γ ⊢s σ : Γ' }} -> {{ ⊢ Δ ;; Γ' }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

#[export]
Hint Resolve presup_sub presup_sub_left presup_sub_right : mctt.

(** With [presup_sub], we can prove similar for [exp]. *)

Lemma presup_exp_ctx : forall {Δ Γ M A}, {{ Δ ;; Γ ⊢ M : A }} -> {{ ⊢ Δ ;; Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_ctx : mctt.

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx : forall {Δ Γ Γ' σ σ'}, {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ⊢ Δ ;; Γ }} /\ {{ ⊢ Δ ;; Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_sub_eq_ctx_left : forall {Δ Γ Γ' σ σ'}, {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ⊢ Δ ;; Γ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

Corollary presup_sub_eq_ctx_right : forall {Δ Γ Γ' σ σ'}, {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ⊢ Δ ;; Γ' }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

#[export]
Hint Resolve presup_sub_eq_ctx presup_sub_eq_ctx_left presup_sub_eq_ctx_right : mctt.

Lemma presup_exp_eq_ctx : forall {Δ Γ M M' A}, {{ Δ ;; Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Δ ;; Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mctt.

(** *** Immediate Results of Context Presuppositions *)

(** Recover some rules we had before adding subtyping.
    Rest are recovered after presupposition lemmas (in SystemOpt). *)

Lemma wf_cumu : forall Δ Γ A i,
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ A : Type@(S i) }}.
Proof with mautosolve.
  intros.
  enough {{ ⊢ Δ ;; Γ }}...
Qed.

Lemma wf_exp_eq_cumu : forall Δ Γ A A' i,
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@(S i) }}.
Proof with mautosolve.
  intros.
  enough {{ ⊢ Δ ;; Γ }}...
Qed.

#[export]
Hint Resolve wf_cumu wf_exp_eq_cumu : mctt.

Lemma wf_ctx_sub_refl : forall Δ Γ Γ',
    {{ Δ ⊢ Γ ≈ Γ' }} ->
    {{ Δ ⊢ Γ ⊆ Γ' }}.
Proof. induction 1; mauto. Qed.

#[export]
Hint Resolve wf_ctx_sub_refl : mctt.

Lemma wf_conv : forall Δ Γ M A i A',
    {{ Δ ;; Γ ⊢ M : A }} ->
    (** The next argument will be removed in SystemOpt *)
    {{ Δ ;; Γ ⊢ A' : Type@i }} ->
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Δ ;; Γ ⊢ M : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_conv : mctt.

Lemma wf_sub_conv : forall Δ Γ1 σ Γ2 Γ3,
  {{ Δ ;; Γ1 ⊢s σ : Γ2 }} ->
  {{ Δ ⊢ Γ2 ≈ Γ3 }} ->
  {{ Δ ;; Γ1 ⊢s σ : Γ3 }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_conv : mctt.

Lemma wf_exp_eq_conv : forall Δ Γ M M' A A' i,
   {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
   (** The next argument will be removed in SystemOpt *)
   {{ Δ ;; Γ ⊢ A' : Type@i }} ->
   {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
   {{ Δ ;; Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_conv : mctt.

Lemma wf_sub_eq_conv : forall Δ Γ1 σ σ' Γ2 Γ3,
    {{ Δ ;; Γ1 ⊢s σ ≈ σ' : Γ2 }} ->
    {{ Δ ⊢ Γ2 ≈ Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s σ ≈ σ' : Γ3 }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_eq_conv : mctt.

Add Parametric Morphism Δ Γ : (wf_sub_eq Δ Γ)
    with signature wf_ctx_eq Δ ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  intros Γ1 Γ2 H **; split; [| symmetry in H]; mauto.
Qed.

(** We can prove some additional lemmas for type presuppositions as well. *)

Lemma lift_exp_ge : forall {Δ Γ A n m},
    n <= m ->
    {{ Δ ;; Γ ⊢ A : Type@n }} ->
    {{ Δ ;; Γ ⊢ A : Type@m }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve lift_exp_ge : mctt.

Corollary lift_exp_max_left : forall {Δ Γ A n} m,
    {{ Δ ;; Γ ⊢ A : Type@n }} ->
    {{ Δ ;; Γ ⊢ A : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (n <= max n m) by lia...
Qed.

Corollary lift_exp_max_right : forall {Δ Γ A} n {m},
    {{ Δ ;; Γ ⊢ A : Type@m }} ->
    {{ Δ ;; Γ ⊢ A : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (m <= max n m) by lia...
Qed.

Lemma lift_exp_eq_ge : forall {Δ Γ A A' n m},
    n <= m ->
    {{ Δ ;; Γ ⊢ A ≈ A': Type@n }} ->
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@m }}.
Proof with mautosolve.
  induction 1; subst...
Qed.

#[export]
Hint Resolve lift_exp_eq_ge : mctt.

Corollary lift_exp_eq_max_left : forall {Δ Γ A A' n} m,
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@n }} ->
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (n <= max n m) by lia...
Qed.

Corollary lift_exp_eq_max_right : forall {Δ Γ A A'} n {m},
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@m }} ->
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof with mautosolve.
  intros.
  assert (m <= max n m) by lia...
Qed.

(** *** Additional Lemmas for Syntactic PERs *)

Lemma exp_eq_refl : forall {Δ Γ M A},
    {{ Δ ;; Γ ⊢ M : A }} ->
    {{ Δ ;; Γ ⊢ M ≈ M : A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_refl : mctt.

Lemma exp_eq_trans_typ_max : forall {Δ Γ i i' A A' A''},
    {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Δ ;; Γ ⊢ A' ≈ A'' : Type@i' }} ->
    {{ Δ ;; Γ ⊢ A ≈ A'' : Type@(max i i') }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ ⊢ A ≈ A' : Type@(max i i') }} by eauto using lift_exp_eq_max_left.
  assert {{ Δ ;; Γ ⊢ A' ≈ A'' : Type@(max i i') }} by eauto using lift_exp_eq_max_right...
Qed.

#[export]
Hint Resolve exp_eq_trans_typ_max : mctt.

Lemma sub_eq_refl : forall {Δ Γ σ Γ'},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢s σ ≈ σ : Γ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve sub_eq_refl : mctt.

Lemma ctx_eq_refl : forall {Δ Γ},
    {{ ⊢ Δ ;; Γ }} ->
    {{ Δ ⊢ Γ ≈ Γ }}.
Proof.
  induction 1; mauto 4.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mctt.

(** *** Lemmas for [exp] of [{{{ Type@i }}}] *)

Lemma exp_sub_typ : forall {Δ Γ Γ' A σ i},
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ A[σ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
  econstructor...
Qed.

#[export]
Hint Resolve exp_sub_typ : mctt.

Lemma presup_ctx_lookup_typ : forall {Δ Γ A x},
    {{ ⊢ Δ ;; Γ }} ->
    {{ #x : A ∈ Γ }} ->
    exists i, {{ Δ ;; Γ ⊢ A : Type@i }}.
Proof with mautosolve 4.
  intros * HΓ.
  induction 1; inversion_clear HΓ;
    [assert {{ Δ ;; Γ, A ⊢ Type@i[Wk] ≈ Type@i : Type@(S i) }} by mauto 4
    | assert (exists i, {{ Δ ;; Γ ⊢ A : Type@i }}) as [] by eauto]; econstructor...
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mctt.

Lemma exp_eq_sub_cong_typ1 : forall {Δ Γ Γ' A A' σ i},
    {{ Δ ;; Γ' ⊢ A ≈ A' : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ A[σ] ≈ A'[σ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_cong_typ2' : forall {Δ Γ Γ' A σ τ i},
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Δ ;; Γ ⊢ A[σ] ≈ A[τ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_compose_typ : forall {Δ Γ1 Γ2 Γ3 A σ τ i},
    {{ Δ ;; Γ3 ⊢ A : Type@i }} ->
    {{ Δ ;; Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mctt.

Lemma exp_eq_sub_compose_weaken_extend_typ : forall {Δ Γ σ Γ' i A j B M},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ' ⊢ B : Type@j }} ->
    {{ Δ ;; Γ ⊢ M : B[σ] }} ->
    {{ Δ ;; Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Type@i }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ;; Γ', B ⊢s Wk : Γ' }} by mauto 4.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; [mautosolve 4 |].
  eapply exp_eq_sub_cong_typ2'...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mctt.

Lemma exp_eq_sub_compose_weaken_id_extend_typ : forall {Δ Γ i A j B M},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ B : Type@j }} ->
    {{ Δ ;; Γ ⊢ M : B }} ->
    {{ Δ ;; Γ ⊢ A[Wk][Id,,M] ≈ A : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mctt.

Lemma exp_eq_sub_compose_double_weaken_double_extend_typ : forall {Δ Γ σ Γ' i A j B M k C N},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ' ⊢ B : Type@j }} ->
    {{ Δ ;; Γ ⊢ M : B[σ] }} ->
    {{ Δ ;; Γ', B ⊢ C : Type@k }} ->
    {{ Δ ;; Γ ⊢ N : C[σ,,M] }} ->
    {{ Δ ;; Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ', B ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply exp_eq_sub_cong_typ1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_typ : mctt.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_typ : forall {Δ Γ i A j B M k C N},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ B : Type@j }} ->
    {{ Δ ;; Γ ⊢ M : B }} ->
    {{ Δ ;; Γ, B ⊢ C : Type@k }} ->
    {{ Δ ;; Γ ⊢ N : C[Id,,M] }} ->
    {{ Δ ;; Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_typ : mctt.

Lemma exp_eq_typ_sub_sub : forall {Δ Γ1 Γ2 Γ3 σ τ i},
    {{ Δ ;; Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢ Type@i[σ][τ] ≈ Type@i : Type@(S i) }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_typ_sub_sub : mctt.
#[export]
Hint Rewrite -> @exp_eq_sub_compose_typ @exp_eq_typ_sub_sub using mauto 4 : mctt.

Lemma vlookup_0_typ : forall {Δ Γ i},
    {{ ⊢ Δ ;; Γ }} ->
    {{ Δ ;; Γ, Type@i ⊢ #0 : Type@i }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv; mauto 4.
  econstructor...
Qed.

Lemma vlookup_1_typ : forall {Δ Γ i A j},
    {{ Δ ;; Γ, Type@i ⊢ A : Type@j }} ->
    {{ Δ ;; Γ, Type@i, A ⊢ #1 : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ, Type@i ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ, Type@i, A ⊢s Wk : Γ, Type@i }} by mauto 4.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mctt.

Lemma exp_sub_typ_helper : forall {Δ Γ σ Γ' M i},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : Type@i }} ->
    {{ Δ ;; Γ ⊢ M : Type@i[σ] }}.
Proof.
  intros.
  do 2 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve exp_sub_typ_helper : mctt.

Lemma exp_eq_var_0_sub_typ : forall {Δ Γ σ Γ' M i},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : Type@i }} ->
    {{ Δ ;; Γ ⊢ #0[σ,,M] ≈ M : Type@i }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor...
Qed.

Lemma exp_eq_var_1_sub_typ : forall {Δ Γ σ Γ' A i M j},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ M : A[σ] }} ->
    {{ #0 : Type@j[Wk] ∈ Γ' }} ->
    {{ Δ ;; Γ ⊢ #1[σ,,M] ≈ #0[σ] : Type@j }}.
Proof with mautosolve 4.
  inversion 4 as [? Γ''|]; subst.
  assert {{ ⊢ Δ ;; Γ'' }} by mauto 4.
  assert {{ Δ ;; Γ'', Type@j ⊢s Wk : Γ'' }} by mauto 4.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_typ exp_eq_var_1_sub_typ : mctt.
#[export]
Hint Rewrite -> @exp_eq_var_0_sub_typ @exp_eq_var_1_sub_typ : mctt.

Lemma exp_eq_var_0_weaken_typ : forall {Δ Γ A i},
    {{ ⊢ Δ ;; Γ, A }} ->
    {{ #0 : Type@i[Wk] ∈ Γ }} ->
    {{ Δ ;; Γ, A ⊢ #0[Wk] ≈ #1 : Type@i }}.
Proof with mautosolve 3.
  inversion_clear 1.
  inversion 1 as [? Γ'|]; subst.
  assert {{ ⊢ Δ ;; Γ' }} by mauto.
  assert {{ Δ ;; Γ', Type@i ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ', Type@i, A ⊢s Wk : Γ', Type@i }} by mauto 4.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_typ : mctt.

Lemma sub_extend_typ : forall {Δ Γ σ Γ' M i},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ,,M : Γ', Type@i }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_extend_typ : mctt.

Lemma sub_eq_extend_cong_typ : forall {Δ Γ σ σ' Γ' M M' i},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Δ ;; Γ ⊢ M ≈ M' : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ,,M ≈ σ',,M' : Γ', Type@i }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma sub_eq_extend_compose_typ : forall {Δ Γ1 τ Γ2 σ Γ3 A i M j},
    {{ Δ ;; Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ;; Γ3 ⊢ A : Type@i }} ->
    {{ Δ ;; Γ2 ⊢ M : Type@j }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ3, Type@j }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_typ : forall {Δ Γ σ Γ' M i},
    {{ Δ ;; Γ' ⊢s σ : Γ }} ->
    {{ Δ ;; Γ' ⊢ M : Type@i }} ->
    {{ Δ ;; Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ ⊢ Type@i : Type@(S i) }} by mauto.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_typ sub_eq_extend_compose_typ sub_eq_p_extend_typ : mctt.


Lemma exp_eq_sub_sub_compose_cong_typ : forall {Δ Γ1 Γ2 Γ3 Γ4 σ τ σ' τ' A i},
    {{ Δ ;; Γ4 ⊢ A : Type@i }} ->
    {{ Δ ;; Γ2 ⊢s σ : Γ4 }} ->
    {{ Δ ;; Γ3 ⊢s σ' : Γ4 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢s τ' : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s σ∘τ ≈ σ'∘τ' : Γ4 }} ->
    {{ Δ ;; Γ1 ⊢ A[σ][τ] ≈ A[σ'][τ'] : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ1 ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }} by mauto.
  assert {{ Δ ;; Γ1 ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Type@i }} by mauto.
  enough {{ Δ ;; Γ1 ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] : Type@i }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mctt.

(** *** Lemmas for [exp] of [{{{ ℕ }}}] *)

Lemma exp_sub_nat : forall {Δ Γ Γ' M σ},
    {{ Δ ;; Γ' ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
  econstructor...
Qed.

#[export]
Hint Resolve exp_sub_nat : mctt.

Lemma exp_eq_sub_cong_nat1 : forall {Δ Γ Γ' M M' σ},
    {{ Δ ;; Γ' ⊢ M ≈ M' : ℕ }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M[σ] ≈ M'[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_cong_nat2 : forall {Δ Γ Γ' M σ τ},
    {{ Δ ;; Γ' ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M[σ] ≈ M[τ] : ℕ }}.
Proof with mautosolve.
  intros.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_sub_compose_nat : forall {Δ Γ1 Γ2 Γ3 M σ τ},
    {{ Δ ;; Γ3 ⊢ M : ℕ }} ->
    {{ Δ ;; Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_sub_nat exp_eq_sub_cong_nat1 exp_eq_sub_cong_nat2 exp_eq_sub_compose_nat : mctt.

Lemma exp_eq_nat_sub_sub : forall {Δ Γ1 Γ2 Γ3 σ τ},
    {{ Δ ;; Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢ ℕ[σ][τ] ≈ ℕ : Type@0 }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub : mctt.

Lemma exp_eq_nat_sub_sub_to_nat_sub : forall {Δ Γ1 Γ2 Γ3 Γ4 σ τ σ'},
    {{ Δ ;; Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢s σ' : Γ4 }} ->
    {{ Δ ;; Γ1 ⊢ ℕ[σ][τ] ≈ ℕ[σ'] : Type@0 }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub_to_nat_sub : mctt.

Lemma exp_eq_sub_compose_weaken_extend_nat : forall {Δ Γ σ Γ' M i B N},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ M : ℕ }} ->
    {{ Δ ;; Γ' ⊢ B : Type@i }} ->
    {{ Δ ;; Γ ⊢ N : B[σ] }} ->
    {{ Δ ;; Γ ⊢ M[Wk][σ,,N] ≈ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ;; Γ', B ⊢s Wk : Γ' }} by mauto 4.
  transitivity {{{ M[Wk∘(σ,,N)] }}}; [mauto 4 |].
  eapply exp_eq_sub_cong_nat2...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_nat : mctt.
  
Lemma exp_eq_sub_compose_weaken_id_extend_nat : forall {Δ Γ M i B N},
    {{ Δ ;; Γ ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢ B : Type@i }} ->
    {{ Δ ;; Γ ⊢ N : B }} ->
    {{ Δ ;; Γ ⊢ M[Wk][Id,,N] ≈ M : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ N : B[Id] }} by mauto 2.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_nat : mctt.

Lemma exp_eq_sub_compose_double_weaken_double_extend_nat : forall {Δ Γ σ Γ' M i B N j C L},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ M : ℕ }} ->
    {{ Δ ;; Γ' ⊢ B : Type@i }} ->
    {{ Δ ;; Γ ⊢ N : B[σ] }} ->
    {{ Δ ;; Γ', B ⊢ C : Type@j }} ->
    {{ Δ ;; Γ ⊢ L : C[σ,,N] }} ->
    {{ Δ ;; Γ ⊢ M[Wk∘Wk][σ,,N,,L] ≈ M[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ', B ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  transitivity {{{ M[Wk][Wk][σ,,N,,L] }}}; [eapply exp_eq_sub_cong_nat1; mautosolve 3 |].
  transitivity {{{ M[Wk][σ,,N] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_nat : mctt.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_nat : forall {Δ Γ M i B N j C L},
    {{ Δ ;; Γ ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢ B : Type@i }} ->
    {{ Δ ;; Γ ⊢ N : B }} ->
    {{ Δ ;; Γ, B ⊢ C : Type@j }} ->
    {{ Δ ;; Γ ⊢ L : C[Id,,N] }} ->
    {{ Δ ;; Γ ⊢ M[Wk∘Wk][Id,,N,,L] ≈ M : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ ⊢ B[Id] : Type@_ }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ N : B[Id] }} by mauto 2.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_nat : mctt.

Lemma vlookup_0_nat : forall {Δ Γ},
    {{ ⊢ Δ ;; Γ }} ->
    {{ Δ ;; Γ, ℕ ⊢ #0 : ℕ }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv; mauto 4.
  econstructor...
Qed.

Lemma vlookup_1_nat : forall {Δ Γ A i},
    {{ Δ ;; Γ, ℕ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ, ℕ, A ⊢ #1 : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 4.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve vlookup_0_nat vlookup_1_nat : mctt.

Lemma exp_sub_nat_helper : forall {Δ Γ σ Γ' M},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢ M : ℕ[σ] }}.
Proof.
  intros.
  do 2 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve exp_sub_nat_helper : mctt.

Lemma exp_eq_var_0_sub_nat : forall {Δ Γ σ Γ' M},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢ #0[σ,,M] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor...
Qed.

Lemma exp_eq_var_1_sub_nat : forall {Δ Γ σ Γ' A i M},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ M : A[σ] }} ->
    {{ #0 : ℕ[Wk] ∈ Γ' }} ->
    {{ Δ ;; Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ }}.
Proof with mautosolve 4.
  inversion 4 as [? Γ''|]; subst.
  assert {{ Δ ;; Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ[Wk][σ] }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ ℕ[Wk][σ] ≈ ℕ : Type@0 }}...
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_nat exp_eq_var_1_sub_nat : mctt.

Lemma exp_eq_var_0_weaken_nat : forall {Δ Γ A},
    {{ ⊢ Δ ;; Γ, A }} ->
    {{ #0 : ℕ[Wk] ∈ Γ }} ->
    {{ Δ ;; Γ, A ⊢ #0[Wk] ≈ #1 : ℕ }}.
Proof with mautosolve 4.
  inversion 1; subst.
  inversion 1 as [? Γ'|]; subst.
  assert {{ Δ ;; Γ', ℕ, A ⊢ #0[Wk] ≈ #1 : ℕ[Wk][Wk] }} by mauto 4.
  assert {{ Δ ;; Γ', ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }}...
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_nat : mctt.

Lemma sub_extend_nat : forall {Δ Γ σ Γ' M},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢s σ,,M : Γ', ℕ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_extend_nat : mctt.

Lemma sub_eq_extend_cong_nat : forall {Δ Γ σ σ' Γ' M M'},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Δ ;; Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Δ ;; Γ ⊢s σ,,M ≈ σ',,M' : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma sub_eq_extend_compose_nat : forall {Δ Γ τ Γ' σ Γ'' M},
    {{ Δ ;; Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ;; Γ' ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢s τ : Γ' }} ->
    {{ Δ ;; Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', ℕ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_nat : forall {Δ Γ σ Γ' M},
    {{ Δ ;; Γ' ⊢s σ : Γ }} ->
    {{ Δ ;; Γ' ⊢ M : ℕ }} ->
    {{ Δ ;; Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ;; Γ ⊢ ℕ : Type@0 }} by mauto.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_nat sub_eq_extend_compose_nat sub_eq_p_extend_nat : mctt.

Lemma exp_eq_sub_sub_compose_cong_nat : forall {Δ Γ1 Γ2 Γ3 Γ4 σ τ σ' τ' M},
    {{ Δ ;; Γ4 ⊢ M : ℕ }} ->
    {{ Δ ;; Γ2 ⊢s σ : Γ4 }} ->
    {{ Δ ;; Γ3 ⊢s σ' : Γ4 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢s τ' : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s σ∘τ ≈ σ'∘τ' : Γ4 }} ->
    {{ Δ ;; Γ1 ⊢ M[σ][τ] ≈ M[σ'][τ'] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ1 ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }} by mauto.
  assert {{ Δ ;; Γ1 ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : ℕ }} by mauto.
  enough {{ Δ ;; Γ1 ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : ℕ }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_nat : mctt.

(** *** Other Tedious Lemmas *)

Lemma sub_eq_weaken_var0_id : forall {Δ Γ A i},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof with mautosolve 4.
  intros * ?.
  assert {{ ⊢ Δ ;; Γ, A }} by mauto 3.
  assert {{ Δ ;; Γ, A ⊢s (Wk∘Id),,#0[Id] ≈ Id : Γ, A }} by mauto.
  assert {{ Δ ;; Γ, A ⊢s Wk ≈ Wk∘Id : Γ }} by mauto.
  enough {{ Δ ;; Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }}...
Qed.

#[export]
Hint Resolve sub_eq_weaken_var0_id : mctt.
#[export]
Hint Rewrite -> @sub_eq_weaken_var0_id using mauto 4 : mctt.

Lemma exp_eq_sub_sub_compose_cong : forall {Δ Γ1 Γ2 Γ3 Γ4 σ τ σ' τ' M A i},
    {{ Δ ;; Γ4 ⊢ A : Type@i }} ->
    {{ Δ ;; Γ4 ⊢ M : A }} ->
    {{ Δ ;; Γ2 ⊢s σ : Γ4 }} ->
    {{ Δ ;; Γ3 ⊢s σ' : Γ4 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ;; Γ1 ⊢s τ' : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s σ∘τ ≈ σ'∘τ' : Γ4 }} ->
    {{ Δ ;; Γ1 ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ1 ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Type@i }} by mauto.
  assert {{ Δ ;; Γ1 ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto.
  assert {{ Δ ;; Γ1 ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto.
  assert {{ Δ ;; Γ1 ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Δ ;; Γ1 ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mctt.

Lemma ctxeq_ctx_lookup : forall {Δ Γ Γ' A x},
    {{ Δ ⊢ Γ ≈ Γ' }} ->
    {{ #x : A ∈ Γ }} ->
    exists B i,
      {{ #x : B ∈ Γ' }} /\
        {{ Δ ;; Γ ⊢ A ≈ B : Type@i }} /\
        {{ Δ ;; Γ' ⊢ A ≈ B : Type@i }}.
Proof with mautosolve.
  intros * HΓΓ' Hx; gen Γ'.
  induction Hx as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? ? ? HΓΓ'']; 
    [|specialize (IHHx _ HΓΓ'')]; destruct_conjs; repeat eexists...
Qed.

#[export]
Hint Resolve ctxeq_ctx_lookup : mctt.

Lemma sub_id_on_typ : forall {Δ Γ M A i},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ M : A }} ->
    {{ Δ ;; Γ ⊢ M : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve sub_id_on_typ : mctt.

Lemma sub_id_extend : forall {Δ Γ M A i},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ M : A }} ->
    {{ Δ ;; Γ ⊢s Id,,M : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_id_extend : mctt.

Lemma sub_eq_id_on_typ : forall {Δ Γ M M' A i},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ;; Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve sub_eq_id_on_typ : mctt.

Lemma sub_eq_id_extend_cong : forall {Δ Γ M M' A i},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ;; Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_id_extend_cong : mctt.

Lemma sub_eq_p_id_extend : forall {Δ Γ M A i},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ M : A }} ->
    {{ Δ ;; Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_p_id_extend : mctt.
#[export]
Hint Rewrite -> @sub_eq_p_id_extend using mauto 4 : mctt.

Lemma sub_q : forall {Δ Γ A i σ Γ'},
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, A[σ] ⊢s q σ : Γ', A }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ;; Γ ⊢ A[σ] : Type@i }} by mauto 4.
  assert {{ Δ ;; Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  econstructor; mauto 3.
  eapply wf_conv...
Qed.

Lemma sub_q_typ : forall {Δ Γ σ Γ' i},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, Type@i ⊢s q σ : Γ', Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ ;; Γ }} by mauto 3.
  assert {{ Δ ;; Γ, Type@i ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ, Type@i ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ, Type@i ⊢ #0 : Type@i }}...
Qed.

Lemma sub_q_nat : forall {Δ Γ σ Γ'},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, ℕ ⊢s q σ : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ ;; Γ }} by mauto 3.
  assert {{ Δ ;; Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_q sub_q_typ sub_q_nat : mctt.

Lemma exp_eq_var_1_sub_q_sigma_nat : forall {Δ Γ A i σ Γ'},
    {{ Δ ;; Γ', ℕ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ, ℕ ⊢s q σ : Γ', ℕ }} by mauto.
  assert {{ ⊢ Δ ;; Γ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ;; Γ', ℕ ⊢ #0 : ℕ }} by mauto.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] : Type@i }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢ #0 : A[q σ∘Wk] }} by (eapply wf_conv; mauto 4).
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Γ', ℕ }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : ℕ }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : ℕ }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ ⊢ #0 : ℕ[σ∘Wk] }} by (eapply wf_conv; mauto 4).
  assert {{ Δ ;; Γ, ℕ ⊢ #0[q σ] ≈ #0 : ℕ }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : ℕ }} by mauto 4.
  econstructor...
Qed.

#[export]
Hint Resolve exp_eq_var_1_sub_q_sigma_nat : mctt.

Lemma sub_id_extend_zero : forall {Δ Γ},
    {{ ⊢ Δ ;; Γ }} ->
    {{ Δ ;; Γ ⊢s Id,,zero : Γ, ℕ }}.
Proof. mauto. Qed.

Lemma sub_weak_compose_weak_extend_succ_var_1 : forall {Δ Γ A i},
    {{ Δ ;; Γ, ℕ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 4.
  enough {{ Δ ;; Γ, ℕ, A ⊢s Wk∘Wk : Γ }}...
Qed.

Lemma sub_eq_id_extend_nat_compose_sigma : forall {Δ Γ M σ Γ'},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ M : ℕ }} ->
    {{ Δ ;; Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Γ', ℕ }} by mauto 4.
  enough {{ Δ ;; Γ ⊢s (Id∘σ),,M[σ] ≈ σ,,M[σ] : Γ', ℕ }} by mauto 4.
  eapply sub_eq_extend_cong_nat...
Qed.

Lemma sub_eq_id_extend_compose_sigma : forall {Δ Γ M A σ Γ' i},
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ' ⊢ M : A }} ->
    {{ Δ ;; Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ;; Γ' ⊢s Id : Γ' }} by mauto.
  assert {{ Δ ;; Γ' ⊢ M : A[Id] }} by mauto.
  assert {{ Δ ;; Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Γ', A }} by mauto 3.
  assert {{ Δ ;; Γ ⊢ M[σ] : A[Id][σ] }} by mauto.
  assert {{ Δ ;; Γ ⊢ A[Id][σ] ≈ A[Id∘σ] : Type@i }} by mauto.
  assert {{ Δ ;; Γ ⊢ M[σ] : A[Id∘σ] }} by mauto 4.
  enough {{ Δ ;; Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve sub_id_extend_zero sub_weak_compose_weak_extend_succ_var_1 sub_eq_id_extend_nat_compose_sigma sub_eq_id_extend_compose_sigma : mctt.

Lemma sub_eq_sigma_compose_weak_id_extend : forall {Δ Γ M A i σ Γ'},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : A }} ->
    {{ Δ ;; Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }}.
Proof with mautosolve.
  intros.
  assert {{ Δ ;; Γ ⊢s Id,,M : Γ, A }} by mauto.
  assert {{ Δ ;; Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ∘(Wk∘(Id,,M)) : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }} by mauto.
  enough {{ Δ ;; Γ ⊢s σ∘(Wk∘ (Id,,M)) ≈ σ∘Id : Γ' }} by mauto.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_sigma_compose_weak_id_extend : mctt.

Lemma sub_eq_q_sigma_id_extend : forall {Δ Γ M A i σ Γ'},
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ M : A[σ] }} ->
    {{ Δ ;; Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Γ', A }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ ;; Γ }} by mauto 3.
  assert {{ Δ ;; Γ ⊢ A[σ] : Type@i }} by mauto.
  assert {{ Δ ;; Γ ⊢ M : A[σ] }} by mauto.
  assert {{ Δ ;; Γ ⊢s Id,,M : Γ, A[σ] }} by mauto.
  assert {{ Δ ;; Γ, A[σ] ⊢s Wk : Γ }} by mauto.
  assert {{ Δ ;; Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto.
  assert {{ Δ ;; Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by (eapply wf_conv; mauto 3).
  assert {{ Δ ;; Γ ⊢s q σ∘(Id,,M) ≈ ((σ∘Wk)∘(Id,,M)),,#0[Id,,M] : Γ', A }} by mauto.
  assert {{ Δ ;; Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }} by mauto.
  assert {{ Δ ;; Γ ⊢ M : A[σ][Id] }} by mauto 4.
  assert {{ Δ ;; Γ ⊢ #0[Id,,M] ≈ M : A[σ][Id] }} by mauto 3.
  assert {{ Δ ;; Γ ⊢ #0[Id,,M] ≈ M : A[σ] }} by mauto.
  enough {{ Δ ;; Γ ⊢ #0[Id,,M] ≈ M : A[(σ∘Wk)∘(Id,,M)] }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_id_extend : mctt.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_id_extend using mauto 4 : mctt.

Lemma sub_eq_p_q_sigma : forall {Δ Γ A i σ Γ'},
    {{ Δ ;; Γ' ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ;; Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  enough {{ Δ ;; Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma : mctt.

Lemma sub_eq_p_q_sigma_nat : forall {Δ Γ σ Γ'},
    {{ Δ ;; Γ' ⊢ ℕ : Type@0 }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof with mautosolve.
  intros.
  assert {{ Δ ;; Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_nat : mctt.

Lemma sub_eq_p_p_q_q_sigma_nat : forall {Δ Γ A i σ Γ'},
    {{ Δ ;; Γ', ℕ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ;; Γ, ℕ ⊢ A[q σ] : Type@i }} by mauto.
  assert {{ ⊢ Δ ;; Γ, ℕ, A[q σ] }} by mauto 3.
  assert {{ ⊢ Δ ;; Γ', ℕ }} by mauto 3.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢s Wk∘q (q σ) ≈ q σ∘Wk : Γ', ℕ }} by mauto.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ Wk∘(q σ∘Wk) : Γ' }} by mauto 3.
  assert {{ Δ ;; Γ', ℕ ⊢s Wk : Γ' }} by mauto.
  assert {{ Δ ;; Γ, ℕ ⊢s q σ : Γ', ℕ }} by mauto.
  assert {{ Δ ;; Γ, ℕ, A[q σ] ⊢s Wk∘(q σ∘Wk) ≈ (Wk∘q σ)∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }} by mauto.
  enough {{ Δ ;; Γ, ℕ, A[q σ] ⊢s (Wk∘q σ)∘Wk ≈ (σ∘Wk)∘Wk : Γ' }}...
Qed.

#[export]
Hint Resolve sub_eq_p_p_q_q_sigma_nat : mctt.

Lemma sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : forall {Δ Γ A i σ Γ'},
    {{ Δ ;; Γ', ℕ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ ;; Γ', ℕ, A }} by mauto 3.
  assert {{ ⊢ Δ ;; Γ, ℕ }} by mauto 3.
  assert {{ Δ ;; Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  assert {{ Δ ;; Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 3.
  assert {{ Δ ;; Γ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
  set (Γ'' := {{{ Γ, ℕ, A[q σ] }}}).
  set (WkWksucc := {{{ (Wk∘Wk),,succ #1 }}}).
  assert {{ ⊢ Δ ;; Γ'' }} by mauto 2.
  assert {{ Δ ;; Γ'' ⊢s Wk∘Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ'' ⊢s WkWksucc : Γ, ℕ }} by mauto.
  assert {{ Δ ;; Γ, ℕ ⊢ #0 : ℕ }} by mauto.
  assert {{ Δ ;; Γ'' ⊢s q σ∘WkWksucc ≈ ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] : Γ', ℕ }} by mautosolve 3.
  assert {{ Δ ;; Γ'' ⊢ #1 : ℕ[Wk][Wk] }} by mauto.
  assert {{ Δ ;; Γ'' ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ ;; Γ'' ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Δ ;; Γ'' ⊢ succ #1 : ℕ }} by mauto.
  assert {{ Δ ;; Γ'' ⊢s Wk∘WkWksucc : Γ }} by mauto 4.
  assert {{ Δ ;; Γ'' ⊢s Wk∘WkWksucc ≈ Wk∘Wk : Γ }} by mauto 4.
  assert {{ Δ ;; Γ ⊢s σ ≈ σ : Γ' }} by mauto.
  assert {{ Δ ;; Γ'' ⊢s σ∘(Wk∘WkWksucc) ≈ σ∘(Wk∘Wk) : Γ' }} by mauto 3.
  assert {{ Δ ;; Γ'' ⊢s (σ∘Wk)∘WkWksucc ≈ σ∘(Wk∘Wk) : Γ' }} by mauto 3.
  assert {{ Δ ;; Γ'' ⊢s σ∘(Wk∘Wk) ≈ (σ∘Wk)∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ'' ⊢s (σ∘Wk)∘Wk ≈ Wk∘(Wk∘q (q σ)) : Γ' }} by mauto.
  assert {{ Δ ;; Γ', ℕ ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ', ℕ, A ⊢s Wk : Γ', ℕ }} by mauto 4.
  assert {{ Δ ;; Γ', ℕ, A ⊢s Wk∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ;; Γ'' ⊢s q (q σ) : Γ', ℕ, A }} by mauto.
  assert {{ Δ ;; Γ'' ⊢s Wk∘(Wk∘q (q σ)) ≈ (Wk∘Wk)∘q (q σ) : Γ' }} by mauto 3.
  assert {{ Δ ;; Γ'' ⊢s σ∘(Wk∘Wk) ≈ (Wk∘Wk)∘q (q σ) : Γ' }} by mauto 3.
  assert {{ Δ ;; Γ'' ⊢ #0[WkWksucc] ≈ succ #1 : ℕ }} by mauto.
  assert {{ Δ ;; Γ'' ⊢ succ #1[q (q σ)] ≈ succ #1 : ℕ }} by mauto 3.
  assert {{ Δ ;; Γ'' ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Δ ;; Γ'' ⊢ succ #1 ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 4.
  assert {{ Δ ;; Γ'' ⊢ #0[WkWksucc] ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 2.
  assert {{ Δ ;; Γ'' ⊢s (σ∘Wk)∘WkWksucc : Γ' }} by mauto 3.
  assert {{ Δ ;; Γ'' ⊢s ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] ≈ ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] : Γ', ℕ }} by mauto 3.
  assert {{ Δ ;; Γ', ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  assert {{ Δ ;; Γ', ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }} by mauto 3.
  assert {{ Δ ;; Γ', ℕ, A ⊢ succ #1 : ℕ }} by mauto.
  enough {{ Δ ;; Γ'' ⊢s ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] ≈ WkWksucc∘q (q σ) : Γ', ℕ }}...
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : mctt.

(** *** Lemmas for [wf_subtyp] *)

Fact wf_subtyp_refl : forall {Δ Γ A i},
    {{ Δ ;; Γ ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢ A ⊆ A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_subtyp_refl : mctt.

Lemma wf_subtyp_ge : forall {Δ Γ i j},
    {{ ⊢ Δ ;; Γ }} ->
    i <= j ->
    {{ Δ ;; Γ ⊢ Type@i ⊆ Type@j }}.
Proof.
  induction 2; mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_ge : mctt.

Lemma wf_subtyp_sub : forall {Δ Γ' A A'},
    {{ Δ ;; Γ' ⊢ A ⊆ A' }} ->
    forall Γ σ,
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  induction 1; intros; mauto 4.
  - transitivity {{{ Type@i }}}; [econstructor; mauto 4 |].
    transitivity {{{ Type@j }}}; [| econstructor; mauto 4].
    mauto 3.
  - transitivity {{{ Π (A[σ]) (B[q σ]) }}}; [econstructor; mauto |].
    transitivity {{{ Π (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4]. 
    eapply wf_subtyp_pi with (i := i); mauto 4.
  - transitivity {{{ Σ (A[σ]) (B[q σ]) }}}; [econstructor; mauto |].
    transitivity {{{ Σ (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4].
    eapply wf_subtyp_sigma with (i := i); mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_sub : mctt.

Lemma wf_subtyp_univ_weaken : forall {Δ Γ i j A},
    {{ Δ ;; Γ ⊢ Type@i ⊆ Type@j }} ->
    {{ ⊢ Δ ;; Γ, A }} ->
    {{ Δ ;; Γ, A ⊢ Type@i ⊆ Type@j }}.
Proof.
  intros.
  eapply wf_subtyp_sub with (σ := {{{ Wk }}}) in H.
  - transitivity {{{ Type@i[Wk] }}}; [econstructor; mauto |].
    etransitivity; mauto.
  - mauto.
Qed.

Lemma ctx_sub_ctx_lookup : forall {Δ Γ Γ'},
    {{ Δ ⊢ Γ' ⊆ Γ }} ->
    forall {A x},
      {{ #x : A ∈ Γ }} ->
      exists B,
        {{ #x : B ∈ Γ' }} /\
          {{ Δ ;; Γ' ⊢ B ⊆ A }}.
Proof with (do 2 eexists; repeat split; mautosolve).
  induction 1; intros * Hx; progressive_inversion.
  dependent destruction Hx.
  - idtac...
  - edestruct IHwf_ctx_sub as [? []]; try eassumption...
Qed.

#[export]
Hint Resolve ctx_sub_ctx_lookup : mctt.

Lemma var_compose_subs : forall {Δ Γ1 τ Γ2 σ Γ3 i A x},
    {{ Δ ;; Γ3 ⊢ A : Type@i }} ->
    {{ Δ ;; Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ;; Γ1 ⊢s τ : Γ2 }} ->
    {{ #x : A[σ][τ] ∈ Γ1 }} ->
    {{ Δ ;; Γ1 ⊢ #x : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
Qed.

#[export]
Hint Resolve var_compose_subs : mctt.

Lemma sub_lookup_var0 : forall Δ Γ σ Γ' M1 M2 B i,
    {{ Δ ;; Γ' ⊢s σ : Γ }} ->
    {{ Δ ;; Γ ⊢ B : Type@i }} ->
    {{ Δ ;; Γ' ⊢ M1 : B[σ] }} ->
    {{ Δ ;; Γ' ⊢ M2 : B[σ] }} ->
    {{ Δ ;; Γ' ⊢ #0[σ,,M1,,M2] ≈ M2 : B[σ] }}.
Proof.
  intros.
  assert {{ Δ ;; Γ, B ⊢ B[Wk] : Type@i }} by mauto.
  assert {{ Δ ;; Γ' ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ;; Γ' ⊢ B[Wk][σ,,M1] : Type @ i }} by mauto 4.
  assert {{ Δ ;; Γ' ⊢ B[Wk][σ,,M1] ≈ B[σ] : Type @ i }}.
  {
    transitivity {{{ B[Wk∘(σ,,M1)] }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
    - eapply exp_eq_sub_cong_typ2'; mauto 4.
  }
  eapply wf_exp_eq_conv;
    [eapply wf_exp_eq_var_0_sub with (A := {{{ B[Wk] }}}) | |];
    mauto 4.
Qed.

Lemma id_sub_lookup_var0 : forall Δ Γ M1 M2 B i,
    {{ Δ ;; Γ ⊢ B : Type@i }} ->
    {{ Δ ;; Γ ⊢ M1 : B }} ->
    {{ Δ ;; Γ ⊢ M2 : B }} ->
    {{ Δ ;; Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var0 | |];
    mauto 3.
Qed.

Lemma sub_lookup_var1 : forall Δ Γ σ Γ' M1 M2 B i,
    {{ Δ ;; Γ' ⊢s σ : Γ }} ->
    {{ Δ ;; Γ ⊢ B : Type@i }} ->
    {{ Δ ;; Γ' ⊢ M1 : B[σ] }} ->
    {{ Δ ;; Γ' ⊢ M2 : B[σ] }} ->
    {{ Δ ;; Γ' ⊢ #1[σ,,M1,,M2] ≈ M1 : B[σ] }}.
Proof.
  intros.
  assert {{ Δ ;; Γ, B ⊢ B[Wk] : Type@i }} by mauto.
  assert {{ Δ ;; Γ' ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ;; Γ' ⊢ B[Wk][σ,,M1] : Type @ i }} by mauto 4.
  assert {{ Δ ;; Γ' ⊢ B[Wk][σ,,M1] ≈ B[σ] : Type @ i }}.
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

Lemma id_sub_lookup_var1 : forall Δ Γ M1 M2 B i,
    {{ Δ ;; Γ ⊢ B : Type@i }} ->
    {{ Δ ;; Γ ⊢ M1 : B }} ->
    {{ Δ ;; Γ ⊢ M2 : B }} ->
    {{ Δ ;; Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var1 | |];
    mauto 3.
Qed.

Lemma exp_eq_var_1_sub_q_sigma : forall {Δ Γ A i B j σ Γ'},
    {{ Δ ;; Γ' ⊢ B : Type@j }} ->
    {{ Δ ;; Γ', B ⊢ A : Type@i }} ->
    {{ Δ ;; Γ ⊢s σ : Γ' }} ->
    {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ ;; Γ' }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ] ⊢s q σ : Γ', B }} by mauto 2.
  assert {{ ⊢ Δ ;; Γ, B[σ] }} by mauto 3.
  assert {{ ⊢ Δ ;; Γ, B[σ], A[q σ] }} by mauto 3.
  assert {{ Δ ;; Γ', B ⊢ B[Wk] : Type@j }} by mauto 4.
  assert {{ Δ ;; Γ', B ⊢ #0 : B[Wk] }} by mauto 3.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] : Type@i }} by mauto 4.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢s q σ∘Wk : Γ', B }} by mauto 3.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #0 : A[q σ∘Wk] }} by mauto 3.
  assert {{ Δ ;; Γ ⊢ B[σ] : Type@j }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢s Wk : Γ, B[σ] }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ] ⊢ B[σ][Wk] : Type@j }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk] : Type@j }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk] : Type@j }} by (eapply exp_eq_sub_sub_compose_cong_typ; mauto 3).
  assert {{ Δ ;; Γ, B[σ],A[q σ] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk] : Type@j }} by (transitivity {{{ B[Wk][q σ][Wk] }}}; mauto 3).
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Δ ;; Γ, B[σ] ⊢s σ∘Wk : Γ' }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ] ⊢ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ∘Wk][Wk] }} by mauto 3.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ B[σ∘Wk][Wk] ≈ B[σ][Wk][Wk] : Type@j }} by mauto 4.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ][Wk][Wk] }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk][Wk] }} by (do 2 etransitivity; mauto 2).
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Δ ;; Γ, B[σ], A[q σ] ⊢ B[σ][Wk∘Wk] : Type@j }} by mauto 2.
  eapply wf_exp_eq_conv; mauto 2.
Qed.

(** *** Type Presuppositions *)

(* TODO: to prove this, we may need the weakening of both gctx and ctx, some of which 
   are stated below. the weakening of ctx, in the presence of explicit substitution,
   is less clear to me *)
Lemma presup_exp_typ : forall {Δ Γ M A},
    {{ Δ ;; Γ ⊢ M : A }} ->
    exists i, {{ Δ ;; Γ ⊢ A : Type@i }}.
Proof.
  induction 1; assert {{ ⊢ Δ ;; Γ }} by mauto 3; destruct_all; mauto 3.

  - enough {{ Δ ;; Γ ⊢s Id,,M : Γ, ℕ }}; mauto 3.

  - eexists; mauto 4 using lift_exp_max_left, lift_exp_max_right.

  - enough {{ Δ ;; Γ ⊢s Id,,N : Γ, A }}; mauto 3.

  - eexists; mauto 4 using lift_exp_max_left, lift_exp_max_right.

  - admit.

  - enough {{ Δ ;; Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 3.
    assert {{ Δ ;; Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ ;; Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
    assert {{ Δ ;; Γ, A, A[Wk] ⊢s Wk : Γ, A }} by mauto 4.
    assert {{ Δ ;; Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 3.
    assert {{ Δ ;; Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4).
    assert {{ Δ ;; Γ ⊢s Id,,M1 : Γ, A }} by mauto 3.
    assert {{ Δ ;; Γ ⊢ M2 : A[Wk][Id,,M1] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
    assert {{ Δ ;; Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }} by mauto 3.
    econstructor; [mautosolve 3 | mautosolve 3 |].
    eapply wf_conv; [| | symmetry]; mauto 3.
    transitivity {{{ Eq A[Wk∘Wk][Id,,M1,,M2] #1[Id,,M1,,M2] #0[Id,,M1,,M2] }}}.
    + econstructor; mauto 3 using id_sub_lookup_var0, id_sub_lookup_var1; eapply wf_conv; mauto 4.
    + assert {{ Δ ;; Γ ⊢ M2 : A }} by eassumption. (* re-assert to help search process *)
      assert {{ Δ ;; Γ ⊢ M1 : A[Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
      assert {{ Δ ;; Γ ⊢ M2 : A[Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
      econstructor; mauto 3 using id_sub_lookup_var0, id_sub_lookup_var1.
Admitted.

Lemma presup_exp : forall {Δ Γ M A},
    {{ Δ ;; Γ ⊢ M : A }} ->
    {{ ⊢ Δ ;; Γ }} /\ exists i, {{ Δ ;; Γ ⊢ A : Type@i }}.
Proof.
  mauto 4 using presup_exp_typ.
Qed.


(** *** New Properties for gctx *)

(* the weakening of gctx seems to need a mutual proof with multiple judgements *)

Lemma wf_weakening_gctx : 
    (forall Γ Δ, {{ ⊢ Δ ;; Γ }} -> forall Δ', {{ ⊢ Δ ,++ Δ' }}  -> {{ ⊢ Δ ,++ Δ' ;; Γ }}) /\
    (forall Δ Γ Γ', {{ Δ ⊢ Γ ⊆ Γ' }} -> forall Δ', {{ ⊢ Δ ,++ Δ' }} -> {{ Δ ,++ Δ' ⊢ Γ ⊆ Γ' }}) /\
    (forall Δ Γ A M, {{ Δ ;; Γ ⊢ M : A }} -> forall Δ', {{ ⊢ Δ ,++ Δ' }} -> {{ Δ ,++ Δ' ;; Γ ⊢ M : A }}) /\
    (forall Δ Γ M M' A, {{ Δ ;; Γ ⊢ M ≈ M' : A }} -> forall Δ', {{ ⊢ Δ ,++ Δ' }} -> {{ Δ ,++ Δ' ;; Γ ⊢ M ≈ M' : A }}) /\
    (forall Δ σ Γ Γ',  {{ Δ;; Γ ⊢s σ : Γ' }} -> forall Δ', {{ ⊢ Δ ,++ Δ' }} -> {{ Δ ,++ Δ' ;; Γ ⊢s σ : Γ' }}) /\
    (forall Δ σ σ' Γ Γ',  {{ Δ;; Γ ⊢s σ ≈ σ' : Γ' }} -> forall Δ', {{ ⊢ Δ ,++ Δ' }} -> {{ Δ ,++ Δ' ;; Γ ⊢s σ ≈ σ' : Γ' }}) /\
    (forall Δ Γ A A', {{ Δ ;; Γ ⊢ A ⊆ A' }} -> forall Δ', {{ ⊢ Δ ,++ Δ' }} -> {{ Δ ,++ Δ' ;; Γ ⊢ A ⊆ A' }}).
Proof.
Admitted.

(* this cannot be proved by induction in this form *)
Lemma gctx_presup_weakening_ctx : forall {Δ Γ A M},
    {{ Δ ;; ⋅ ⊢ M : A }} ->
    {{ ⊢ Δ ;; Γ }} ->
    {{ Δ ;; Γ ⊢ M : A }}.
Proof.
  intros. dependent induction H; mauto 3.
Admitted.

Lemma presup_gctx_lookup_typ_nil : forall {Δ A x M},
    {{ ⊢ Δ }} ->
    {{ `#x := [ M ] :: A ∈ Δ }} ->
    exists i, {{ Δ ;; ⋅ ⊢ A : Type@i }}.
Proof with mautosolve 4.
  intros * HΔ.
  induction 1; inversion_clear HΔ.
Admitted.

Lemma presup_gctx_lookup_typ : forall {Δ Γ A x M},
    {{ ⊢ Δ ;; Γ }} ->
    {{ `#x := [ M ] :: A ∈ Δ }} ->
    exists i, {{ Δ ;; Γ ⊢ A : Type@i }}.
Proof with mautosolve 4.
  intros * Hctx.
  induction 1.
  - admit.
  - admit.
Admitted.

(** *** Consistency Helper *)

(* TODO: needs a closer look, the conclusion could be possibly 
   strengthened to any axiom free Δ *)
Lemma no_closed_neutral : forall {A} {W : ne},
    ~ {{ ⋅ ;; ⋅ ⊢ W : A }}.
Proof.
  intros * H.
  dependent induction H; destruct W;
    try (simpl in *; congruence);
    autoinjections;
    intuition.
  inversion_by_head ctx_lookup.
Admitted.

#[export]
Hint Resolve no_closed_neutral : mctt.
