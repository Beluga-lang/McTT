From Coq Require Import Setoid.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CoreInversions Presup.
Import Syntax_Notations.

Add Parametric Morphism i Γ : (wf_exp Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> iff as wf_exp_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups...
Qed.

Add Parametric Morphism i Γ : (wf_exp_eq Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups...
Qed.

Add Parametric Morphism Γ i : (wf_subtyp Γ)
    with signature (wf_exp_eq Γ {{{ Type@i }}}) ==> eq ==> iff as wf_subtyp_morphism_iff1.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 4.
Qed.

Add Parametric Morphism Γ j : (wf_subtyp Γ)
    with signature eq ==> (wf_exp_eq Γ {{{ Type@j }}}) ==> iff as wf_subtyp_morphism_iff2.
Proof.
  split; intros; gen_presups;
    etransitivity; mauto 3.
Qed.

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.

Corollary wf_subtyp_refl' : forall Γ M M' i,
    {{ Γ ⊢ M ≈ M' : Type@i }} ->
    {{ Γ ⊢ M ⊆ M' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_refl' : mctt.
#[export]
Remove Hints wf_subtyp_refl : mctt.

Corollary wf_conv' : forall Γ M A i A',
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv' : mctt.
#[export]
Remove Hints wf_conv : mctt.

Corollary wf_exp_eq_conv' : forall Γ M M' A A' i,
   {{ Γ ⊢ M ≈ M' : A }} ->
   {{ Γ ⊢ A ≈ A' : Type@i }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv' : mctt.
#[export]
Remove Hints wf_exp_eq_conv : mctt.

Corollary wf_ctx_eq_extend' : forall {Γ Δ A A' i},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ ⊢ Γ, A ≈ Δ, A' }}.
Proof.
  intros.
  assert {{ Δ ⊢ A ≈ A' : Type@i }} by mauto.
  gen_presups.
  mautosolve 4.
Qed.

#[export]
Hint Resolve wf_ctx_eq_extend' : mctt.
#[export]
Remove Hints wf_ctx_eq_extend : mctt.

Corollary wf_nat' : forall {Γ i},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ ℕ : Type@i }}.
Proof.
  intros.
  assert (0 <= i) by lia.
  mauto.
Qed.

#[export]
Hint Resolve wf_nat' : mctt.
#[export]
Remove Hints wf_nat : mctt.

Corollary wf_natrec' : forall {Γ A MZ MS M},
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_natrec' : mctt.
#[export]
Remove Hints wf_natrec : mctt.

Corollary wf_pi_max : forall {Γ A i B j},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A ⊢ B : Type@j }} ->
    {{ Γ ⊢ Π A B : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Γ ⊢ A : Type@(max i j) }} by mauto using lift_exp_max_left.
  assert {{ Γ, A ⊢ B : Type@(max i j) }} by mauto using lift_exp_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_pi_max : mctt.

Corollary wf_fn' : forall {Γ A M B},
    {{ Γ, A ⊢ M : B }} ->
    {{ Γ ⊢ λ A M : Π A B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_fn' : mctt.
#[export]
Remove Hints wf_fn : mctt.

Corollary wf_app' : forall {Γ M N A B},
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M N : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_app' : mctt.
#[export]
Remove Hints wf_app : mctt.

Lemma wf_exp_eq_typ_sub' : forall Γ σ Δ i j,
    {{ Γ ⊢s σ : Δ }} ->
    i < j ->
    {{ Γ ⊢ Type@i[σ] ≈ Type@i : Type@j }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_exp_eq_typ_sub' : mctt.

#[export]
Hint Rewrite -> wf_exp_eq_typ_sub' using solve [lia | mauto 3] : mctt.

Corollary wf_exp_eq_nat_sub' : forall Γ σ Δ i,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ ℕ[σ] ≈ ℕ : Type@i }}.
Proof.
  intros.
  assert (0 <= i) by lia.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_sub : mctt.

#[export]
Hint Rewrite -> wf_exp_eq_nat_sub' using mautosolve 3 : mctt.

Corollary wf_exp_eq_natrec_cong' : forall {Γ A A' i MZ MZ' MS MS' M M'},
    {{ Γ, ℕ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mctt.

Corollary wf_exp_eq_natrec_sub' : forall {Γ σ Δ A MZ MS M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_sub' : mctt.
#[export]
Remove Hints wf_exp_eq_natrec_sub : mctt.

Corollary wf_exp_eq_nat_beta_zero' : forall {Γ A MZ MS},
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mctt.

Corollary wf_exp_eq_nat_beta_succ' : forall {Γ A MZ MS M},
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mctt.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mctt.

Corollary wf_exp_eq_pi_sub_max : forall {Γ σ Δ A i B j},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ, A ⊢ B : Type@j }} ->
    {{ Γ ⊢ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Δ ⊢ A : Type@(max i j) }} by mauto using lift_exp_max_left.
  assert {{ Δ, A ⊢ B : Type@(max i j) }} by mauto using lift_exp_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_sub_max : mctt.

Corollary wf_exp_eq_pi_cong' : forall {Γ A A' B B' i},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ B ≈ B' : Type@i }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_cong : mctt.

Corollary wf_exp_eq_pi_cong_max : forall {Γ A A' i B B' j},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ B ≈ B' : Type@j }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i j) }} by eauto using lift_exp_eq_max_left.
  assert {{ Γ, A ⊢ B ≈ B' : Type@(max i j) }} by eauto using lift_exp_eq_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mctt.

Corollary wf_exp_eq_fn_cong' : forall {Γ A A' i B M M'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ M ≈ M' : B }} ->
    {{ Γ ⊢ λ A M ≈ λ A' M' : Π A B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_cong : mctt.

Corollary wf_exp_eq_fn_sub' : forall {Γ σ Δ A M B},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ M : B }} ->
    {{ Γ ⊢ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_sub' : mctt.
#[export]
Remove Hints wf_exp_eq_fn_sub : mctt.

Corollary wf_exp_eq_app_cong' : forall {Γ A B M M' N N'},
    {{ Γ ⊢ M ≈ M' : Π A B }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_app_cong : mctt.

Corollary wf_exp_eq_app_sub' : forall {Γ σ Δ A B M N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : Π A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Δ ⊢ A : Type@i }} /\ {{ Δ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_sub' : mctt.
#[export]
Remove Hints wf_exp_eq_app_sub : mctt.

Corollary wf_exp_eq_pi_beta' : forall {Γ A B M N},
    {{ Γ, A ⊢ M : B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert {{ Γ ⊢ A : Type@i }} by (eapply lift_exp_max_left; mauto 3)).
  exvar nat ltac:(fun i => assert {{ Γ, A ⊢ B : Type@i }} by (eapply lift_exp_max_right; mauto 3)).
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_beta : mctt.

Corollary wf_exp_eq_pi_eta' : forall {Γ A B M},
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ M ≈ λ A (M[Wk] #0) : Π A B }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_eta' : mctt.
#[export]
Remove Hints wf_exp_eq_pi_eta : mctt.

Lemma wf_subtyp_pi' : forall Γ A A' B B' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A' ⊢ B ⊆ B' }} ->
    {{ Γ ⊢ Π A B ⊆ Π A' B' }}.
Proof.
  intros. gen_presups.
  eapply wf_subtyp_pi with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right, lift_exp_eq_max_left.
  eapply ctxeq_exp; [ | mauto 3 using lift_exp_max_right].
  mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mctt.
#[export]
Remove Hints wf_subtyp_pi : mctt.

Corollary wf_exp_eq_sigma_cong' : forall {Γ A A' B B' i},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ B ≈ B' : Type@i }} ->
    {{ Γ ⊢ Σ A B ≈ Σ A' B' : Type@i }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_sigma_cong' : mctt.
#[export]
Remove Hints wf_exp_eq_sigma_cong : mctt.

Corollary wf_exp_eq_sigma_cong_max : forall {Γ A A' i B B' j},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ B ≈ B' : Type@j }} ->
    {{ Γ ⊢ Σ A B ≈ Σ A' B' : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i j) }} by eauto using lift_exp_eq_max_left.
  assert {{ Γ, A ⊢ B ≈ B' : Type@(max i j) }} by eauto using lift_exp_eq_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mctt.

Lemma wf_subtyp_sigma' : forall Γ A A' B B' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A' ⊢ B ⊆ B' }} ->
    {{ Γ ⊢ Σ A B ⊆ Σ A' B' }}.
Proof.
  intros. gen_presups.
  eapply wf_subtyp_sigma with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right, lift_exp_eq_max_left.
  eapply ctxeq_exp; [ | mauto 3 using lift_exp_max_right].
  mauto 4.
Qed.

#[export]
Hint Resolve wf_subtyp_sigma' : mctt.
#[export]
Remove Hints wf_subtyp_sigma : mctt.

Lemma wf_exp_eq_refl_sub' : forall Γ Δ σ A M,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ (refl A M)[σ] ≈ refl A[σ] M[σ] : (Eq A M M)[σ] }}.
Proof.
  impl_opt_constructor.
Qed.


Lemma wf_exp_eq_eqrec_cong' : forall {Γ A A' M1 M1' M2 M2' B B' BR BR' M M' i j},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M1 ≈ M1' : A }} ->
    {{ Γ ⊢ M2 ≈ M2' : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B ≈ B' : Type@j }} ->
    {{ Γ, A ⊢ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊢ M ≈ M' : Eq A M1 M2 }} ->
    {{ Γ ⊢ eqrec M as Eq A M1 M2 return B | refl -> BR end ≈ eqrec M' as Eq A' M1' M2' return B' | refl -> BR' end : B[Id,,M1,,M2,,M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_refl_sub' : mctt.
#[export]
Remove Hints wf_exp_eq_refl_sub : mctt.
