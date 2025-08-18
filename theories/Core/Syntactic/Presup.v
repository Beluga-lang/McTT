From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.

Lemma presup_exp_eq_natrec_cong_right : forall {Γ i A A' MZ' MS' M M'},
    {{ ⊢ Γ, ℕ }} ->
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ Γ, ℕ ⊢ A' : Type@i }} ->
    {{ Γ, ℕ ⊢ A ≈ A' : Type@i }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ MZ' : A[Id,,zero] }} ->
    {{ ⊢ Γ, ℕ, A }} ->
    {{ Γ, ℕ, A ⊢ MS' : A[Wk∘Wk,,succ #1] }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M' : ℕ }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,M' : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢ A[Id,,M] ≈ A'[Id,,M'] : Type@i }} by (transitivity {{{ A[Id,,M'] }}}; mauto 2).
  assert {{ Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢ MZ' : A'[Id,,zero] }} by mauto 4.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ MS' : A'[Wk∘Wk,,succ #1] }} by mauto 4.
  assert {{ ⊢ Γ, ℕ, A ≈ Γ, ℕ, A' }} by mauto 4.
  assert {{ Γ, ℕ, A' ⊢ MS' : A'[Wk∘Wk,,succ #1] }} by mauto 3.
  eapply wf_conv; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_natrec_cong_right : mctt.

Lemma presup_exp_eq_natrec_sub_left : forall {Γ σ Δ i A MZ MS M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ ⊢ Δ, ℕ }} ->
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Δ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⊢ Δ, ℕ, A }} ->
    {{ Δ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] : A[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M[σ] : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢ A[σ,,M[σ]] : Type@i }} by mauto 2.
  assert {{ Δ ⊢s Id,,M : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, ℕ }} by mauto 2.
  assert {{ Γ ⊢ A[(Id,,M)∘σ] ≈ A[σ,,M[σ]] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ A[Id,,M][σ] ≈ A[σ,,M[σ]] : Type@i }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_natrec_sub_left : mctt.

Lemma presup_exp_eq_natrec_sub_right : forall {Γ σ Δ i A MZ MS M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ ⊢ Δ, ℕ }} ->
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Δ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⊢ Δ, ℕ, A }} ->
    {{ Δ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢s q (q σ) : Δ, ℕ, A }} by mauto 2.
  assert {{ Γ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
  (* Possible lemma? *)
  assert (forall N, {{ Γ ⊢ N : ℕ }} -> {{ Γ ⊢ A[q σ][Id,,N] : Type@i }} /\ {{ Γ ⊢ A[q σ][Id,,N] ≈ A[σ,,N] : Type@i }}).
  {
    intros.
    assert {{ Γ ⊢ N : ℕ[σ] }} by mauto 3.
    assert {{ Γ ⊢s Id,,N : Γ, ℕ }} by mauto 3.
    assert {{ Γ ⊢s q σ∘(Id,,N) ≈ σ,,N : Δ, ℕ }} by mauto 3.
    assert {{ Γ ⊢s σ,,N : Δ, ℕ }} by mauto 2.
    assert {{ Γ ⊢ A[q σ∘(Id,,N)] ≈ A[σ,,N] : Type@i }} by mauto 3.
    split; mauto 3.
  }
  (* Assertion for M *)
  assert {{ Γ ⊢ M[σ] : ℕ }} by mauto 3.
  (* Assertion for type *)
  assert ({{ Γ ⊢ A[q σ][Id,,M[σ]] : Type@i }} /\ {{ Γ ⊢ A[q σ][Id,,M[σ]] ≈ A[σ,,M[σ]] : Type@i }}) as [] by mauto 3.
  (* Assertion for MZ *)
  assert {{ Δ ⊢ zero : ℕ }} by mauto 2.
  assert {{ Δ ⊢s Id,,zero : Δ, ℕ }} by mauto 2.
  assert {{ Γ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 2.
  assert {{ Γ ⊢s σ,,zero[σ] ≈ σ,,zero : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Id,,zero)∘σ ≈ σ,,zero : Δ, ℕ }} by mauto 3.
  assert ({{ Γ ⊢ A[q σ][Id,,zero] : Type@i }} /\ {{ Γ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Type@i }}) as [] by mauto 3.
  assert {{ Γ ⊢ A[(Id,,zero)∘σ] ≈ A[σ,,zero] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] : Type@i }} by (etransitivity; [| symmetry]; mauto 3).
  assert {{ Γ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by mauto 4.
  (* Assertion for MS *)
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Δ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] : Type@i }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by (eapply wf_conv; mauto 2).
  (* Final *)
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_natrec_sub_right : mctt.

Lemma presup_exp_eq_beta_succ_right : forall {Γ i A MZ MS M},
    {{ ⊢ Γ, ℕ }} ->
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⊢ Γ, ℕ, A }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  intros.
  set (WkWksucc := {{{ Wk∘Wk,,succ #1 }}}).
  set (recM := {{{ rec M return A | zero -> MZ | succ -> MS end }}}).
  set (IdMrecM := {{{ Id,,M,,recM }}}).
  (* Assertion for type *)
  assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 3.
  assert {{ Γ ⊢ recM : A[Id,,M] }} by mauto 4.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ ⊢s WkWksucc∘IdMrecM ≈ (Wk∘Wk)∘IdMrecM,,(succ #1)[IdMrecM] : Γ, ℕ }}
    by (eapply sub_eq_extend_compose_nat; mauto 3).
  assert {{ Γ ⊢s Id : Γ }} by mauto 2.
  assert {{ Γ ⊢s IdMrecM : Γ, ℕ, A }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM : Γ }} by mauto 2.
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM ≈ Wk∘(Wk∘IdMrecM) : Γ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 2.
  assert {{ Γ ⊢s Wk∘(Wk∘IdMrecM) ≈ Wk∘(Id,,M) : Γ }} by (econstructor; mauto 2).
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM ≈ Id : Γ }} by (etransitivity; mauto 3).
  assert {{ Γ ⊢ #1[IdMrecM] ≈ #0[Id,,M] : ℕ }} by mauto 3.
  assert {{ Γ ⊢ #1[IdMrecM] ≈ M : ℕ }} by mauto 3.
  assert {{ Γ ⊢ succ #1[IdMrecM] ≈ succ M : ℕ }} by mauto 2.
  assert {{ Γ ⊢ (succ #1)[IdMrecM] ≈ succ M : ℕ }} by (etransitivity; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM,,(succ #1)[IdMrecM] ≈ Id,,succ M : Γ, ℕ }} by mauto 2.
  assert {{ Γ ⊢s WkWksucc∘IdMrecM : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,succ M : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s WkWksucc∘IdMrecM ≈ Id,,succ M : Γ, ℕ }} by mauto 2.
  assert {{ Γ ⊢ A[WkWksucc∘IdMrecM] ≈ A[Id,,succ M] : Type@i }} by mauto 2.
  enough {{ Γ ⊢ A[WkWksucc][IdMrecM] ≈ A[Id,,succ M] : Type@i }}; [eapply wf_conv | etransitivity]; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_beta_succ_right : mctt.

Lemma presup_exp_eq_fn_cong_right : forall {Γ i A A' j B M'},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ B : Type@j }} ->
    {{ Γ, A ⊢ M' : B }} ->
    {{ Γ ⊢ λ A' M' : Π A B }}.
Proof.
  intros.
  assert {{ Γ ⊢ A : Type@(max i j) }} by mauto 2 using lift_exp_max_left.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i j) }} by mauto 2 using lift_exp_eq_max_left.
  assert {{ Γ, A ⊢ B : Type@(max i j) }} by mauto 2 using lift_exp_max_right.
  assert {{ Γ ⊢ Π A B ≈ Π A' B : Type@(max i j) }} by mauto 3.
  assert {{ Γ, A' ⊢ M' : B }} by mauto 4.
  assert {{ Γ ⊢ Π A B : Type@(max i j) }} by mauto 2.
  enough {{ Γ ⊢ λ A' M' : Π A' B }}; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_cong_right : mctt.

Lemma presup_exp_eq_fn_sub_right : forall {Γ σ Δ i A j B M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Type@j }} ->
    {{ Δ, A ⊢ M : B }} ->
    {{ Γ ⊢ λ A[σ] M[q σ] : (Π A B)[σ] }}.
Proof.
  intros.
  assert {{ Δ ⊢ A : Type@(max i j) }} by mauto 2 using lift_exp_max_left.
  assert {{ Δ, A ⊢ B : Type@(max i j) }} by mauto 2 using lift_exp_max_right.
  assert {{ Γ ⊢ A[σ] : Type@(max i j) }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ B[q σ] : Type@(max i j) }} by mauto 3.
  assert {{ Γ ⊢ Π A[σ] B[q σ] : Type@(max i j) }} by mauto 2.
  assert {{ Γ ⊢ Π A[σ] B[q σ] ≈ Π A[σ] B[q σ] : Type@(max i j) }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ M[q σ] : B[q σ] }} by mauto 3.
  assert {{ Γ ⊢ λ A[σ] M[q σ] : Π A[σ] B[q σ] }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_sub_right : mctt.

Lemma presup_exp_eq_app_cong_right : forall {Γ i A B M' N N'},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M' : Π A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ N' : A }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M' N' : B[Id,,N] }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id ≈ Id : Γ }} by mauto 2.
  assert {{ Γ ⊢ A ≈ A[Id] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ N ≈ N' : A[Id] }} by mauto 2.
  assert {{ Γ ⊢s Id,,N ≈ Id,,N' : Γ, A }} by mauto 2.
  assert {{ Γ ⊢ B[Id,,N] ≈ B[Id,,N'] : Type@i }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_cong_right : mctt.

Lemma presup_exp_eq_app_sub_left : forall {Γ σ Δ i A B M N},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Δ ⊢ M : Π A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : (Π A B)[σ] }} by mauto 3.
  assert {{ Γ ⊢ Π A[σ] B[q σ] : Type@i }} by mauto 4.
  assert {{ Γ ⊢ M[σ] : Π A[σ] B[q σ] }} by mauto 3.
  assert {{ Δ ⊢ N : A[Id] }} by mauto 2.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ Id∘σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, A }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢s σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ B[σ,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Type@i }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_left : mctt.

Lemma presup_exp_eq_app_sub_right : forall {Γ σ Δ i A B M N},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Δ ⊢ M : Π A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ B[q σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : Π A[σ] B[q σ] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) ≈ σ,,N[σ] : Δ, A }} by mauto 2.
  assert {{ Γ ⊢s Id,,N[σ] : Γ, A[σ] }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) : Δ, A }} by mauto 2.
  assert {{ Γ ⊢ B[q σ∘(Id,,N[σ])] ≈ B[σ,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] : Type@i }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_right : mctt.

Lemma presup_exp_eq_pi_eta_right : forall {Γ i A B M},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ λ A (M[Wk] #0) : Π A B }}.
Proof.
  intros.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢s q Wk : Γ, A }} by mauto 2.
  assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢ B[q Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A ⊢ M[Wk] : Π A[Wk] B[q Wk] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Γ, A ⊢s q Wk∘(Id,,#0) ≈ Id : Γ, A }} by (etransitivity; mauto 2).
  assert {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A ⊢ B[q Wk][Id,,#0] ≈ B[Id] : Type@i }} by (transitivity {{{ B[q Wk∘(Id,,#0)] }}}; mauto 3).
  econstructor; eauto.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_pi_eta_right : mctt.

Lemma presup_exp_eq_prop_eq_var0 : forall {Γ i A},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var0 : mctt.

Lemma presup_exp_eq_prop_eq_var1 : forall {Γ i A},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  eapply var_compose_subs; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var1 : mctt.

Lemma presup_exp_eq_prop_eq_wf : forall {Γ i A},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 3.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_wf : mctt.

Lemma presup_exp_eq_prop_eq_sub_helper2 : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 3.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[σ] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ M2[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σ,,M1[σ]] }} by mauto 3.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_sub_helper2 : mctt.

Lemma presup_exp_eq_prop_eq_typ_sub2_eq : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M1[σ],,M2[σ]] ≈ (Eq A M1 M2)[σ] : Type@i }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 3.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Γ ⊢ M1[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ] : Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σ,,M1[σ]] }} by mauto 3.
  assert {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢s Wk∘Wk : Δ }} by mauto 4.
  assert {{ Δ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘Wk][σ,,M1[σ],,M2[σ]] : Type@i }} by mauto 2.
  enough {{ Γ ⊢ Eq A[Wk∘Wk][σ,,M1[σ],,M2[σ]] #1[σ,,M1[σ],,M2[σ]] #0[σ,,M1[σ],,M2[σ]] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }}
    by (etransitivity; [| etransitivity]; [| eassumption |]; econstructor; mauto 2).
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  econstructor; mauto 2; eapply wf_exp_eq_conv; mauto 4 using sub_lookup_var0, sub_lookup_var1.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_typ_sub2_eq : mctt.

Lemma presup_exp_eq_prop_eq_sub_helper3 : forall {Γ σ Δ i A M1 M2 N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Δ ⊢ N : Eq A M1 M2 }} ->
    {{ Γ ⊢s σ,,M1[σ],,M2[σ],,N[σ] : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }} by mauto 3.
  assert {{ Δ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M1[σ],,M2[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ N[σ] : (Eq A[Wk∘Wk] #1 #0)[σ,,M1[σ],,M2[σ]] }} by (eapply wf_conv; mauto 3).
  mauto 3.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_sub_helper3 : mctt.

Lemma presup_exp_eq_prop_eq_id_sub_helper2 : forall {Γ i A M1 M2},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢s Id : Γ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M1 : Γ, A }} by mauto 2.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][Id,,M1] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2 : A[Wk][Id,,M1] }} by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_id_sub_helper2 : mctt.

Lemma presup_exp_eq_prop_eq_typ_id_sub2_eq : forall {Γ i A M1 M2},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,M1,,M2] ≈ Eq A M1 M2 : Type@i }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M1 : Γ, A }} by mauto 2.
  assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M1] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2 : A[Wk][Id,,M1] }} by mauto 3.
  assert {{ Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘Wk][Id,,M1,,M2] : Type@i }} by mauto 2.
  transitivity {{{ Eq A[Wk∘Wk][Id,,M1,,M2] #1[Id,,M1,,M2] #0[Id,,M1,,M2] }}}; [econstructor; mautosolve 2 |].
  econstructor; mauto 2; eapply wf_exp_eq_conv; mauto 4 using id_sub_lookup_var0, id_sub_lookup_var1.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_typ_id_sub2_eq : mctt.

Lemma presup_exp_eq_prop_eq_id_sub_helper3 : forall {Γ i A M1 M2 N},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢ N : Eq A M1 M2 }} ->
    {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,M1,,M2] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ N : (Eq A[Wk∘Wk] #1 #0)[Id,,M1,,M2] }} by (eapply wf_conv; mauto 3).
  mauto 3.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_id_sub_helper3 : mctt.

Lemma presup_exp_eq_refl_sub_right : forall {Γ σ Δ i A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ refl A[σ] M[σ] : (Eq A M M)[σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ (Eq A M M)[σ] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ (Eq A M M)[σ] ≈ Eq A[σ] M[σ] M[σ] : Type@i }} by mauto 3.
  eapply wf_conv; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_refl_sub_right : mctt.

Lemma presup_exp_eq_eqrec_sub_left : forall {Γ σ Δ i A M1 M2 j B N BR},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ ⊢ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} ->
    {{ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Δ ⊢ N : Eq A M1 M2 }} ->
    {{ Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[σ,,M1[σ],,M2[σ],,N[σ]] }}.
Proof.
  intros.
  set (IdM1 := {{{ Id,,M1 }}}).
  set (IdM1M2 := {{{ IdM1,,M2 }}}).
  set (σM1 := {{{ σ,,M1[σ] }}}).
  set (σM1M2 := {{{ σM1,,M2[σ] }}}).
  eapply wf_conv; mauto 3.
  transitivity {{{ B[(IdM1M2,,N)∘σ] }}}; [mauto 3 |].
  eapply exp_eq_sub_cong_typ2'; mauto 3.
  assert {{ Δ ⊢ (Eq A[Wk∘Wk] #1 #0)[IdM1M2] : Type@i }} by (eapply exp_sub_typ; mauto 2).
  assert {{ Δ ⊢ N : (Eq A[Wk∘Wk] #1 #0)[IdM1M2] }} by (eapply wf_conv; mauto 3).
  transitivity {{{ (IdM1M2∘σ),,N[σ] }}}; [econstructor; mautosolve 2 | symmetry].
  assert {{ Γ ⊢ N[σ] : (Eq A M1 M2)[σ] }} by mauto 2.
  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σM1M2] : Type@i }} by (eapply exp_sub_typ; mauto 2).
  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σM1M2] ≈ (Eq A M1 M2)[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ N[σ] : (Eq A[Wk∘Wk] #1 #0)[σM1M2] }} by mauto 3.
  enough {{ Γ ⊢s σM1M2 ≈ IdM1M2∘σ : Δ, A, A[Wk] }} by (econstructor; mauto 2).
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M1[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σM1] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σM1] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σM1] }} by (eapply wf_conv; mauto 2).
  assert {{ Δ ⊢ A[Wk][IdM1] : Type@i }} by mauto 3.
  assert {{ Δ ⊢ A[Wk][IdM1] ≈ A : Type@i }} by mauto 2.
  assert {{ Δ ⊢ M2 : A[Wk][IdM1] }} by (eapply wf_conv; mauto 2).
  transitivity {{{ (IdM1∘σ),,M2[σ] }}}; econstructor; mautosolve 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_eqrec_sub_left : mctt.

Lemma presup_exp_eq_eqrec_sub_right : forall {Γ σ Δ i A M1 M2 j B N BR},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ ⊢ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} ->
    {{ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Δ ⊢ N : Eq A M1 M2 }} ->
    {{ Γ ⊢ eqrec N[σ] as Eq A[σ] M1[σ] M2[σ] return B[q (q (q σ))] | refl -> BR[q σ] end : B[σ,,M1[σ],,M2[σ],,N[σ]] }}.
Proof.
  intros.
  assert {{ Δ ⊢s Id,,M1 : Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Δ, A, A[Wk] }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢s Wk∘Wk : Δ }} by mauto 3.
  assert {{ Δ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] : Type@i }} by (eapply exp_sub_typ; mauto 3).
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M1[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ M2[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σ,,M1[σ]] }} by mauto 3.
  assert {{ Γ ⊢s σ,,M1[σ] : Δ, A }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.

  assert {{ Δ, A, A[Wk] ⊢s Wk : Δ, A }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘Wk][σ,,M1[σ],,M2[σ]] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ N[σ] : (Eq A M1 M2)[σ] }} by mauto 2.
  assert {{ Γ ⊢ #1[σ,,M1[σ],,M2[σ]] ≈ M1[σ] : A[Wk∘Wk][σ,,M1[σ],,M2[σ]] }}
    by (eapply wf_exp_eq_conv; mauto 2 using sub_lookup_var1).
  assert {{ Γ ⊢ #0[σ,,M1[σ],,M2[σ]] ≈ M2[σ] : A[Wk∘Wk][σ,,M1[σ],,M2[σ]] }}
    by (eapply wf_exp_eq_conv; [eapply sub_lookup_var0 | |]; mauto 2).
  assert {{ Γ ⊢ N[σ] : (Eq A[Wk∘Wk] #1 #0)[σ,,M1[σ],,M2[σ]] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
  assert {{ Γ ⊢s σ,,M1[σ],,M2[σ],,N[σ] : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Γ, A[σ], A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢s Wk : Γ, A[σ] }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[σ][Wk∘Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ Eq A[σ][Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢ A[Wk][q σ] ≈ A[σ][Wk] : Type@i }} by mauto 3.
  assert {{ ⊢ Γ, A[σ], A[Wk][q σ] ≈ Γ, A[σ], A[σ][Wk] }} by (econstructor; mauto 3).
  assert {{ Γ, A[σ], A[σ][Wk] ⊢s q (q σ) : Δ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] ≈ A[σ][Wk∘Wk] : Type@i }}.
  {
    transitivity {{{ A[Wk][q σ][Wk] }}}; [mauto 3 |].
    transitivity {{{ A[σ][Wk][Wk] }}}; [| mauto 2].
    eapply exp_eq_sub_cong_typ1; mauto 3.
  }
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk∘Wk][q (q σ)] ≈ A[σ][Wk∘Wk] : Type@i }}.
  {
    transitivity {{{ A[Wk][q σ∘Wk] }}}; [| eassumption].
    transitivity {{{ A[Wk][Wk][q (q σ)] }}}; [eapply exp_eq_sub_cong_typ1; mauto 3 |].
    transitivity {{{ A[Wk][Wk∘q (q σ)] }}}; [mauto 2 |].
    eapply exp_eq_sub_cong_typ2'; mauto 3.
  }
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ Eq A[σ][Wk∘Wk] #0 #0 : Type@i }} by (econstructor; mauto 2).
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ (Eq A[Wk∘Wk] #1 #0)[q (q σ)] ≈ Eq A[σ][Wk∘Wk] #1 #0 : Type@i }}.
  {
    etransitivity; [econstructor; mauto 2 |].
    econstructor; mauto 2.
    - eapply wf_exp_eq_conv;
        [eapply ctxeq_exp_eq; [eassumption | eapply exp_eq_var_1_sub_q_sigma] | |];
        mauto 2.
    - eapply wf_exp_eq_conv; [econstructor | |]; mauto 2.
      + eapply wf_conv; mauto 2.
      + mauto 3.
  }
  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s q (q (q σ)) : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}
    by (eapply ctxeq_sub; [econstructor | eapply sub_q]; mauto 3).
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢s Id,,#0 : Γ, A[σ], A[σ][Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk∘Wk][Id,,#0] ≈ A[σ][Wk] : Type@i }}
    by (transitivity {{{ A[σ][Wk][Wk][Id,,#0] }}}; [symmetry |]; mauto 3).

  assert {{ Γ, A[σ] ⊢s Id,,#0,,refl A[σ][Wk] #0 : Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }}.
  {
    econstructor; mauto 2.
    eapply wf_conv; [econstructor | |]; mauto 2.
    symmetry.
    etransitivity; [econstructor; mauto 3 |].
    econstructor; eauto.
    - eapply wf_exp_eq_conv; mauto 2.
      transitivity {{{ #0[Id] }}}; mauto 2.
      eapply wf_exp_eq_conv; [econstructor | |]; mauto 3.
    - eapply wf_exp_eq_conv; [econstructor | |]; mauto 3.
      transitivity {{{ A[σ][Wk] }}}; mauto 3.
  }
  assert {{ Γ, A[σ] ⊢s q (q σ)∘(Id,,#0) ≈ q σ,,#0 : Δ, A, A[Wk] }}.
  {
    eapply sub_eq_q_sigma_id_extend; mauto 2.
    eapply wf_conv; mauto 2.
  }
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk∘Wk][Id,,#0] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ, A[σ] ⊢ #0[Id,,#0] ≈ #0 : A[σ][Wk][Id] }} by (econstructor; mauto 3).
  assert {{ Γ, A[σ] ⊢ #0[Id,,#0] ≈ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0[Id,,#0] ≈ #0 : A[σ][Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ, A[σ] ⊢ (Eq A[σ][Wk∘Wk] #0 #0)[Id,,#0] ≈ Eq A[σ][Wk] #0 #0 : Type@i }}
    by (etransitivity; econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢s (q (q σ)∘Wk)∘(Id,,#0,,refl A[σ][Wk] #0) : Δ, A, A[Wk] }}.
  {
    econstructor; [eassumption |].
    econstructor; mauto 3.
  }
  assert {{ ⊢ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s (q (q σ)∘Wk)∘(Id,,#0,,refl A[σ][Wk] #0) ≈ q (q σ)∘(Id,,#0) : Δ, A, A[Wk] }}.
  {
    transitivity {{{ q (q σ)∘(Wk∘(Id,,#0,,refl A[σ][Wk] #0)) }}}; [mauto 3 |].
    econstructor; mauto 2.
    eapply wf_sub_eq_p_extend with (A:={{{ Eq A[σ][Wk∘Wk] #0 #0 }}}); mauto 2.
    eapply wf_conv; mauto 2.
  }
  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s Wk : Γ, A[σ], A[σ][Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s (q (q σ)∘Wk)∘(Id,,#0,,refl A[σ][Wk] #0) ≈ q σ,,#0 : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk∘Wk][Id,,#0] ≈ A[Wk][q σ] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0 : A[Wk][q σ] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q σ,,#0] ≈ A[Wk][q σ] : Type@i }}
    by (transitivity {{{ A[Wk][Wk][q σ,,#0] }}}; [eapply exp_eq_sub_cong_typ1 |]; mauto 3).
  assert {{ Γ, A[σ] ⊢s q σ,,#0 : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q σ,,#0] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q σ,,#0] ≈ A[σ][Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0[q σ,,#0] ≈ #0 : A[σ][Wk] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ, A[σ] ⊢ #0[q σ,,#0] ≈ #0 : A[Wk∘Wk][q σ,,#0] }} by mauto 3.

  assert {{ Γ, A[σ] ⊢s σ∘Wk : Δ }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.

  assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #1[q σ,,#0] ≈ #0 : A[σ][Wk] }}
    by (eapply wf_exp_eq_conv; [eapply sub_lookup_var1 | |]; mauto 2).
  assert {{ Γ, A[σ] ⊢ #1[q σ,,#0] ≈ #0 : A[Wk∘Wk][q σ,,#0] }} by mauto 3.

  assert {{ Γ, A[σ] ⊢s q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) ≈ (q (q σ)∘(Id,,#0)),,refl A[σ][Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    etransitivity;
      [eapply wf_sub_eq_extend_compose; eauto; mauto 3 |].

    - eapply wf_conv; [mauto 2 | |].
      + mauto 3.
      + symmetry.
        transitivity {{{ (Eq A[Wk∘Wk] #1 #0)[q (q σ)][Wk] }}};
          [mautosolve 3 |].
        eapply exp_eq_sub_cong_typ1; mauto 2.
    - econstructor; mauto 2.
      eapply wf_exp_eq_conv; [| mautosolve 2 |].
      + econstructor; mauto 2.
        eapply wf_conv; [econstructor | |]; mauto 2.
      + etransitivity; mauto 2.
        symmetry.
        etransitivity;
          [eapply exp_eq_sub_cong_typ2'; mauto 2 | etransitivity];
          econstructor; mauto 2.
  }

  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q (q σ)∘(Id,,#0)] ≈ A[Wk][q σ] : Type@i }} by (etransitivity; mauto 3).
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q (q σ)∘(Id,,#0)] ≈ A[σ][Wk] : Type@i }} by mauto 2.

  assert {{ Γ, A[σ] ⊢ #0[q (q σ)∘(Id,,#0)] ≈ #0 : A[σ][Wk] }}.
  {
    transitivity {{{ #0[q σ,,#0] }}}; [| eassumption].
    eapply wf_exp_eq_conv; [econstructor; [| eassumption] | |]; mauto 3.
  }
  assert {{ Γ, A[σ] ⊢ #0[q (q σ)∘(Id,,#0)] ≈ #0 : A[Wk∘Wk][q (q σ)∘(Id,,#0)] }} by (eapply wf_exp_eq_conv; mauto 3).

  assert {{ Γ, A[σ] ⊢ #1[q (q σ)∘(Id,,#0)] ≈ #0 : A[σ][Wk] }}.
  {
    transitivity {{{ #1[q σ,,#0] }}}; [| eassumption].
    eapply wf_exp_eq_conv; [econstructor; [| eassumption] | |]; mauto 3.
  }
  assert {{ Γ, A[σ] ⊢ #1[q (q σ)∘(Id,,#0)] ≈ #0 : A[Wk∘Wk][q (q σ)∘(Id,,#0)] }} by (eapply wf_exp_eq_conv; mauto 3).

  assert {{ Γ, A[σ] ⊢s q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) ≈ q σ,,#0,,refl A[σ][Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    etransitivity; [eassumption |].
    econstructor; mauto 2.
    eapply exp_eq_refl.
    eapply wf_conv; [mauto 2 | mauto 3 |].
    symmetry.
    etransitivity; econstructor; mauto 2.
  }

  assert {{ Γ, A[σ] ⊢s Id∘q σ : Δ, A }} by mauto 3.
  assert {{ Γ, A[σ] ⊢s Id∘q σ ≈ q σ : Δ, A }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0[q σ] ≈ #0 : A[σ∘Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0[q σ] ≈ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0[q σ] ≈ #0 : A[Wk][q σ] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ, A[σ] ⊢s (Id,,#0)∘q σ : Δ, A, A[Wk] }} by (econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢s (Id,,#0)∘q σ ≈ q σ,,#0 : Δ, A, A[Wk] }}.
  {
    etransitivity; [eapply wf_sub_eq_extend_compose; mauto 2 |].
    econstructor; eauto.
    eapply wf_exp_eq_conv; mauto 2.
    eapply exp_eq_sub_cong_typ2'; mauto 2.
  }

  assert {{ Δ, A ⊢ A[Wk∘Wk][Id,,#0] ≈ A[Wk] : Type@i }}
    by (transitivity {{{ A[Wk][Wk][Id,,#0] }}}; [eapply exp_eq_sub_cong_typ1 |]; mauto 3).
  assert {{ Δ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk] }} by (eapply wf_exp_eq_conv; [econstructor | |]; mauto 2).
  assert {{ Δ, A ⊢ A[Wk∘Wk][Id,,#0] : Type@i }} by (eapply exp_sub_typ; mauto 2).
  assert {{ Δ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Δ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk] }}.
  {
    transitivity {{{ #0[Id] }}}; [| mauto 2].
    eapply wf_exp_eq_conv; [econstructor | |]; mauto 2.
    eapply wf_conv; mauto 3.
    symmetry; mauto 3.
  }
  assert {{ Δ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv; mauto 2).

  assert {{ Δ, A ⊢ refl A[Wk] #0 : (Eq A[Wk∘Wk] #1 #0)[Id,,#0] }}.
  {
    eapply wf_conv; [mautosolve 2 | |].
    - mauto 3.
    - symmetry.
      etransitivity; econstructor; mauto 2.
  }

  assert {{ Γ, A[σ] ⊢ (Eq A[Wk] #0 #0)[q σ] ≈ Eq A[σ][Wk] #0 #0 : Type@i }}
    by (etransitivity; [econstructor |]; mauto 2).
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][(Id,,#0)∘q σ] ≈ A[σ][Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #1[(Id,,#0)∘q σ] ≈ #0 : A[σ][Wk] }}
    by (transitivity {{{ #1[q σ,,#0] }}}; [eapply wf_exp_eq_conv |]; mauto 2; econstructor; mauto 3).
  assert {{ Γ, A[σ] ⊢ #1[(Id,,#0)∘q σ] ≈ #0 : A[Wk∘Wk][(Id,,#0)∘q σ] }} by (eapply wf_exp_eq_conv; mauto 2).

  assert {{ Γ, A[σ] ⊢ #0[(Id,,#0)∘q σ] ≈ #0 : A[σ][Wk] }}.
  {
    transitivity {{{ #0[q σ,,#0] }}}; [eapply wf_exp_eq_conv; [| | eassumption] |]; mauto 2.
    econstructor; mauto 3.
  }
  assert {{ Γ, A[σ] ⊢ #0[(Id,,#0)∘q σ] ≈ #0 : A[Wk∘Wk][(Id,,#0)∘q σ] }} by (eapply wf_exp_eq_conv; mauto 2).

  assert {{ Γ, A[σ] ⊢ (Eq A[Wk∘Wk] #1 #0)[(Id,,#0)∘q σ] ≈ Eq A[σ][Wk] #0 #0 : Type@i }}
    by (etransitivity; econstructor; mauto 2).

  assert {{ Γ, A[σ] ⊢s (Id,,#0,,refl A[Wk] #0)∘q σ ≈ q σ,,#0,,refl A[σ][Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    etransitivity; [eapply wf_sub_eq_extend_compose; mautosolve 2 |].
    econstructor; eauto.
    etransitivity.
    - eapply wf_exp_eq_conv; mauto 2.
      etransitivity; mauto 2.
    - eapply wf_exp_eq_conv; [econstructor | |]; mauto 2.
      etransitivity; mauto 2.
  }

  assert {{ Δ, A ⊢s Id,,#0,,refl A[Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by (econstructor; mauto 2).

  assert {{ Γ ⊢s Id,,M1[σ] : Γ, A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[σ][Wk][Id,,M1[σ]] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2[σ] : A[σ][Wk][Id,,M1[σ]] }} by (eapply wf_conv; revgoals; mauto 2).
  assert {{ Γ ⊢s Id,,M1[σ],,M2[σ] : Γ, A[σ], A[σ][Wk] }} by mauto 2.

  assert {{ Γ ⊢ A[σ][Wk∘Wk][Id,,M1[σ],,M2[σ]] ≈ A[σ] : Type@i }} by mauto 2.

  assert {{ Γ ⊢ #1[Id,,M1[σ],,M2[σ]] ≈ M1[σ] : A[σ] }} by mauto 2 using id_sub_lookup_var1.
  assert {{ Γ ⊢ #1[Id,,M1[σ],,M2[σ]] ≈ M1[σ] : A[σ][Wk∘Wk][Id,,M1[σ],,M2[σ]] }} by (eapply wf_exp_eq_conv; mauto 2).

  assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ]] ≈ M2[σ] : A[σ] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ]] ≈ M2[σ] : A[σ][Wk∘Wk][Id,,M1[σ],,M2[σ]] }} by (eapply wf_exp_eq_conv; mauto 2).

  assert {{ Γ ⊢ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,M1[σ],,M2[σ]] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }}
    by (etransitivity; econstructor; mauto 2).
  assert {{ Γ ⊢ (Eq A M1 M2)[σ] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ N[σ] : (Eq A[σ][Wk∘Wk] #1 #0)[Id,,M1[σ],,M2[σ]] }}
    by (eapply wf_conv; mauto 2; transitivity {{{ (Eq A M1 M2)[σ] }}}; [| etransitivity]; mauto 2).

  assert {{ Γ ⊢s Id,,M1[σ],,M2[σ],,N[σ] : Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }} by mauto 2.

  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s q (q σ)∘Wk : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢ (Eq A[Wk∘Wk] #1 #0)[q (q σ)∘Wk] ≈ (Eq A[σ][Wk∘Wk] #1 #0)[Wk] : Type@i }}
    by (etransitivity; [symmetry; eapply exp_eq_sub_compose_typ |]; mauto 2).

  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢ #0 : (Eq A[Wk∘Wk] #1 #0)[q (q σ)∘Wk] }} by (eapply wf_conv; mauto 2).

  assert {{ Γ ⊢s (q σ∘Wk)∘(Id,,M1[σ],,M2[σ]) : Δ, A }} by (econstructor; mauto 2).
  assert {{ Γ ⊢s (q σ∘Wk)∘(Id,,M1[σ],,M2[σ]) ≈ σ,,M1[σ] : Δ, A }}.
  {
    etransitivity; [eapply wf_sub_eq_compose_assoc; eassumption |].
    etransitivity;
      [eapply wf_sub_eq_compose_cong;
       [eapply wf_sub_eq_p_extend with (A:={{{ A[σ][Wk] }}}) | eapply sub_eq_refl] |];
      mauto 2.
  }

  assert {{ Γ ⊢ A[Wk][(q σ∘Wk)∘(Id,,M1[σ],,M2[σ])] ≈ A[σ] : Type@i }} by (transitivity {{{ A[Wk][σ,,M1[σ]] }}}; mauto 2).
  assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ]] ≈ M2[σ] : A[Wk][(q σ∘Wk)∘(Id,,M1[σ],,M2[σ])] }} by (eapply wf_exp_eq_conv; revgoals; mauto 2).

  assert {{ Γ, A[σ], A[σ][Wk] ⊢ #0 : A[Wk][q σ∘Wk] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ ⊢s q (q σ)∘(Id,,M1[σ],,M2[σ]) ≈ σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }}
    by (etransitivity; [eapply wf_sub_eq_extend_compose | econstructor]; mauto 2).
  assert {{ Γ ⊢s (q (q σ)∘Wk)∘(Id,,M1[σ],,M2[σ],,N[σ]) : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ ⊢s (q (q σ)∘Wk)∘(Id,,M1[σ],,M2[σ],,N[σ]) ≈ σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }}.
  {
    etransitivity; [eapply wf_sub_eq_compose_assoc; eassumption |].
    etransitivity;
      [eapply wf_sub_eq_compose_cong;
       [eapply wf_sub_eq_p_extend with (A:={{{ Eq A[σ][Wk∘Wk] #1 #0 }}}) | eapply sub_eq_refl] |];
      eassumption.
  }

  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M1[σ],,M2[σ]] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[(q (q σ)∘Wk)∘(Id,,M1[σ],,M2[σ],,N[σ])] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ #0[Id,,M1[σ],,M2[σ],,N[σ]] ≈ N[σ] : (Eq A[Wk∘Wk] #1 #0)[(q (q σ)∘Wk)∘(Id,,M1[σ],,M2[σ],,N[σ])] }}
    by (eapply wf_exp_eq_conv with (A:={{{ Eq A[σ] M1[σ] M2[σ] }}}); [econstructor | |]; mauto 3).
  assert {{ Γ ⊢s q (q (q σ))∘(Id,,M1[σ],,M2[σ],,N[σ]) ≈ σ,,M1[σ],,M2[σ],,N[σ] : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}
    by (etransitivity; mauto 2).

  assert {{ Γ, A[σ] ⊢s (Id,,#0,,refl A[Wk] #0)∘q σ ≈ q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}
    by (etransitivity; mauto 2).

  eapply wf_conv; [econstructor | |]; mauto 2; mauto 3.
  - eapply wf_conv; mauto 2; mauto 3.
  - etransitivity; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_eqrec_sub_right : mctt.

Lemma presup_exp_eq_refl_cong_right : forall {Γ i A A' M M'},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ refl A' M' : Eq A M M }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
  symmetry; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_refl_cong_right : mctt.

Lemma presup_exp_eq_eqrec_cong_right : forall {Γ i A A' M1 M1' M2 M2' j B B' BR BR' N N'},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M1' : A }} ->
    {{ Γ ⊢ M1 ≈ M1' : A }} ->
    {{ Γ ⊢ M2' : A }} ->
    {{ Γ ⊢ M2 ≈ M2' : A }} ->
    {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B' : Type@j }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B ≈ B' : Type@j }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ, A ⊢ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ, A ⊢ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊢ N : Eq A M1 M2 }} ->
    {{ Γ ⊢ N' : Eq A M1 M2 }} ->
    {{ Γ ⊢ N ≈ N' : Eq A M1 M2 }} ->
    {{ Γ ⊢ eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end : B[Id,,M1,,M2,,N] }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id,,M1 : Γ, A }} by mauto 2.
  assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A : Type@i }} by mauto 2.
  assert {{ Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘Wk][Id,,M1,,M2] ≈ A : Type@i }}.
  {
    eapply exp_eq_sub_compose_double_weaken_id_double_extend_typ; revgoals; eauto.
    eapply wf_conv; mauto 2.
  }
  assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
  assert {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : A[Wk∘Wk][Id,,M1,,M2] }}
    by (eapply wf_exp_eq_conv; mauto 2 using id_sub_lookup_var1).
  assert {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : A[Wk∘Wk][Id,,M1,,M2] }}
    by (eapply wf_exp_eq_conv; mauto 2 using id_sub_lookup_var0).
  assert {{ Γ ⊢ N : (Eq A[Wk∘Wk] #1 #0)[Id,,M1,,M2] }} by (eapply wf_conv; mauto 2; symmetry; mauto 2).
  assert {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
  assert {{ Γ ⊢ Eq A' M1' M2' : Type@i }} by (econstructor; mauto 2).
  assert {{ Γ ⊢ Eq A' M1' M2' ≈ Eq A M1 M2 : Type @ i }} by mauto 3.

  assert {{ ⊢ Γ, A ≈ Γ, A' }} by mauto 3.
  assert {{ Γ, A ⊢ A'[Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A' ⊢ A'[Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A ⊢ A[Wk] ≈ A'[Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A' ⊢ A[Wk] ≈ A'[Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] ≈ Γ, A', A'[Wk] }} by mauto 3.

  assert {{ Γ, A', A'[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
  assert {{ Γ, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3).
  assert {{ Γ, A, A[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Type@i }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 ≈ Eq A'[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3).

  assert {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Γ, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }} by mauto 3.

  assert {{ Γ, A ⊢ Eq A[Wk] #0 #0 : Type@i }} by (econstructor; mauto 2).
  assert {{ Γ, A ⊢ Eq A'[Wk] #0 #0 ≈ Eq A[Wk] #0 #0 : Type@i }} by (econstructor; mauto 3).

  assert {{ Γ, A ⊢ refl A'[Wk] #0 : Eq A[Wk] #0 #0 }} by (eapply wf_conv; [econstructor | |]; mauto 3).
  assert {{ Γ, A ⊢ refl A[Wk] #0 : Eq A[Wk] #0 #0 }} by mauto 3.
  assert {{ Γ, A ⊢ refl A[Wk] #0 ≈ refl A'[Wk] #0 : Eq A[Wk] #0 #0 }} by mauto 3.
  assert {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }} by mauto 2.
  assert {{ Γ, A ⊢s Wk∘(Id,,#0) : Γ, A }} by (econstructor; mauto 2).
  assert {{ Γ, A ⊢ A[Wk∘Wk][Id,,#0] ≈ A[Wk] : Type@i }}
    by (transitivity {{{ A[Wk][Wk][Id,,#0] }}}; [eapply exp_eq_sub_cong_typ1; [symmetry |] |]; mauto 3).
  assert {{ Γ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk] }}.
  {
    transitivity {{{ #0[Id] }}}.
    - eapply wf_exp_eq_conv;
        [eapply wf_exp_eq_var_S_sub with (A:={{{ A[Wk] }}}) | |];
        mauto 3.
    - mauto 3.
  }
  assert {{ Γ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk] }}.
  {
    eapply wf_exp_eq_conv;
      [eapply wf_exp_eq_var_0_sub with (A:={{{ A[Wk] }}}) | |];
      mauto 3.
  }
  assert {{ Γ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }} by (etransitivity; econstructor; mauto 2).
  assert {{ Γ, A ⊢ refl A'[Wk] #0 : (Eq A[Wk∘Wk] #1 #0)[Id,,#0] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ, A ⊢ refl A[Wk] #0 : (Eq A[Wk∘Wk] #1 #0)[Id,,#0] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ, A ⊢s Id,,#0,,refl A'[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
  assert {{ Γ, A ⊢s Id,,#0,,refl A[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.

  assert {{ Γ, A ⊢s Id,,#0,,refl A[Wk] #0 ≈ Id,,#0,,refl A'[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}
    by (econstructor; [| | eapply wf_exp_eq_conv]; mauto 2).

  assert {{ Γ, A ⊢ B[Id,,#0,,refl A[Wk] #0] ≈ B'[Id,,#0,,refl A'[Wk] #0] : Type@j }}
    by (etransitivity; [eapply exp_eq_sub_cong_typ2' | eapply exp_eq_sub_cong_typ1]; mauto 2).

  assert {{ Γ ⊢ M1 ≈ M1' : A[Id] }} by (eapply wf_exp_eq_conv; mauto 3).
  assert {{ Γ ⊢s Id,,M1 ≈ Id,,M1' : Γ, A }} by mauto 2.
  assert {{ Γ ⊢ M2 ≈ M2' : A[Wk][Id,,M1] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ ⊢s Id,,M1,,M2 ≈ Id,,M1',,M2' : Γ, A, A[Wk] }} by mauto 2.

  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,M1,,M2] ≈ Eq A M1 M2 : Type@i }} by mauto 2.
  assert {{ Γ ⊢s Id,,M1,,M2,,N ≈ Id,,M1',,M2',,N' : Γ, A, A[Wk], Eq (A[Wk∘Wk]) #1 #0 }}
    by (econstructor; [| | eapply wf_exp_eq_conv]; mauto 2).

  assert {{ Γ ⊢s Id,,M1' : Γ, A }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M1'] ≈ A : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2' : A[Wk][Id,,M1'] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ ⊢s Id,,M1',,M2' : Γ, A, A[Wk] }} by mauto 2.

  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,M1',,M2'] ≈ Eq A M1 M2 : Type@i }}
    by (transitivity {{{ Eq A M1' M2' }}}; [| econstructor]; mauto 2).
  assert {{ Γ ⊢ N' : (Eq A[Wk∘Wk] #1 #0)[Id,,M1',,M2'] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ ⊢s Id,,M1',,M2',,N' : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.

  eapply wf_conv;
    [econstructor; mauto 3 | mauto 2 | ].
  - eapply ctxeq_exp; eauto.
    eapply wf_conv; mauto 2.
  - etransitivity; [eapply exp_eq_sub_cong_typ2' | eapply exp_eq_sub_cong_typ1]; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_eqrec_cong_right : mctt.

Lemma presup_exp_eq_eqrec_beta_right : forall {Γ i A M j B BR},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊢ BR[Id,,M] : B[Id,,M,,M,,refl A M] }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id,,M : Γ, A }} by mauto 2.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M] ≈ A : Type@i }} by mauto 2.
  assert {{ Γ ⊢s Id,,M,,M : Γ, A, A[Wk] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘Wk][Id,,M,,M] ≈ A : Type@i }}.
  {
    eapply exp_eq_sub_compose_double_weaken_id_double_extend_typ; mauto 2.
    eapply wf_conv; mauto 2.
  }
  assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
  assert {{ Γ ⊢ refl A M : Eq A M M }} by mauto 2.
  assert {{ Γ ⊢ refl A M : (Eq A[Wk∘Wk] #1 #0)[Id,,M,,M] }} by (eapply wf_conv; mauto 2; symmetry; mauto 3).
  assert {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} by mauto 4.

  assert {{ Γ, A ⊢ refl A[Wk] #0 : Eq A[Wk] #0 #0 }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }} by mauto 2.
  assert {{ Γ, A ⊢s Wk∘(Id,,#0) : Γ, A }} by mauto 2.
  assert {{ Γ, A ⊢ A[Wk∘Wk][Id,,#0] ≈ A[Wk] : Type@i }}
    by (transitivity {{{ A[Wk][Wk][Id,,#0] }}}; [symmetry |]; mauto 4).
  assert {{ Γ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk] }}.
  {
    transitivity {{{ #0[Id] }}}.
    - eapply wf_exp_eq_conv;
        [eapply wf_exp_eq_var_S_sub with (A:={{{ A[Wk] }}}) | |];
        mauto 3.
    - mauto 3.
  }
  assert {{ Γ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk] }}
    by (eapply wf_exp_eq_conv; [eapply wf_exp_eq_var_0_sub with (A:={{{ A[Wk] }}}) | |]; mauto 3).
  assert {{ Γ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv; mauto 2).
  assert {{ Γ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }}
    by (etransitivity; econstructor; mauto 2).
  assert {{ Γ, A ⊢ refl A[Wk] #0 : (Eq A[Wk∘Wk] #1 #0)[Id,,#0] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ, A ⊢s Id,,#0,,refl A[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.

  assert {{ Γ, A ⊢ #0 : A[Wk][Id] }} by mauto 3.

  assert {{ Γ ⊢ A[Wk][Id∘(Id,,M)] ≈ A : Type@i }}.
  {
    transitivity {{{ A[Wk][Id,,M] }}}; mauto 3.
    eapply exp_eq_sub_cong_typ2'; mauto 3.
  }
  assert {{ Γ ⊢s Id : Γ }} by mauto 3.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A }}
    by (eapply wf_exp_eq_conv with (A:={{{ A[Id] }}}); mauto 3).
  assert {{ Γ ⊢ A[Wk][Id∘(Id,,M)] : Type@i }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[Wk][Id∘(Id,,M)] }} by mauto 3.

  assert {{ Γ ⊢s Id∘(Id,,M),,#0[Id,,M] ≈ Id,,M,,M : (Γ, A), A[Wk] }} by mauto 3.
  assert {{ Γ ⊢s (Id,,#0)∘(Id,,M) ≈ Id,,M,,M : (Γ, A), A[Wk] }}
    by (etransitivity; [eapply wf_sub_eq_extend_compose |]; mauto 2).

  assert {{ Γ ⊢ #1[Id,,M,,M] ≈ M : A }} by mauto 2 using id_sub_lookup_var1.
  assert {{ Γ ⊢s Wk∘(Id,,M,,M) : Γ, A }} by (eapply wf_sub_conv; mauto 2).
  assert {{ Γ ⊢s Wk∘(Id,,M,,M) ≈ Id,,M : Γ, A }} by (econstructor; [| | eapply wf_conv]; mauto 2).
  assert {{ Γ ⊢ #1[Id,,M,,M] ≈ M : A[Wk∘Wk][Id,,M,,M] }} by (eapply wf_exp_eq_conv; mauto 2).

  assert {{ Γ ⊢ #0[Id,,M,,M] ≈ M : A }} by mauto 2 using id_sub_lookup_var0.
  assert {{ Γ ⊢ #0[Id,,M,,M] ≈ M : A[Wk∘Wk][Id,,M,,M] }} by (eapply wf_exp_eq_conv; mauto 2).

  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[(Id,,#0)∘(Id,,M)] ≈ Eq A M M : Type@i }}
    by (etransitivity; [eapply exp_eq_sub_cong_typ2' | ]; mauto 2).

  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0][Id,,M] ≈ Eq A M M : Type@i }} by (etransitivity; [mauto 4 | mauto 3]).
  assert {{ Γ ⊢ Eq A M M : Type@i }} by mauto 2.

  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[Wk][Id,,M] }} by (eapply wf_exp_eq_conv with (A := A); mauto 2).

  assert {{ Γ ⊢ (refl A[Wk] #0)[Id,,M] ≈ refl A M : Eq A M M }}.
  {
    etransitivity.
    - eapply wf_exp_eq_conv; [eapply wf_exp_eq_refl_sub | |]; mauto 4.
    - eapply wf_exp_eq_conv; [econstructor | | econstructor]; mauto 3.
  }

  assert {{ Γ ⊢ (refl A[Wk] #0)[Id,,M] ≈ refl A M : (Eq A[Wk∘Wk] #1 #0)[(Id,,#0)∘(Id,,M)] }}
    by (eapply wf_exp_eq_conv; mauto 3).

  eapply wf_conv; mauto 3.
  etransitivity.
  - eapply exp_eq_sub_compose_typ; mauto 2.
  - symmetry.
    eapply exp_eq_sub_cong_typ2'; mauto 2.
    symmetry.
    etransitivity;
      [eapply wf_sub_eq_extend_compose |];
      mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_eqrec_beta_right : mctt.

Lemma presup_exp_eq_var_0_sub_left : forall {Γ σ Δ i A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ #0[σ,,M] : A[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 2.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_0_sub_left : mctt.

Lemma presup_exp_eq_var_S_sub_left : forall {Γ σ Δ i A M B x},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #x : B ∈ Δ }} ->
    {{ Γ ⊢ #(S x)[σ,,M] : B[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert (exists j, {{ Δ ⊢ B : Type@j }}) as [j] by mauto 2.
  assert {{ Δ, A ⊢ #(S x) : B[Wk] }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_S_sub_left : mctt.

Lemma presup_exp_eq_sub_cong_right : forall {Γ σ σ' Δ i A M M'},
    {{ ⊢ Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Δ ⊢ M' : A }} ->
    {{ Δ ⊢ M ≈ M' : A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ' : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M'[σ'] : A[σ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 2.
  eapply exp_eq_sub_cong_typ2'; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_cong_right : mctt.

Lemma presup_exp_eq_sub_compose_right : forall {Γ τ Γ' σ Γ'' i A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ ⊢ Γ'' }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A : Type@i }} ->
    {{ Γ'' ⊢ M : A }} ->
    {{ Γ ⊢ M[σ][τ] : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_compose_right : mctt.

#[local]
Ltac gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      let HAi := fresh "HAi" in
      pose proof presup_exp_eq _ _ _ _ H as [HΓ [HM [HN [i HAi]]]]
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub_eq _ _ _ _ H as [HΓ [Hσ [Hτ HΔ]]]
  | {{ ^?Γ ⊢ ^?M ⊆ ^?N }} =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      pose proof presup_subtyp _ _ _ H as [HΓ [i [HM HN]]]
  end.

Lemma presup_exp_eq : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ exists i, {{ Γ ⊢ A : Type@i }}
with presup_sub_eq : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}
with presup_subtyp : forall {Γ M M'}, {{ Γ ⊢ M ⊆ M' }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ M : Type@i }} /\ {{ Γ ⊢ M' : Type@i }}.
Proof with mautosolve 4.
  1: set (WkWksucc := {{{ Wk∘Wk ,, succ #1 }}}).
  all: inversion_clear 1;
    (on_all_hyp: gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp);
    gen_core_presups;
    clear presup_exp_eq presup_sub_eq presup_subtyp;
    repeat split; try mautosolve 3;
    try (eexists; unshelve solve [mauto 4 using lift_exp_max_left, lift_exp_max_right]; constructor).

  all: try (econstructor; mautosolve 4).

  (** presup_exp_eq cases *)
  - eexists; eapply exp_sub_typ; mauto 4 using lift_exp_max_left, lift_exp_max_right.

  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.

  (** presup_sub_eq cases *)
  - econstructor; mauto 3.
    eapply wf_conv...

  - enough {{ Γ ⊢ #0[σ] : A[Wk∘σ] }} by mauto 4.
    eapply wf_conv...

  (** presup_subtyp cases *)
  - exists (max (S i) (S j)); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

Ltac gen_presup H := gen_presup_IH @presup_exp_eq @presup_sub_eq @presup_subtyp H + gen_core_presup H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
