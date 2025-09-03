From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Algorithmic.Subtyping Require Export Lemmas.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import Consequences.Rules.
From Mctt.Core.Semantic Require Import Consequences.
From Mctt.Core.Soundness Require Import EqualityCases.
From Mctt.Frontend Require Import Elaborator.
Import Domain_Notations.

Lemma functional_alg_type_infer : forall {Γ A A' M},
    {{ Γ ⊢a M ⟹ A }} ->
    {{ Γ ⊢a M ⟹ A' }} ->
    A = A'.
Proof.
  intros * HM1 HM2. gen A'.
  induction HM1; intros;
    inversion_clear HM2;
    functional_nbe_rewrite_clear;
    f_equiv;
    try reflexivity;
    intuition.
  - assert (n{{{ Type@i }}} = n{{{ Type@i0 }}}) as [= <-] by intuition.
    assert (n{{{ Type@j }}} = n{{{ Type@j0 }}}) as [= <-] by intuition.
    reflexivity.
  - assert (n{{{ Π A B }}} = n{{{ Π A0 B0 }}}) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (n{{{ Type@i }}} = n{{{ Type@i0 }}}) as [= <-] by intuition.
    assert (n{{{ Type@j }}} = n{{{ Type@j0 }}}) as [= <-] by intuition.
    reflexivity.
  - assert (n{{{ Σ A B }}} = n{{{ Σ A' B0 }}}) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (n{{{ Σ A B }}} = n{{{ Σ A0 B0 }}}) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (n{{{ Type@i }}} = n{{{ Type@i0 }}}) as [= <-] by intuition.
    reflexivity.
  - assert (A = A0) as <- by mauto using functional_ctx_lookup.
    functional_nbe_rewrite_clear.
    reflexivity.
Qed.

#[local]
Hint Resolve functional_alg_type_infer : mctt.

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ ^?Γ ⊢a ^?M ⟹ ^?A1 }}, H2 : {{ ^?Γ ⊢a ^?M ⟹ ^?A2 }} |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2 using functional_alg_type_infer] | tactic_error A2 A1]; clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.

Lemma alg_type_sound :
  (forall {Γ A M}, {{ Γ ⊢a M ⟸ A }} -> {{ ⊢ Γ }} -> forall i, {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }}) /\
    (forall {Γ A M}, {{ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}).
Proof.
  apply alg_type_mut_ind; intros; try mautosolve 4.
  - assert {{ Γ ⊢ M : A }} by mauto 3.
    assert (exists i, {{ Γ ⊢ A : Type@i }}) as [j] by (gen_presups; eauto 2).
    assert {{ Γ ⊢ A : Type@(max i j) }} by mauto 3 using lift_exp_max_right.
    assert {{ Γ ⊢ B : Type@(max i j) }} by mauto 3 using lift_exp_max_left.
    assert {{ Γ ⊢ A ⊆ B }} by mauto 2 using alg_subtyping_sound.
    mauto 3.
  - assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 2.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, ℕ, A }} by mauto 3.
    assert {{ Γ ⊢ M : ℕ }} by mauto 2.
    assert {{ Γ ⊢ A[Id,,zero] : Type@i }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Type@i }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,M] ≈ B : Type@i }} as <- by mauto 4 using soundness_ty'.
    mauto 4.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, A }} by mauto 3.
    mauto 4.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 2 using soundness_ty'.
    assert {{ Γ, A ⊢ M : B }} by mauto 2.
    assert (exists j, {{ Γ, A ⊢ B : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert {{ Γ ⊢ Π A B ≈ Π C B : Type@(max i j) }} as <- by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ M : Π A B }} by mauto 2.
    assert (exists i, {{ Γ ⊢ Π A B : Type@i }}) as [i] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, ^(A : exp) ⊢ B : Type@i }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,N] ≈ C : Type@i }} as <- by mauto 4 using soundness_ty'.
    mauto 3.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, A }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A : Type@i }} by (gen_presups; eauto 2).
    assert {{ Γ ⊢ A ≈ A' : Type@i }} by mauto 2 using soundness_ty'.
    assert {{ Γ ⊢s Id,,M1 : Γ , A }} by mauto 3.
    assert {{ Γ ⊢ B[Id,,M1] : Type@j }} by mauto 4.
    assert {{ Γ ⊢ M2 : B[Id,,M1] }} by mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 3. 
    assert {{ Γ, A ⊢ B : Type@j }} by mauto 3. 
    assert {{ Γ, A ⊢ B ≈ C : Type@j }} by mauto 2 using soundness_ty'.
    assert {{ Γ ⊢ Σ A B ≈ Σ A' C : Type@(max i j) }} as <- by mauto using wf_exp_eq_sigma_cong_max.
    mauto 4.
  - assert {{ Γ ⊢ M : Σ A B }} by mauto 2.
    gen_presups.
    apply wf_sigma_inversion' in HA. destruct_all.
    assert {{ Γ ⊢ fst M : A }} by mauto 3.
    assert {{ Γ ⊢ B[Id,,fst M] : Type@i }} by mauto 3.
    eapply wf_conv' with (A:={{{B[Id,,fst M]}}}); mauto 3 using soundness_ty'.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ Γ ⊢ M1 : A }} by mauto 2.
    assert {{ Γ ⊢ M2 : A }} by mauto 2.
    mauto 2.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 2 using soundness_ty'.
    assert {{ Γ ⊢ M : A }} by mauto 2.
    assert {{ Γ ⊢ M ≈ N : A }} by mauto 2 using soundness'.
    assert {{ Γ ⊢ M ≈ N : C }} by mauto 2.
    enough {{ Γ ⊢ Eq C N N ≈ Eq A M M : Type@i }} as -> by mauto 2.
    transitivity {{{ Eq A N N }}}; econstructor; mauto 3.
  - assert {{ Γ ⊢ A : Type@i }} by mauto 2.
    assert {{ Γ ⊢ M1 : A }} by mauto 2.
    assert {{ Γ ⊢ M2 : A }} by mauto 2.
    assert {{ ⊢ Γ, A }} by mauto 2.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 2.
    assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.
    assert {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 3.
    assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} by mauto 2.
    unshelve epose proof (@glu_rel_eq_eqrec_synprop_gen _ {{{ Id }}} _ _ A _ _); shelve_unifiable; [| eassumption |]; mauto 3;
      destruct_conjs.
    assert {{ Γ ⊢ M1 : A[Id] }} by mauto 2.
    assert {{ Γ ⊢ M2 : A[Id] }} by mauto 2.
    match goal with
    | H : forall _ _, _ -> _ -> _ |- _ =>
         unshelve epose proof (H M1 M2 _ _); shelve_unifiable; [eassumption | eassumption |]; destruct_conjs
    end.
    assert {{ Γ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} by mauto 3.
    assert {{ Γ ⊢ N : Eq A M1 M2 }} by mauto 3.
    assert {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@j }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,M1,,M2,,N] ≈ C : Type@j }} as <- by mauto 2 using soundness_ty'.
    mauto 3.
  - assert {{ Γ ⊢ #x : A }} by mauto 2.
    assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i] by mauto 2.
    assert {{ Γ ⊢ A ≈ B : Type@i }} as <- by mauto 2 using soundness_ty'.
    mauto 3.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  pose proof alg_type_sound; intuition.
Qed.

Lemma alg_type_infer_sound : forall {Γ A M},
    {{ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}.
Proof.
  pose proof alg_type_sound; intuition.
Qed.

Lemma alg_type_infer_normal : forall {Γ A A' M},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢a M ⟹ A }} ->
    nbe_ty Γ A A' ->
    A = A'.
Proof with (f_equiv; mautosolve 4).
  intros * ? Hinfer Hnbe. gen A'.
  assert {{ Γ ⊢ M : A }} by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  - assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 3.
    assert {{ Γ ⊢ M : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound...
  - assert {{ Γ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 3 using soundness_ty'.
    assert {{ Γ, A ⊢ M : B }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ, A ⊢ B : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert {{ ⊢ Γ, A ≈ Γ, ^(C : exp) }} by mauto 3.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    assert (initial_env {{{ Γ, ^(C : exp) }}} d{{{ ρ ↦ ⇑! a (length Γ) }}}) by mauto 3.
    assert (nbe_ty Γ A C) by mauto 3.
    assert (nbe_ty Γ C A0) by mauto 3.
    replace A0 with C by mauto 2.
    assert (nbe_ty {{{ Γ, ^(C : exp) }}} B B') by mauto 3.
    assert (nbe_ty {{{ Γ, A }}} B B') by mauto 4 using ctxeq_nbe_ty_eq'...
  - assert {{ Γ ⊢ M : ^n{{{ Π A B }}} }} by mauto 3 using alg_type_infer_sound.
    assert (exists i, {{ Γ ⊢ Π A B : Type@i }}) as [i] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, ^(A : exp) ⊢ B : Type@i }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ B[Id,,N] : Type@i }} by mauto 3...
  - assert {{ Γ ⊢ A : Type@i }} by (eapply alg_type_sound in Hinfer1; mauto 3).
    assert {{ Γ , A ⊢ B : Type@j }} by (eapply alg_type_sound in Hinfer2; mauto 3).
    assert (exists j, {{ Γ ⊢ Σ A' C : Type@j }}) as [k] by (gen_presups; eauto 2).
    apply wf_sigma_inversion' in H7; fold nf_to_exp in *. destruct_all.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    assert (nbe_ty Γ A A' ) by mauto 3.
    assert (nbe_ty Γ A' A0 ) by mauto 3.
    replace A0 with A' in * by mauto 3.
    assert {{ Γ ⊢ A ≈ A' : Type@i }} by mauto 3 using soundness_ty'.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    assert (nbe_ty {{{ Γ, A }}} B C) by unshelve mauto 3.
    assert (nbe_ty {{{ Γ,  ^(A' : exp)}}} C B') by mauto 4.
    assert {{ ⊢ Γ, A ≈ Γ, ^(A' : exp) }} by mauto 3.
    assert (nbe_ty {{{ Γ, ^(A : exp) }}} C B') by mauto 3 using ctxeq_nbe_ty_eq'.
    replace B' with C in * by mauto 3...
  - assert {{ Γ ⊢ M : ^n{{{ Σ A B }}} }} by mauto 3 using alg_type_infer_sound.
    gen_presups.
    assert (nbe_ty Γ {{{Σ A B }}} n{{{Σ A B}}}). {
      assert {{ Γ ⊢ ^ n{{{ Σ A B }}} ≈ ^ n{{{ Σ A B }}} : Type@i }} by (eapply exp_eq_refl; mauto 3).
      apply completeness_ty in H as IH. destruct_all.
      eapply IHHinfer in H2; subst; auto.
    }
    dir_inversion_clear_by_head nbe.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    functional_read_rewrite_clear. reflexivity.
  - assert {{ Γ ⊢ M : ^n{{{ Σ A B }}} }} by mauto 3 using alg_type_infer_sound.
    gen_presups.
    apply wf_sigma_inversion' in HA; fold nf_to_exp in *.
    destruct_all.
    assert {{ Γ ⊢ fst M : A }} by mauto 3.
    assert {{ Γ ⊢ B[Id,,fst M] : Type@i }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢ M : A }} by mauto 3 using alg_type_check_sound.
    dir_inversion_clear_by_head nbe.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    functional_read_rewrite_clear.
    assert (nbe_ty Γ A C) by mauto 3.
    assert (nbe_ty Γ C A0) by mauto 3.
    replace A0 with C in * by mauto 3.
    assert (nbe Γ M A N) by mauto 3.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 2 using soundness_ty'.
    assert (nbe Γ N C M1) by mauto 2.
    replace M1 with N in * by mauto 2.
    reflexivity.
  - assert {{ Γ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢ M1 : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ M2 : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ N : Eq A M1 M2 }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
    assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : ^n{{{ Type@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@j }} by mauto 2.
    mauto 3.
  - assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i] by mauto 2...
Qed.

#[export]
Hint Resolve alg_type_infer_normal : mctt.

Lemma alg_type_check_typ_implies_alg_type_infer_typ : forall {Γ A i},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢a A ⟸ Type@i }} ->
    exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  firstorder.
Qed.

#[export]
Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.

Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M A B i},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ Π A B : Type@i }} ->
    {{ Γ ⊢a M ⟸ Π A B }} ->
    exists A' B', {{ Γ ⊢a M ⟹ Π A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}.
Proof.
  intros * ? ? Hcheck.
  assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' C Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  inversion Hnbe1; subst.
  functional_initial_env_rewrite_clear.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  simpl in *.
  assert {{ Γ ⊢ M : ^n{{{ Π A0 B0 }}} }} by mauto 3 using alg_type_infer_sound.
  assert (exists j, {{ Γ ⊢ Π A0 B0 : Type@j }}) as [j] by (gen_presups; eauto 2).
  assert ({{ Γ ⊢ A0 : Type@j }} /\ {{ Γ, ^(A0 : exp) ⊢ B0 : Type@j }}) as [] by mauto 3.
  do 2 eexists.
  assert (nbe_ty Γ A A0) by mauto 3.
  assert {{ Γ ⊢ A ≈ A0 : Type@i }} by mauto 3 using soundness_ty'.
  repeat split; mauto 3.
  assert (initial_env {{{ Γ, A }}} d{{{ ρ ↦ ⇑! a (length Γ) }}}) by mauto 3.
  assert (nbe_ty {{{ Γ, A }}} B B') by mauto 3.
  assert (initial_env {{{ Γ, ^(A0 : exp) }}} d{{{ ρ ↦ ⇑! a0 (length Γ) }}}) by mauto 3.
  assert (nbe_ty {{{ Γ, ^(A0 : exp) }}} B0 B0) by mauto 3.
  assert {{ ⊢ Γ, A ≈ Γ, ^(A0 : exp) }} by mauto 3.
  assert (nbe_ty {{{ Γ, A }}} B0 B0) by mauto 4 using ctxeq_nbe_ty_eq'.
  mauto 3.
Qed.

#[export]
Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.

Lemma alg_type_check_sigma_implies_alg_type_infer_sigma : forall {Γ M A B i},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ Σ A B : Type@i }} ->
    {{ Γ ⊢a M ⟸ Σ A B }} ->
    exists A' B', {{ Γ ⊢a M ⟹ Σ A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}.
Proof.
  intros * ? ? Hcheck.
  assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' C Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  inversion Hnbe1; subst.
  functional_initial_env_rewrite_clear.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  simpl in *.
  assert {{ Γ ⊢ M : ^n{{{ Σ A0 B0 }}} }} by mauto 3 using alg_type_infer_sound.
  assert (exists j, {{ Γ ⊢ Σ A0 B0 : Type@j }}) as [j] by (gen_presups; eauto 2).
  assert ({{ Γ ⊢ A0 : Type@j }} /\ {{ Γ, ^(A0 : exp) ⊢ B0 : Type@j }}) as [] by mauto 3.
  do 2 eexists.
  assert (nbe_ty Γ A A0) by mauto 3.
  assert {{ Γ ⊢ A ≈ A0 : Type@i }} by mauto 3 using soundness_ty'.
  repeat split; mauto 3.
  assert (initial_env {{{ Γ, A }}} d{{{ ρ ↦ ⇑! a (length Γ) }}}) by mauto 3.
  assert (nbe_ty {{{ Γ, A }}} B B') by mauto 3.
  assert (initial_env {{{ Γ, ^(A0 : exp) }}} d{{{ ρ ↦ ⇑! a0 (length Γ) }}}) by mauto 3.
  assert (nbe_ty {{{ Γ, ^(A0 : exp) }}} B0 B0) by mauto 3.
  assert {{ ⊢ Γ, A ≈ Γ, ^(A0 : exp) }} by mauto 3.
  assert (nbe_ty {{{ Γ, A }}} B0 B0) by mauto 4 using ctxeq_nbe_ty_eq'.
  mauto 3.
Qed.

#[export]
Hint Resolve alg_type_check_sigma_implies_alg_type_infer_sigma : mctt.

Lemma alg_type_check_subtyp : forall {Γ A A' M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢a M ⟸ A' }}.
Proof.
  intros * [] **.
  assert {{ Γ0 ⊢a B ⊆ A' }} by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

#[export]
Hint Resolve alg_type_check_subtyp : mctt.

Corollary alg_type_check_conv : forall {Γ i A A' M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢a M ⟸ A' }}.
Proof.
  mauto 3.
Qed.

#[export]
Hint Resolve alg_type_check_conv : mctt.

Lemma alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢a M ⟸ A }}.
Proof.
  intros * Hue.
  induction 1; gen_presups; inversion Hue; subst; clear Hue; mauto 4 using alg_subtyping_complete, alg_type_check_subtyp.
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists j, {{ Γ, ℕ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ Γ ⊢ A[Id,,M] : Type@i }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Type@i }} as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert (exists j, {{ Γ, A ⊢a B ⟹ Type@j }} /\ j <= i) as [j' []] by mauto 3.
    assert (max j j' <= i) by lia.
    econstructor; mauto 3 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ Γ, A ⊢a M ⟸ B }} by mauto 3.
    assert (exists B', {{ Γ, A ⊢a M ⟹ B' }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [B' []] by (inversion_clear_by_head alg_type_check; firstorder).
    assert (exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W : Type@i }}) as [W []] by mauto 3 using soundness_ty.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert {{ Γ, A ⊢ M : B' }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ, A ⊢ B' : Type@j }}) as [] by (gen_presups; eauto 2).
    econstructor; mauto 3.
    eapply alg_subtyping_complete.
    eapply wf_subtyp_pi'; mauto 2.
    mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
  - assert {{ Γ ⊢a M ⟸ Π A B }} by mauto 2.
    assert {{ Γ ⊢a N ⟸ A }} by mauto 2.
    assert (exists A' B', {{ Γ ⊢a M ⟹ Π A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [A' [B' [? []]]] by mauto 3.
    assert {{ Γ ⊢ M : ^n{{{ Π A' B' }}} }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ ⊢ Π A' B' : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A' : Type@j }} /\ {{ Γ, ^(A' : exp) ⊢ B' : Type@j }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A' }} by mauto 3.
    assert {{ Γ ⊢ B'[Id,,N] : Type@j }} by mauto 3.
    assert (exists W, nbe_ty Γ {{{ B'[Id,,N] }}} W /\ {{ Γ ⊢ B'[Id,,N] ≈ W : Type@j }}) as [W []] by (eapply soundness_ty; mauto 3).
    assert {{ Γ, A ⊢ B' : Type@j }} by mauto 4.
    assert {{ Γ, A ⊢ B' ⊆ B }} by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert {{ Γ ⊢ B'[Id,,N] ⊆ B[Id,,N] }} by mauto 3.
    assert {{ Γ ⊢ W ⊆ B[Id,,N] }} by (transitivity {{{ B'[Id,,N] }}}; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert (exists j, {{ Γ, A ⊢a B ⟹ Type@j }} /\ j <= i) as [j' []] by mauto 3.
    assert (max j j' <= i) by lia.
    econstructor; mauto 3 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert (exists j, {{ Γ, A ⊢a B ⟹ Type@j }} /\ j <= i) as [j' []] by mauto 3. 
    assert {{ Γ ⊢ A : Type@j }}. 
    {
      eapply alg_type_infer_sound in H3; mauto 3.
    }
    assert {{ Γ, A ⊢ B : Type@j' }}. {
      eapply alg_type_infer_sound in H6; mauto 3.
    }
    assert (exists WA, nbe_ty Γ A WA /\ {{ Γ ⊢ A ≈ WA : Type@j }}) as [WA []] by mauto 3 using soundness_ty.
    assert (exists WB, nbe_ty {{{ Γ , A }}} B WB /\ {{ Γ , A ⊢ B ≈ WB : Type@j' }}) as [WB []] by mauto 3 using soundness_ty.
    assert {{ Γ ⊢ WA : Type@j }} by (gen_presups; mauto 3).
    assert {{ Γ , ^(WA :exp) ⊢ WB : Type@j' }}. 
    {
      gen_presups.
      eapply @ctxeq_exp with (Γ:={{{Γ,A}}}); mauto 3.
    }
    assert {{ Γ ⊢ ^ n{{{ Σ WA WB }}} ⊆ Σ A B }}. 
    { eapply wf_subtyp_sigma with (i:=max j j'); mauto 3 
      using lift_exp_eq_max_left, lift_exp_eq_max_right, lift_exp_max_left, lift_exp_max_right.
    }
    assert {{ Γ ⊢a ⟨ M : A; N : B ⟩ ⟹ Σ WA WB }} by (econstructor; mauto 3).
    mauto 3 using alg_subtyping_complete.
  - assert {{ Γ ⊢a M ⟸ Σ A B }} by mauto 3.
    assert (exists A' B', {{ Γ ⊢a M ⟹ Σ A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [A' [B' [? []]]] by mauto 3.
    assert {{ Γ ⊢a A' ⊆ A }} by mauto 3 using alg_subtyping_complete.
    mauto 3.
  - assert {{ Γ ⊢a M ⟸ Σ A B }} by mauto 3.
    assert (exists A' B', {{ Γ ⊢a M ⟹ Σ A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [A' [B' [? []]]] by mauto 3.
    assert {{ Γ ⊢ M : Σ A' B' }} by (eapply alg_type_sound in H4; mauto 3).
    assert (exists j, {{ Γ ⊢ Σ A' B' : Type@j }}) as [j] by (gen_presups; eauto 2).
    apply wf_sigma_inversion' in HA.
    apply wf_sigma_inversion' in H8. destruct_all.
    assert {{ Γ, ^(A:exp) ⊢ B' : Type@j }} by mauto 4.
    assert {{ Γ, A ⊢ B' ⊆ B }}. {
      eapply alg_subtyping_sound with (i:=max i0 j); mauto 3 using lift_exp_max_left, lift_exp_max_right.
    }
    assert (exists W, nbe_ty Γ {{{ B'[Id,,fst M] }}} W /\ {{ Γ ⊢ B'[Id,,fst M] ≈ W : Type@j }}) as [W []].  {
      eapply soundness_ty; mauto 3.
      eapply wf_conv'; [eapply wf_exp_sub |]; mauto 3.
      econstructor; mauto 3.
    }
    assert {{ Γ ⊢ B'[Id,,fst M] ⊆ B[Id,,fst M] }} by (eapply wf_subtyp_subst; mauto 3).
    assert {{ Γ ⊢ W ⊆ B[Id,,fst M] }} by (transitivity {{{ B'[Id,,fst M] }}}; mauto 3).
    mauto using alg_subtyping_complete.
  - assert (exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W : Type@i }}) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    econstructor; [econstructor |]; mauto 3 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ Γ ⊢a M ⟸ A }} by eauto 2.
    assert (exists C, nbe_ty Γ A C /\ {{ Γ ⊢ A ≈ C : Type@i }}) as [C []] by mauto 3 using soundness_ty.
    assert (exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}) as [W []] by mauto 3 using soundness.
    econstructor; mauto 3.
    assert {{ Γ ⊢ ^n{{{ Eq C W W }}} ≈ Eq A M M : Type@i }} by mauto 3.
    mauto 3 using alg_subtyping_complete.
  - assert (exists k, {{ Γ ⊢a A ⟹ Type@k }} /\ k <= i) as [k []] by mauto 3.
    assert (exists l, {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢a B ⟹ Type@l }} /\ l <= j) as [l []] by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
    assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : ^n{{{ Type@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@j }} by mauto 2.
    assert (exists C, nbe_ty Γ {{{ B[Id,,M1,,M2,,N] }}} C /\ {{ Γ ⊢ B[Id,,M1,,M2,,N] ≈ C : Type@j }}) as [C []] by mauto 3 using soundness_ty.
    econstructor; [econstructor |]; mauto 4 using alg_subtyping_complete.
Qed.

#[export]
Hint Resolve alg_type_check_complete : mctt.

Corollary alg_type_infer_complete : forall {Γ A M},
    user_exp M ->
    {{ Γ ⊢ M : A }} ->
    exists B, {{ Γ ⊢a M ⟹ B }} /\ {{ Γ ⊢a B ⊆ A }}.
Proof.
  intros.
  assert {{ Γ ⊢a M ⟸ A }} as Hcheck by mauto 4 using alg_type_check_complete.
  inversion_clear Hcheck.
  firstorder.
Qed.

#[export]
Hint Resolve alg_type_infer_complete : mctt.

Corollary alg_type_infer_typ_complete : forall {Γ i A},
    user_exp A ->
    {{ Γ ⊢ A : Type@i }} ->
    exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

#[export]
Hint Resolve alg_type_infer_typ_complete : mctt.

Corollary alg_type_infer_pi_complete : forall {Γ i A},
    user_exp A ->
    {{ Γ ⊢ A : Type@i }} ->
    exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

#[export]
Hint Resolve alg_type_infer_pi_complete : mctt.
