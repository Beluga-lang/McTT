From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core Require Export Soundness.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Completeness.Consequences Require Export Types.
Import Domain_Notations.

Lemma idempotent_nbe : forall {Γ A M N L},
    {{ Γ ⊢ M : A }} ->
    nbe Γ M A N ->
    nbe Γ N A L ->
    N = L.
Proof.
  intros.
  assert {{ Γ ⊢ M ≈ N : A }} as [? []]%completeness by mauto 2 using soundness'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.
#[export]
Hint Resolve idempotent_nbe : mctt.

Lemma idempotent_nbe' : forall {Γ i A A' M N L},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    nbe Γ M A N ->
    nbe Γ N A' L ->
    N = L.
Proof.
  intros * ? [env_relΓ [? [j]]]%completeness_fundamental_exp_eq **.
  assert {{ Γ ⊢ M ≈ N : A }} as [? [? [k]]]%completeness_fundamental_exp_eq by mauto 3 using soundness'.
  handle_per_ctx_env_irrel.
  destruct_by_head nbe.
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)); destruct_all.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: fun H => directed (pose proof (H _ _ ltac:(eassumption)); destruct_all)).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  destruct_all.
  functional_eval_rewrite_clear.
  handle_per_univ_elem_irrel.
  pose proof (per_elem_then_per_top ltac:(eassumption) ltac:(eassumption) (length Γ)); destruct_all.
  functional_read_rewrite_clear.
  reflexivity.
Qed.
#[export]
Hint Resolve idempotent_nbe' : mctt.

Lemma idempotent_nbe_ty : forall {Γ i A B C},
    {{ Γ ⊢ A : Type@i }} ->
    nbe_ty Γ A B ->
    nbe_ty Γ B C ->
    B = C.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ B : Type@i }} as [? []]%completeness_ty by mauto 2 using soundness_ty'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.

#[export]
Hint Resolve idempotent_nbe_ty : mctt.

Lemma adjust_exp_eq_level : forall {Γ A A' i j},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A : Type@j }} ->
    {{ Γ ⊢ A' : Type@j }} ->
    {{ Γ ⊢ A ≈ A' : Type@j }}.
Proof.
  intros * ?%completeness_ty ?%soundness ?%soundness.
  destruct_conjs.
  dir_inversion_by_head nbe; dir_inversion_by_head nbe_ty; subst.
  match_by_head eval_exp ltac:(fun H => progressive_invert H).
  match_by_head read_nf ltac:(fun H => progressive_invert H).
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  etransitivity; [| symmetry]; eauto.
Qed.

Lemma exp_eq_pi_inversion : forall {Γ A B A' B' i},
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} /\ {{ Γ, A ⊢ B ≈ B' : Type@i }}.
Proof.
  intros * H.
  gen_presups.
  (on_all_hyp: fun H => apply wf_pi_inversion' in H; destruct H).
  (on_all_hyp: fun H => apply completeness_ty in H).
  (on_all_hyp: fun H => pose proof (soundness H)).
  destruct_conjs.
  dir_inversion_clear_by_head nbe.
  dir_inversion_clear_by_head nbe_ty.
  dir_inversion_by_head initial_env; subst.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_clear_by_head read_nf.
  dir_inversion_by_head read_typ; subst.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  autoinjections.
  assert {{ Γ ⊢ A' ≈ A : Type@i }} by mauto 3.
  assert {{ ⊢ Γ, A' ≈ Γ, A }} by mauto 3.
  split; [mauto 3 |].
  etransitivity; [| symmetry]; mauto 2.
Qed.

Lemma nf_of_pi : forall {Γ M A B},
    {{ Γ ⊢ M : Π A B }} ->
    exists W1 W2, nbe Γ M {{{ Π A B }}} n{{{ λ W1 W2 }}}.
Proof.
  intros * [? []]%soundness.
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  dir_inversion_clear_by_head read_nf.
  do 2 eexists; mauto 4.
Qed.

#[export]
Hint Resolve nf_of_pi : mctt.

Theorem canonical_form_of_pi : forall {M A B},
    {{ ⋅ ⊢ M : Π A B }} ->
    exists W1 W2, nbe {{{ ⋅ }}} M {{{ Π A B }}} n{{{ λ W1 W2 }}}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve canonical_form_of_pi : mctt.

Lemma exp_eq_sigma_inversion : forall {Γ A B A' B' i},
    {{ Γ ⊢ Σ A B ≈ Σ A' B' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} /\ {{ Γ, A ⊢ B ≈ B' : Type@i }}.
Proof.
  intros * H.
  gen_presups.
  (on_all_hyp: fun H => apply wf_sigma_inversion' in H; destruct H).
  (on_all_hyp: fun H => apply completeness_ty in H).
  (on_all_hyp: fun H => pose proof (soundness H)).
  destruct_conjs.
  dir_inversion_clear_by_head nbe.
  dir_inversion_clear_by_head nbe_ty.
  dir_inversion_by_head initial_env; subst.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_clear_by_head read_nf.
  dir_inversion_by_head read_typ; subst.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  autoinjections.
  assert {{ Γ ⊢ A' ≈ A : Type@i }} by mauto 3.
  assert {{ ⊢ Γ, A' ≈ Γ, A }} by mauto 3.
  split; [mauto 3 |].
  etransitivity; [| symmetry]; mauto 2.
Qed.

Lemma nf_of_sigma : forall {Γ M A B},
    {{ Γ ⊢ M : Σ A B }} ->
    exists W1 W2 W3 W4, nbe Γ M {{{ Σ A B }}} n{{{ ⟨ W1 : W2 ; W3 : W4 ⟩ }}}.
Proof.
  intros * [? []]%soundness.
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  dir_inversion_clear_by_head read_nf.
  do 4 eexists; mauto 4.
Qed.

#[export]
Hint Resolve nf_of_sigma : mctt.

Theorem canonical_form_of_sigma : forall {M A B},
    {{ ⋅ ⊢ M : Σ A B }} ->
    exists W1 W2 W3 W4, nbe {{{ ⋅ }}} M {{{ Σ A B }}} n{{{ ⟨ W1 : W2 ; W3 : W4 ⟩ }}}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve canonical_form_of_sigma : mctt.

Inductive canonical_nat : nf -> Prop :=
| canonical_nat_zero : canonical_nat n{{{ zero }}}
| canonical_nat_succ : forall W, canonical_nat W -> canonical_nat n{{{ succ W }}}
.

#[export]
Hint Constructors canonical_nat : mctt.

Theorem canonical_form_of_nat : forall {M},
    {{ ⋅ ⊢ M : ℕ }} ->
    exists W, nbe {{{ ⋅ }}} M {{{ ℕ }}} W /\ canonical_nat W.
Proof with mautosolve 4.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M.
  match_by_head1 read_nf ltac:(fun H => dependent induction H);
    intros; mauto 3;
    gen_presups.
  - eassert ({{ ⋅ ⊢ ^_ : ℕ }} /\ {{ ⋅ ⊢ ℕ ⊆ ℕ }}) as [? _]...
  - match_by_head1 (wf_exp {{{ ⋅ }}} {{{ ℕ }}}) ltac:(fun H => contradict H)...
Qed.

#[export]
Hint Resolve canonical_form_of_nat : mctt.

Theorem canonical_form_of_typ : forall {i M},
    {{ ⋅ ⊢ M : Type@i }} ->
    exists W, nbe {{{ ⋅ }}} M {{{ Type@i }}} W /\ is_typ_constr W /\ (forall V, W <> n{{{ ⇑ V }}}).
Proof with mautosolve 4.
  intros * [? []]%soundness.
  eexists; split; [eassumption |].
  dir_inversion_clear_by_head nbe.
  invert_rel_typ_body.
  match_by_head1 eval_exp ltac:(fun H => clear H).
  gen M.
  dir_inversion_clear_by_head read_nf.
  match_by_head1 read_typ ltac:(fun H => dependent induction H);
    intros; split; intros; mauto 3; try congruence;
    gen_presups;
    match_by_head1 (wf_exp {{{ ⋅ }}} {{{ Type@i }}}) ltac:(fun H => contradict H)...
Qed.

#[export]
Hint Resolve canonical_form_of_typ : mctt.

Lemma subtyp_spec : forall {Γ A B},
    {{ Γ ⊢ A ⊆ B }} ->
    (exists k, {{ Γ ⊢ A ≈ B : Type@k }}) \/
      (exists i j, (exists k, {{ Γ ⊢ A ≈ Type@i : Type@k }}) /\ (exists k, {{ Γ ⊢ Type@j ≈ B : Type@k }}) /\ i <= j) \/
      (exists A1 A2 B1 B2, (exists k, {{ Γ ⊢ A ≈ Π A1 A2 : Type@k }}) /\ (exists k, {{ Γ ⊢ Π B1 B2 ≈ B : Type@k }}) /\ (exists k, {{ Γ ⊢ A1 ≈ B1 : Type@k }}) /\ {{ Γ, B1 ⊢ A2 ⊆ B2 }}) \/
      (exists A1 A2 B1 B2, (exists k, {{ Γ ⊢ A ≈ Σ A1 A2 : Type@k }}) /\ (exists k, {{ Γ ⊢ Σ B1 B2 ≈ B : Type@k }}) /\ (exists k, {{ Γ ⊢ A1 ≈ B1 : Type@k }}) /\ {{ Γ, B1 ⊢ A2 ⊆ B2 }}).
Proof with (congruence + firstorder (mautosolve 4 + lia)).
  induction 1; mauto 3.
  - destruct_all; firstorder (mauto 3);
      try (right; right; left; do 4 eexists; firstorder mautosolve 3);
      try (right; right; right; do 4 eexists; firstorder mautosolve 3).
    + match goal with
      | _: {{ Γ ⊢ M' ≈ Type@?i : Type@_ }},
          _: {{ Γ ⊢ Type@?j ≈ M' : Type@_ }} |- _ =>
          assert {{ Γ ⊢ Type@j ≈ Type@i : Type@_ }} by mauto 3;
          assert (j = i) as -> by mauto 3
      end...
    + assert {{ Γ ⊢ Π ^_ ^_ ≈ Type@_ : Type@_ }} by mauto 3.
      assert ({{{ Π ^_ ^_ }}} = {{{ Type@_ }}}) by mauto 3...
    + assert {{ Γ ⊢ Σ ^_ ^_ ≈ Type@_ : Type@_ }} by mauto 3.
      assert ({{{ Σ ^_ ^_ }}} = {{{ Type@_ }}}) by mauto 3...
    + assert {{ Γ ⊢ Π ^_ ^_ ≈ Type@_ : Type@_ }} by mauto 3.
      assert ({{{ Π ^_ ^_ }}} = {{{ Type@_ }}}) by mauto 3...
    + match goal with
      | _: {{ Γ ⊢ M' ≈ Π ^?A1 ^?A2 : Type@_ }},
          _: {{ Γ ⊢ Π ^?B1 ^?B2 ≈ M' : Type@_ }} |- _ =>
          assert {{ Γ ⊢ Π A1 A2 ≈ Π B1 B2 : Type@_ }} by mauto 3;
          assert ({{ Γ ⊢ A1 ≈ B1 : Type@_ }} /\ {{ Γ, A1 ⊢ A2 ≈ B2 : Type@_ }}) as [] by mauto 3 using exp_eq_pi_inversion
      end.
      assert {{ ⊢ Γ ≈ Γ }} by mauto 3.
      right; right; left.
      do 4 eexists; repeat split; mauto 3.
      * eexists; eapply exp_eq_trans_typ_max...
      * etransitivity; [| eassumption].
        etransitivity; eapply ctxeq_subtyp...
    + assert {{ Γ ⊢ Π ^_ ^_ ≈ Σ ^_ ^_ : Type@_ }} as Hcontra by mauto 3.
      eapply is_typ_constr_and_exp_eq_sigma_implies_eq_sigma in Hcontra; mauto 3.
      destruct_all...
    + assert {{ Γ ⊢ Σ ^_ ^_ ≈ Type@_ : Type@_ }} by mauto 3.
      assert ({{{ Σ ^_ ^_ }}} = {{{ Type@_ }}}) by mauto 3...
    + assert {{ Γ ⊢ Π ^_ ^_ ≈ Σ ^_ ^_ : Type@_ }} as Hcontra by mauto 3.
      eapply is_typ_constr_and_exp_eq_sigma_implies_eq_sigma in Hcontra; mauto 3.
      destruct_all...
    + match goal with
      | _: {{ Γ ⊢ M' ≈ Σ ^?A1 ^?A2 : Type@_ }},
          _: {{ Γ ⊢ Σ ^?B1 ^?B2 ≈ M' : Type@_ }} |- _ =>
          assert {{ Γ ⊢ Σ A1 A2 ≈ Σ B1 B2 : Type@_ }} by mauto 3;
          assert ({{ Γ ⊢ A1 ≈ B1 : Type@_ }} /\ {{ Γ, A1 ⊢ A2 ≈ B2 : Type@_ }}) as [] by mauto 3 using exp_eq_sigma_inversion
      end.
      assert {{ ⊢ Γ ≈ Γ }} by mauto 3.
      right; right; right.
      do 4 eexists; repeat split; mauto 3.
      * eexists; eapply exp_eq_trans_typ_max...
      * etransitivity; [| eassumption].
        etransitivity; eapply ctxeq_subtyp...
  - right; left.
    do 2 eexists...
  - right; right; left.
    do 4 eexists...
  - right; right; right.
    do 4 eexists...
Qed.

#[export]
Hint Resolve subtyp_spec : mctt.

Lemma consistency_ne_helper : forall {i A A'} {W : ne},
    is_typ_constr A' ->
    (forall j, A' <> {{{ Type@j }}}) ->
    {{ ⋅, Type@i ⊢ A ⊆ A' }} ->
    ~ {{ ⋅, Type@i ⊢ W : A }}.
Proof with (congruence + mautosolve 3).
 intros * HA' HA'eq Heq HW. gen A'.
  dependent induction HW; intros; mauto 3; try directed dependent destruction HA';
    try (destruct W; simpl in *; congruence).
  - destruct W; simpl in *; autoinjections.
    eapply IHHW4; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW3; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW3; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW3; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    do 2 match_by_head ctx_lookup ltac:(fun H => dependent destruction H).
    assert {{ ⋅, Type@i ⊢ Type@i[Wk] ≈ Type@i : Type@(S i) }} by mauto 3.
    eapply subtyp_spec in Heq as [| []]; destruct_conjs;
      try (eapply HA'eq; mautosolve 4).
    destruct H1. 
    + destruct_all.
      assert {{ ⋅, Type@i ⊢ Type@i ≈ Π ^_ ^_ : Type@_ }} by mauto 3.
      assert ({{{ Π ^_ ^_ }}} = {{{ Type@i }}}) by mauto 3...
    + destruct_all.
      assert {{ ⋅, Type@i ⊢ Type@i ≈ Σ ^_ ^_ : Type@_ }} by mauto 3.
      assert ({{{ Σ ^_ ^_ }}} = {{{ Type@i }}}) by mauto 3...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW6; [| | | | mauto 4]...
Qed.

Theorem consistency : forall {i} M,
    ~ {{ ⋅ ⊢ M : Π Type@i #0 }}.
Proof with (congruence + mautosolve 3).
  intros * HW.
  assert (exists W1 W2, nbe {{{ ⋅ }}} M {{{ Π Type@i #0 }}} n{{{ λ W1 W2 }}}) as [W1 [W2 Hnbe]] by mauto 3.
  assert (exists W, nbe {{{ ⋅ }}} M {{{ Π Type@i #0 }}} W /\ {{ ⋅ ⊢ M ≈ W : Π Type@i #0 }}) as [? []] by mauto 3 using soundness.
  gen_presups.
  functional_nbe_rewrite_clear.
  dependent destruction Hnbe.
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  match_by_head read_typ ltac:(fun H => directed dependent destruction H).
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  simpl in *.
  assert (exists B, {{ ⋅, Type@i ⊢ M0 : B }} /\ {{ ⋅ ⊢ Π Type@i B ⊆ Π Type@i #0 }}) as [B [? [| [|]]%subtyp_spec]] by mauto 3;
    destruct_all;
    try assert ({{{ Π ^_ ^_ }}} = {{{ Type@_ }}}) by mauto 3;
    try congruence.
  - assert (_ /\ {{ ^_ ⊢ B ≈ #0 : ^_ }}) as [_ ?] by mauto 3 using exp_eq_pi_inversion.
    eapply consistency_ne_helper...
  - assert (_ /\ {{ ^_ ⊢ B ≈ ^_ : ^_ }}) as [_ ?] by mauto 3 using exp_eq_pi_inversion.
    assert (_ /\ {{ ^_ ⊢ ^_ ≈ #0 : ^_ }}) as [? ?] by mauto 3 using exp_eq_pi_inversion.
    assert {{ ^_ ⊢ B ⊆ #0 }} by (etransitivity; [| eapply ctxeq_subtyp]; mauto 4).
    eapply consistency_ne_helper...
  - eapply is_typ_constr_and_exp_eq_pi_implies_eq_pi in H6; mauto 3.
    destruct_all...
Qed.
