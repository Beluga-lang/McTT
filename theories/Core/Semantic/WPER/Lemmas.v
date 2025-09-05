From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.WCong Require Import Definitions Lemmas.
From Mctt.Core.Semantic Require Import WPER.CoreTactics WPER.Definitions.

Import Domain_Notations.

Add Parametric Morphism R0 `(R0_morphism : Proper _ ((@relation_equivalence domain) ==> (@relation_equivalence domain)) R0) A ρ A' ρ' : (rel_mod_eval R0 A ρ A' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_eval_morphism.
Proof.
  split; intros []; econstructor; try eassumption;
    [> eapply R0_morphism; [symmetry + idtac |]; eassumption ..].
Qed.

Add Parametric Morphism f a f' a' : (rel_mod_app f a f' a')
    with signature (@relation_equivalence domain) ==> iff as rel_mod_app_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    apply HRR'; eassumption.
Qed.

Lemma per_bot_sym : forall m n,
    {{ Dom m ≈≈ n ∈ per_bot }} ->
    {{ Dom n ≈≈ m ∈ per_bot }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_all.
  do 2 eexists; mauto.
Qed.

#[export]
Hint Resolve per_bot_sym : mctt.

Lemma per_bot_trans : forall m n l,
    {{ Dom m ≈≈ n ∈ per_bot }} ->
    {{ Dom n ≈≈ l ∈ per_bot }} ->
    {{ Dom m ≈≈ l ∈ per_bot }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear.
  do 2 eexists; mauto.
Qed.

#[export]
Hint Resolve per_bot_trans : mctt.

#[export]
Instance per_bot_PER : PER per_bot.
Proof.
  split.
  - eauto using per_bot_sym.
  - eauto using per_bot_trans.
Qed.

Lemma var_per_bot : forall {n},
    {{ Dom !n ≈≈ !n ∈ per_bot }}.
Proof.
  intros ? ?. repeat econstructor.
Qed.

#[export]
Hint Resolve var_per_bot : mctt.

Lemma per_top_sym : forall m n,
    {{ Dom m ≈≈ n ∈ per_top }} ->
    {{ Dom n ≈≈ m ∈ per_top }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs.
  do 2 eexists; mauto.
Qed.

#[export]
Hint Resolve per_top_sym : mctt.

Lemma per_top_trans : forall m n l,
    {{ Dom m ≈≈ n ∈ per_top }} ->
    {{ Dom n ≈≈ l ∈ per_top }} ->
    {{ Dom m ≈≈ l ∈ per_top }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear.
  do 2 eexists; mauto.
Qed.

#[export]
Hint Resolve per_top_trans : mctt.

#[export]
Instance per_top_PER : PER per_top.
Proof.
  split.
  - eauto using per_top_sym.
  - eauto using per_top_trans.
Qed.

Lemma per_bot_then_per_top : forall m m' a a' b b' c c',
    {{ Dom m ≈≈ m' ∈ per_bot }} ->
    {{ Dom ⇓ (⇑ a b) ⇑ c m ≈≈ ⇓ (⇑ a' b') ⇑ c' m' ∈ per_top }}.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs.
  do 2 eexists; split; constructor; mauto 3.
Qed.

#[export]
Hint Resolve per_bot_then_per_top : mctt.

Lemma per_top_typ_sym : forall m n,
    {{ Dom m ≈≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈≈ m ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_all. 
  do 2 eexists; mauto.
Qed.

#[export]
Hint Resolve per_top_typ_sym : mctt.

Lemma per_top_typ_trans : forall m n l,
    {{ Dom m ≈≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈≈ l ∈ per_top_typ }} ->
    {{ Dom m ≈≈ l ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_all.
  functional_read_rewrite_clear.
  do 2 eexists; mauto.
Qed.

#[export]
Hint Resolve per_top_typ_trans : mctt.

#[export]
Instance per_top_typ_PER : PER per_top_typ.
Proof.
  split.
  - eauto using per_top_typ_sym.
  - eauto using per_top_typ_trans.
Qed.

Lemma per_nat_sym : forall m n,
    {{ Dom m ≈≈ n ∈ per_nat }} ->
    {{ Dom n ≈≈ m ∈ per_nat }}.
Proof with mautosolve.
  induction 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_sym : mctt.

Lemma per_nat_trans : forall m n l,
    {{ Dom m ≈≈ n ∈ per_nat }} ->
    {{ Dom n ≈≈ l ∈ per_nat }} ->
    {{ Dom m ≈≈ l ∈ per_nat }}.
Proof with mautosolve.
  intros * H. gen l.
  induction H; inversion_clear 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_trans : mctt.

#[export]
Instance per_nat_PER : PER per_nat.
Proof.
  split.
  - eauto using per_nat_sym.
  - eauto using per_nat_trans.
Qed.

Lemma per_ne_sym : forall m n,
    {{ Dom m ≈≈ n ∈ per_ne }} ->
    {{ Dom n ≈≈ m ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_sym : mctt.

Lemma per_ne_trans : forall m n l,
    {{ Dom m ≈≈ n ∈ per_ne }} ->
    {{ Dom n ≈≈ l ∈ per_ne }} ->
    {{ Dom m ≈≈ l ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  inversion_clear 1.
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_trans : mctt.

#[export]
Instance per_ne_PER : PER per_ne.
Proof.
  split.
  - eauto using per_ne_sym.
  - eauto using per_ne_trans.
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> eq ==> eq ==> iff as per_univ_elem_morphism_iff.
Proof with mautosolve.
  simpl.
  intros R R' HRR'.
  split; intros Horig; [gen R' | gen R];
    induction Horig using per_univ_elem_ind; basic_per_univ_elem_econstructor; eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor...
Qed.

Add Parametric Morphism i : (per_univ_elem i)
    with signature (@relation_equivalence domain) ==> (@relation_equivalence domain) as per_univ_elem_morphism_relation_equivalence.
Proof with mautosolve.
  intros ** a b.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism i A ρ A' ρ' : (rel_typ i A ρ A' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_typ_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

Lemma domain_app_per : forall f f' a a',
  {{ Dom f ≈≈ f' ∈ per_bot }} ->
  {{ Dom a ≈≈ a' ∈ per_top }} ->
  {{ Dom f a ≈≈ f' a' ∈ per_bot }}.
Proof.
  intros. intros s.
  specialize (H s).
  specialize (H0 s).
  destruct_all. 
  do 2 eexists; repeat split; mauto.
Qed.

Ltac rewrite_relation_equivalence_left :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_relation_equivalence_right :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_relation_equivalence :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_relation_equivalence :=
  clear_relation_equivalence;
  rewrite_relation_equivalence_right;
  clear_relation_equivalence;
  rewrite_relation_equivalence_left;
  clear_relation_equivalence.

Lemma per_univ_elem_right_irrel : forall i i' R a b R' b',
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF a ≈≈ b' ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof with (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear; econstructor; intuition).
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen a' b' R'.
  induction Horig using per_univ_elem_ind; intros * Heq Hright;
    subst; basic_invert_per_univ_elem Hright; unfold per_univ;
    intros;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ _ eq_refl equiv_a_a').
  split; intros.
  - rename equiv_c_c' into equiv0_c_c'.
    assert (equiv_c_c' : in_rel c c') by firstorder...
  - assert (equiv0_c_c' : in_rel0 c c') by firstorder...
Qed.

#[local]
Ltac per_univ_elem_right_irrel_assert1 :=
  match goal with
  | H1 : {{ DF ^?a ≈≈ ^?b ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^?a ≈≈ ^?b' ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_univ_elem_right_irrel_assert := repeat per_univ_elem_right_irrel_assert1.

Lemma per_univ_elem_sym : forall i R a b,
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈≈ a ∈ per_univ_elem i ↘ R }} /\
      (forall m m',
          {{ Dom m ≈≈ m' ∈ R }} ->
          {{ Dom m' ≈≈ m ∈ R }}).
Proof with mautosolve.
  simpl.
  induction 1 using per_univ_elem_ind; subst.
  - split.
    + apply per_univ_elem_core_univ'; firstorder.
    + intros.
      rewrite H1 in *.
      destruct_by_head per_univ.
      eexists.
      eapply proj1...
  - split; [basic_per_univ_elem_econstructor | intros; apply_relation_equivalence]...
  - destruct_conjs.
    split.
    + basic_per_univ_elem_econstructor; eauto.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_all.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      apply_relation_equivalence.
      eassumption.
    + apply_relation_equivalence.
      intros.
      assert (in_rel c' c) by eauto.
      assert (in_rel c c) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_univ_elem_right_irrel_assert.
      intuition.
  - split; [econstructor | intros; apply_relation_equivalence]...
Qed.

Corollary per_univ_sym : forall i R a b,
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈≈ a ∈ per_univ_elem i ↘ R }}.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_sym' : forall i a b,
    {{ Dom a ≈≈ b ∈ per_univ i }} ->
    {{ Dom b ≈≈ a ∈ per_univ i }}.
Proof.
  intros * [? ?%per_univ_elem_sym].
  firstorder.
Qed.

Corollary per_elem_sym : forall i R a b m m',
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom m ≈≈ m' ∈ R }} ->
    {{ Dom m' ≈≈ m ∈ R }}.
Proof.
  intros * ?%per_univ_elem_sym.
  firstorder.
Qed.

Corollary per_univ_elem_left_irrel : forall i i' R a b R' a',
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF a' ≈≈ b ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ?%per_univ_sym ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Corollary per_univ_elem_cross_irrel : forall i i' R a b R' b',
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ DF b' ≈≈ a ∈ per_univ_elem i' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ? ?%per_univ_sym.
  eauto using per_univ_elem_right_irrel.
Qed.

Ltac do_per_univ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_univ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ^?a ≈≈ ^_ ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^?a ≈≈ ^_ ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈≈ ^?b ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^_ ≈≈ ^?b ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^?a ≈≈ ^_ ∈ per_univ_elem ?i ↘ ?R1 }},
      H2 : {{ DF ^_ ≈≈ ^?a ∈ per_univ_elem ?i' ↘ ?R2 }} |- _ =>
      (** Order matters less here as H1 and H2 cannot be exchanged *)
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_univ_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_univ_elem_irrel_assert :=
  repeat do_per_univ_elem_irrel_assert1.

Ltac handle_per_univ_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_univ_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Lemma per_univ_elem_trans : forall i R a1 a2,
    per_univ_elem i R a1 a2 ->
    (forall j a3,
        per_univ_elem j R a2 a3 ->
        per_univ_elem i R a1 a3) /\
      (forall m1 m2 m3,
          R m1 m2 ->
          R m2 m3 ->
          R m1 m3).
Proof with (basic_per_univ_elem_econstructor; mautosolve 4).
  induction 1 using per_univ_elem_ind;
    [> split;
     [ intros * HT2; basic_invert_per_univ_elem HT2
     | intros * HTR1 HTR2; apply_relation_equivalence ] ..]; mauto.
  - (** univ case *)
    subst.
    destruct HTR1, HTR2.
    functional_eval_rewrite_clear.
    handle_per_univ_elem_irrel.
    eexists.
    specialize (H2 _ _ _ H0) as [].
    intuition.
  - (** nat case *)
    idtac...
  - (** pi case *)
    destruct_conjs.
    basic_per_univ_elem_econstructor; eauto.
    + handle_per_univ_elem_irrel.
      intuition.
    + intros.
      handle_per_univ_elem_irrel.
      assert (in_rel c c') by firstorder.
      assert (in_rel c c) by intuition.
      assert (in_rel0 c c) by intuition.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      handle_per_univ_elem_irrel...
  - (** fun case *)
    intros.
    assert (in_rel c c) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intuition.
  - (** neut case *)
    idtac...
Qed.

Corollary per_univ_trans : forall i j R a1 a2 a3,
    per_univ_elem i R a1 a2 ->
    per_univ_elem j R a2 a3 ->
    per_univ_elem i R a1 a3.
Proof.
  intros * ?%per_univ_elem_trans.
  firstorder.
Qed.

Corollary per_univ_trans' : forall i j a1 a2 a3,
    {{ Dom a1 ≈≈ a2 ∈ per_univ i }} ->
    {{ Dom a2 ≈≈ a3 ∈ per_univ j }} ->
    {{ Dom a1 ≈≈ a3 ∈ per_univ i }}.
Proof.
  intros * [? ?] [? ?].
  handle_per_univ_elem_irrel.
  firstorder mauto using per_univ_trans.
Qed.

Corollary per_elem_trans : forall i R a1 a2 m1 m2 m3,
    per_univ_elem i R a1 a2 ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * ?% per_univ_elem_trans.
  firstorder.
Qed.

#[export]
Instance per_univ_PER {i R} : PER (per_univ_elem i R).
Proof.
  split.
  - auto using per_univ_sym.
  - eauto using per_univ_trans.
Qed.

#[export]
Instance per_univ_PER' {i} : PER (per_univ i).
Proof.
  split.
  - auto using per_univ_sym'.
  - eauto using per_univ_trans'.
Qed.

#[export]
Instance per_elem_PER {i R a b} `(H : per_univ_elem i R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_elem_sym _ _ _ _ m m' H). eauto.
  - pose proof (fun m0 m1 m2 => per_elem_trans _ _ _ _ m0 m1 m2 H); eauto.
Qed.

(** This lemma gets rid of the unnecessary PER premise. *)
Lemma per_univ_elem_pi' :
  forall i a a' ρ B ρ' B'
    (in_rel : relation domain)
    (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈≈ c' ∈ in_rel }}), relation domain)
    elem_rel,
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ in_rel}} ->
    (forall {c c'} (equiv_c_c' : {{ Dom c ≈≈ c' ∈ in_rel }}),
        rel_mod_eval (per_univ_elem i) B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
    {{ DF Π a ρ B ≈≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }}.
Proof.
  intros.
  basic_per_univ_elem_econstructor; eauto.
  typeclasses eauto.
Qed.

Ltac per_univ_elem_econstructor :=
  (repeat intro; hnf; eapply per_univ_elem_pi') + basic_per_univ_elem_econstructor.

#[export]
Hint Resolve per_univ_elem_pi' : mctt.

Lemma per_univ_elem_pi_clean_inversion : forall {i j a a' in_rel ρ ρ' B B' elem_rel},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ in_rel }} ->
    {{ DF Π a ρ B ≈≈ Π a' ρ' B' ∈ per_univ_elem j ↘ elem_rel }} ->
    exists (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈≈ c' ∈ in_rel }}), relation domain),
      (forall c c' (equiv_c_c' : {{ Dom c ≈≈ c' ∈ in_rel }}),
          rel_mod_eval (per_univ_elem j) B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} (out_rel equiv_c_c')) /\
        (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')).
Proof.
  intros * Ha HΠ.
  basic_invert_per_univ_elem HΠ.
  handle_per_univ_elem_irrel.
  eexists.
  split.
  - instantiate (1 := fun c c' (equiv_c_c' : in_rel c c') m m' =>
                        forall R,
                          rel_typ j B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} R ->
                          R m m').
    intros.
    assert (in_rel0 c c') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel.
    intuition.
  - split; intros;
      [ assert (in_rel0 c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel c c') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel.
    intuition.
Qed.

Ltac invert_per_univ_elem H :=
  (unshelve eapply (per_univ_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + basic_invert_per_univ_elem H.

(* TODO: unify with the uip version above *)
Ltac invert_per_univ_elem_nouip H :=
  (unshelve eapply (per_univ_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + basic_invert_per_univ_elem_nouip H.

Lemma per_univ_elem_cumu : forall i a0 a1 R,
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem (S i) ↘ R }}.
Proof with solve [eauto].
  simpl.
  induction 1 using per_univ_elem_ind; subst;
    per_univ_elem_econstructor; eauto.
  intros.
  destruct_rel_mod_eval.
  econstructor...
Qed.

#[export]
Hint Resolve per_univ_elem_cumu : mctt.

Lemma per_univ_elem_cumu_ge : forall i i' a0 a1 R,
    i <= i' ->
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem i' ↘ R }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve per_univ_elem_cumu_ge : mctt.

Lemma per_univ_elem_cumu_max_left : forall i j a0 a1 R,
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem i ↘ R }} ->
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with mautosolve.
  intros.
  assert (i <= max i j) by lia...
Qed.

Lemma per_univ_elem_cumu_max_right : forall i j a0 a1 R,
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem j ↘ R }} ->
    {{ DF a0 ≈≈ a1 ∈ per_univ_elem (max i j) ↘ R }}.
Proof with mautosolve.
  intros.
  assert (j <= max i j) by lia...
Qed.

Lemma per_subtyp_to_univ_elem : forall a b i,
    {{ Sub a <: b at i }} ->
    exists R R',
      {{ DF a ≈≈ a ∈ per_univ_elem i ↘ R }} /\
        {{ DF b ≈≈ b ∈ per_univ_elem i ↘ R' }}.
Proof.
  destruct 1; do 2 eexists; mauto;
    split; per_univ_elem_econstructor; mauto;
    try apply Equivalence_Reflexive.
  lia.
Qed.

Lemma per_elem_subtyping : forall A B i,
    {{ Sub A <: B at i }} ->
    forall R R' a b,
      {{ DF A ≈≈ A ∈ per_univ_elem i ↘ R }} ->
      {{ DF B ≈≈ B ∈ per_univ_elem i ↘ R' }} ->
      R a b ->
      R' a b.
Proof.
  induction 1; intros.
  4:clear H3 H4.
  all:(on_all_hyp: fun H => directed invert_per_univ_elem H);
    apply_equiv_left;
    trivial.
  - firstorder mauto.
  - intros.
    deepexec IHper_subtyp ltac:(fun H => pose proof H).
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    deepexec H1 ltac:(fun H => pose proof H).
    econstructor; eauto.
    repeat match goal with
           | H : per_univ_elem i _ ?a ?b |- _ =>
               tryif unify a b
               then fail
               else
                 assert (per_univ_elem i _ a a) by
                   eauto using per_univ_sym, per_univ_trans;
               assert (per_univ_elem i _ b b) by
                 eauto using per_univ_sym, per_univ_trans;
               fail_if_dup
           end.
    deepexec H2 ltac:(fun H => pose proof H).
    trivial.
Qed.

Lemma per_elem_subtyping_gen : forall a b i a' b' R R' m n,
    {{ Sub a <: b at i }} ->
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈≈ b' ∈ per_univ_elem i ↘ R' }} ->
    R m n ->
    R' m n.
Proof.
  intros.
  eapply per_elem_subtyping; saturate_refl; try eassumption.
Qed.

Lemma per_subtyp_refl : forall a b i R,
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub a <: b at i }} /\ {{ Sub b <: a at i }}.
Proof.
  simpl; induction 1 using per_univ_elem_ind;
    subst;
    mauto;
    destruct_all.

  assert ({{ DF Π a ρ B ≈≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }})
           by (eapply per_univ_elem_pi'; eauto; intros; destruct_rel_mod_eval; mauto).
  repeat match goal with
         | H : ?R ?a ?b |- _ =>
             tryif unify a b
             then fail
             else
               directed pose proof (PER_refl1 _ _ _ _ _ H);
             directed pose proof (PER_refl2 _ _ _ _ _ H);
             fail_if_dup
         end.
  split; econstructor; eauto.
  - intros;
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      trivial.
  - intros. symmetry in H12.
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      trivial.
Qed.

Lemma per_subtyp_refl1 : forall a b i R,
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub a <: b at i }}.
Proof.
  intros.
  apply per_subtyp_refl in H.
  firstorder.
Qed.

#[export]
Hint Resolve per_subtyp_refl1 : mctt.

Lemma per_subtyp_refl2 : forall a b i R,
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Sub b <: a at i }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_refl2 : mctt.


Inductive sub_trans_measure : domain -> Prop :=
| stm_neut : forall a b,
    sub_trans_measure d{{{ ⇑ a b }}}
| stm_nat :
  sub_trans_measure d{{{ ℕ }}}
| stm_univ : forall i,
    sub_trans_measure d{{{ 𝕌 @ i }}}
| stm_pi : forall a ρ B i in_rel,
    sub_trans_measure a ->
    {{ DF a ≈≈ a ∈ per_univ_elem i ↘ in_rel }} ->
    (forall c b : domain,
        {{ Dom c ≈≈ c ∈ in_rel }} ->
        {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
        sub_trans_measure b) ->
    sub_trans_measure d{{{ Π a ρ B }}}.

#[local]
  Hint Constructors sub_trans_measure : mctt.

Lemma sub_trans_measure_exists : forall A1 A2 i R,
    {{ DF A1 ≈≈ A2 ∈ per_univ_elem i ↘ R }} ->
    sub_trans_measure A1.
Proof.
  simpl. induction 1 using per_univ_elem_ind; mauto.
  saturate_refl.
  econstructor; mauto; intros.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  trivial.
Qed.

Lemma per_subtyp_trans' : forall A2,
    sub_trans_measure A2 ->
    forall A1 A3 i,
      {{ Sub A1 <: A2 at i }} ->
      {{ Sub A2 <: A3 at i }} ->
      {{ Sub A1 <: A3 at i }}.
Proof.
  induction 1; intros ? ? ? Hsub1 Hsub2; simpl in *.
  1-3:progressive_inversion;
  mauto.
  - econstructor; lia.
  - dependent destruction Hsub1.
    dependent destruction Hsub2.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    intros.
    deepexec per_elem_subtyping ltac:(fun H => pose proof H).
    saturate_refl.
    directed invert_per_univ_elem H9.
    directed invert_per_univ_elem H10.
    destruct_rel_mod_eval.
    functional_eval_rewrite_clear.
    deepexec (H4 c c') ltac:(fun H => pose proof H).
    deepexec (H8 c' c') ltac:(fun H => pose proof H).
    eapply H2; apply_equiv_left; eauto.
Qed.

Lemma per_subtyp_trans : forall A1 A2 A3 i,
    {{ Sub A1 <: A2 at i }} ->
    {{ Sub A2 <: A3 at i }} ->
    {{ Sub A1 <: A3 at i }}.
Proof.
  intros.
  destruct (per_subtyp_to_univ_elem _ _ _ H0) as [? [? []]].
  eauto using per_subtyp_trans', sub_trans_measure_exists.
Qed.

#[export]
Hint Resolve per_subtyp_trans : mctt.

#[export]
Instance per_subtyp_trans_ins i : Transitive (per_subtyp i).
Proof.
  eauto using per_subtyp_trans.
Qed.

Lemma per_subtyp_transp : forall a b i a' b' R R',
    {{ Sub a <: b at i }} ->
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ DF b ≈≈ b' ∈ per_univ_elem i ↘ R' }} ->
    {{ Sub a' <: b' at i }}.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

Lemma per_subtyp_cumu : forall a1 a2 i,
    {{ Sub a1 <: a2 at i }} ->
    forall j,
      i <= j ->
      {{ Sub a1 <: a2 at j }}.
Proof.
  induction 1; intros; econstructor; mauto.
  lia.
Qed.

#[export]
Hint Resolve per_subtyp_cumu : mctt.

Lemma per_subtyp_cumu_left : forall a1 a2 i j,
    {{ Sub a1 <: a2 at i }} ->
    {{ Sub a1 <: a2 at max i j }}.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

Lemma per_subtyp_cumu_right : forall a1 a2 i j,
    {{ Sub a1 <: a2 at i }} ->
    {{ Sub a1 <: a2 at max j i }}.
Proof.
  intros. eapply per_subtyp_cumu; try eassumption.
  lia.
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof with mautosolve.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity...
Qed.

Add Parametric Morphism : per_ctx_env
    with signature (@relation_equivalence env) ==> (@relation_equivalence ctx) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

Lemma per_ctx_env_right_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ ≈≈ Δ' ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof with (destruct_rel_typ; handle_per_univ_elem_irrel; eexists; intuition).
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    inversion Hright; subst;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros ρ ρ'.
  split; intros [].
  - assert {{ Dom ρ ↯ ≈≈ ρ' ↯ ∈ tail_rel0 }} by intuition...
  - assert {{ Dom ρ ↯ ≈≈ ρ' ↯ ∈ tail_rel }} by intuition...
Qed.

Lemma per_ctx_env_sym : forall Γ Δ R,
    {{ DF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈≈ Γ ∈ per_ctx_env ↘ R }} /\
      (forall ρ ρ',
          {{ Dom ρ ≈≈ ρ' ∈ R }} ->
          {{ Dom ρ' ≈≈ ρ ∈ R }}).
Proof with solve [intuition].
  simpl.
  induction 1; split; simpl in *; destruct_conjs; try econstructor; intuition;
    pose proof (@relation_equivalence_pointwise env).
  - assert (tail_rel ρ' ρ) by eauto.
    assert (tail_rel ρ ρ) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    econstructor; eauto.
    symmetry...
  - apply_relation_equivalence.
    destruct_conjs.
    assert (tail_rel d{{{ ρ' ↯ }}} d{{{ ρ ↯ }}}) by eauto.
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ ↯ }}}) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    eexists; symmetry; handle_per_univ_elem_irrel; intuition.
Qed.

Corollary per_ctx_sym : forall Γ Δ R,
    {{ DF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ ≈≈ Γ ∈ per_ctx_env ↘ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_env_sym : forall Γ Δ R ρ ρ',
    {{ DF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ Dom ρ ≈≈ ρ' ∈ R }} ->
    {{ Dom ρ' ≈≈ ρ ∈ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_ctx_env_left_irrel : forall Γ Γ' Δ R R',
    {{ DF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ' ≈≈ Δ ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel : forall Γ Δ Δ' R R',
    {{ DF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ DF Δ' ≈≈ Γ ∈ per_ctx_env ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : {{ DF ^?Γ ≈≈ ^_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ^?Γ ≈≈ ^_ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^_ ≈≈ ^?Δ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ^_ ≈≈ ^?Δ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^?Γ ≈≈ ^_ ∈ per_ctx_env ↘ ?R1 }},
        H2 : {{ DF ^_ ≈≈ ^?Γ ∈ per_ctx_env ↘ ?R2 }} |- _ =>
        (** Order matters less here as H1 and H2 cannot be exchanged *)
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    end.

Ltac do_per_ctx_env_irrel_assert :=
  repeat do_per_ctx_env_irrel_assert1.

Ltac handle_per_ctx_env_irrel :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Lemma per_ctx_env_trans : forall Γ1 Γ2 R,
    {{ DF Γ1 ≈≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    (forall Γ3,
        {{ DF Γ2 ≈≈ Γ3 ∈ per_ctx_env ↘ R }} ->
        {{ DF Γ1 ≈≈ Γ3 ∈ per_ctx_env ↘ R }}) /\
      (forall ρ1 ρ2 ρ3,
          {{ Dom ρ1 ≈≈ ρ2 ∈ R }} ->
          {{ Dom ρ2 ≈≈ ρ3 ∈ R }} ->
          {{ Dom ρ1 ≈≈ ρ3 ∈ R }}).
Proof with solve [eauto using per_univ_trans].
  simpl.
  induction 1; subst;
    [> split;
     [ inversion 1; subst; eauto
     | intros; destruct_conjs; eauto] ..];
    pose proof (@relation_equivalence_pointwise env);
    handle_per_ctx_env_irrel;
    try solve [intuition].
  - econstructor; only 4: reflexivity; eauto.
    + apply_relation_equivalence. intuition.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ.
      handle_per_univ_elem_irrel.
      econstructor; intuition.
      (** This one cannot be replaced with `etransitivity` as we need different `i`s. *)
      eapply per_univ_trans; [| eassumption]; eassumption.
  - destruct_conjs.
    assert (tail_rel d{{{ ρ1 ↯ }}} d{{{ ρ3 ↯ }}}) by eauto.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    eexists.
    apply_relation_equivalence.
    etransitivity; intuition.
Qed.

Corollary per_ctx_trans : forall Γ1 Γ2 Γ3 R,
    {{ DF Γ1 ≈≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ2 ≈≈ Γ3 ∈ per_ctx_env ↘ R }} ->
    {{ DF Γ1 ≈≈ Γ3 ∈ per_ctx_env ↘ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

Corollary per_env_trans : forall Γ1 Γ2 R ρ1 ρ2 ρ3,
    {{ DF Γ1 ≈≈ Γ2 ∈ per_ctx_env ↘ R }} ->
    {{ Dom ρ1 ≈≈ ρ2 ∈ R }} ->
    {{ Dom ρ2 ≈≈ ρ3 ∈ R }} ->
    {{ Dom ρ1 ≈≈ ρ3 ∈ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

#[export]
Instance per_ctx_PER {R} : PER (per_ctx_env R).
Proof.
  split.
  - auto using per_ctx_sym.
  - eauto using per_ctx_trans.
Qed.

#[export]
Instance per_env_PER {R Γ Δ} (H : per_ctx_env R Γ Δ) : PER R.
Proof.
  split.
  - pose proof (fun ρ ρ' => per_env_sym _ _ _ ρ ρ' H); auto.
  - pose proof (fun ρ0 ρ1 ρ2 => per_env_trans _ _ _ ρ0 ρ1 ρ2 H); eauto.
Qed.

(** This lemma removes the PER argument *)
Lemma per_ctx_env_cons' : forall {Γ Γ' i A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ tail_rel }}), relation domain)
                             env_rel,
    {{ EF Γ ≈≈ Γ' ∈ per_ctx_env ↘ tail_rel }} ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ tail_rel }}),
        rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> fun ρ ρ' =>
         exists (equiv_ρ_drop_ρ'_drop : {{ Dom ρ ↯ ≈≈ ρ' ↯ ∈ tail_rel }}),
           {{ Dom ^(ρ 0) ≈≈ ^(ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop }}) ->
    {{ EF Γ, A ≈≈ Γ', A' ∈ per_ctx_env ↘ env_rel }}.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve per_ctx_env_cons' : mctt.

Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Lemma per_ctx_env_cons_clean_inversion : forall {Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈≈ Γ' ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ EF Γ, A ≈≈ Γ', A' ∈ per_ctx_env ↘ env_relΓA }} -> 
    exists i (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ env_relΓ }}), relation domain),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ env_relΓ }}),
          rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> fun ρ ρ' =>
             exists (equiv_ρ_drop_ρ'_drop : {{ Dom ρ ↯ ≈≈ ρ' ↯ ∈ env_relΓ }}),
               {{ Dom ^(ρ 0) ≈≈ ^(ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop }}).
Proof with intuition.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ i A ρ A' ρ' R ->
                          {{ Dom m ≈≈ m' ∈ R }}).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_univ_elem_morphism_iff; eauto.
    split; intros...
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
  - intros ρ ρ'.
    split; intros; destruct_conjs;
      assert {{ Dom ρ ↯ ≈≈ ρ' ↯ ∈ tail_rel }} by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve eexists; intros...
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
Qed.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; deex_in H; destruct H as [])
  + (inversion H; subst).

Lemma per_ctx_respects_length : forall {Γ Γ'},
    {{ Exp Γ ≈≈ Γ' ∈ per_ctx }} ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.

Lemma per_ctx_subtyp_respects_length : forall {Γ Δ},
    {{ SubE Γ <: Δ }} ->
    length Γ = length Δ.
Proof.
  intros * H.
  induction H; simpl; congruence.
Qed.

Lemma per_ctx_subtyp_to_env : forall Γ Δ,
    {{ SubE Γ <: Δ }} ->
    exists R R',
      {{ EF Γ ≈≈ Γ ∈ per_ctx_env ↘ R }} /\
        {{ EF Δ ≈≈ Δ ∈ per_ctx_env ↘ R' }}.
Proof.
  destruct 1; destruct_all.
  - repeat eexists; econstructor; apply Equivalence_Reflexive.
  - eauto.
Qed.

Lemma per_ctx_env_subtyping : forall Γ Δ,
    {{ SubE Γ <: Δ }} ->
    forall R R' ρ ρ',
      {{ EF Γ ≈≈ Γ ∈ per_ctx_env ↘ R }} ->
      {{ EF Δ ≈≈ Δ ∈ per_ctx_env ↘ R' }} ->
      R ρ ρ' ->
      R' ρ ρ'.
Proof.
  induction 1; intros;
    handle_per_ctx_env_irrel;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    apply_relation_equivalence;
    trivial.

  destruct_all.
  assert {{ Dom ρ ↯ ≈≈ ρ' ↯ ∈ tail_rel0 }} by intuition.
  unshelve eexists; [eassumption |].
  destruct_rel_typ.
  eapply per_elem_subtyping with (i := max i1 (max i0 i)); try eassumption.
  - eauto using per_subtyp_cumu_right.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left.
  - saturate_refl.
    eauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
Qed.

Lemma per_ctx_subtyp_refl1 : forall Γ Δ R,
    {{ EF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ SubE Γ <: Δ }}.
Proof.
  induction 1; mauto.

  assert (exists R, {{ EF Γ , A ≈≈ Γ' , A' ∈ per_ctx_env ↘ R }}) by
    (eexists; eapply per_ctx_env_cons'; eassumption).
  destruct_all.
  econstructor; try solve [saturate_refl; mauto 2].
  intros.
  destruct_rel_typ.
  simplify_evals.
  eauto using per_subtyp_refl1.
Qed.

Lemma per_ctx_subtyp_refl2 : forall Γ Δ R,
    {{ EF Γ ≈≈ Δ ∈ per_ctx_env ↘ R }} ->
    {{ SubE Δ <: Γ }}.
Proof.
  intros. symmetry in H. eauto using per_ctx_subtyp_refl1.
Qed.

Lemma per_ctx_subtyp_trans : forall Γ1 Γ2,
    {{ SubE Γ1 <: Γ2 }} ->
    forall Γ3,
      {{ SubE Γ2 <: Γ3 }} ->
      {{ SubE Γ1 <: Γ3 }}.
Proof.
  induction 1; intros;
    (on_all_hyp: fun H => directed invert_per_ctx_env H);
    mauto 1;
    clear_PER.

  handle_per_ctx_env_irrel.
  econstructor; try eassumption.
  - firstorder.
  - instantiate (1 := max i i0).
    intros.
    assert {{ Dom ρ ≈≈ ρ' ∈ tail_rel0 }} by (eapply per_ctx_env_subtyping; revgoals; eassumption).
    saturate_refl_for tail_rel.
    destruct_rel_typ.
    handle_per_univ_elem_irrel.
    etransitivity.
    + intuition mauto using per_subtyp_cumu_left.
    + intuition mauto using per_subtyp_cumu_right.
  - econstructor; intuition.
    + typeclasses eauto.
    + solve_refl.
Qed.

#[export]
Hint Resolve per_ctx_subtyp_trans : mctt.

#[export]
Instance per_ctx_subtyp_trans_ins : Transitive per_ctx_subtyp.
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.
