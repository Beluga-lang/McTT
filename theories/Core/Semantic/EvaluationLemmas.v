From Coq Require Import Lia PeanoNat Relations.
From Mcltt Require Import Base LibTactics EvaluationDefinitions.
Import Domain_Notations.

Section functional_eval.
  Let functional_eval_exp_prop M p m1 (_ : {{ ⟦ M ⟧ p ↘ m1 }}) : Prop := forall m2 (Heval2: {{ ⟦ M ⟧ p ↘ m2 }}), m1 = m2.
  Let functional_eval_natrec_prop A MZ MS m p r1 (_ : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r1 }}) : Prop := forall r2 (Heval2 : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r2 }}), r1 = r2.
  Let functional_eval_app_prop m n r1 (_ : {{ $| m & n |↘ r1 }}) : Prop := forall r2 (Heval2 : {{ $| m & n |↘ r2 }}), r1 = r2.
  Let functional_eval_sub_prop σ p p1 (_ : {{ ⟦ σ ⟧s p ↘ p1 }}) : Prop := forall p2 (Heval2 : {{ ⟦ σ ⟧s p ↘ p2 }}), p1 = p2.

  #[local]
  Ltac unfold_functional_eval :=
    unfold functional_eval_exp_prop, functional_eval_natrec_prop, functional_eval_app_prop, functional_eval_sub_prop in *;
    clear functional_eval_exp_prop functional_eval_natrec_prop functional_eval_app_prop functional_eval_sub_prop.

  Lemma functional_eval_exp : forall M p m1 (Heval1 : {{ ⟦ M ⟧ p ↘ m1 }}), functional_eval_exp_prop M p m1 Heval1.
  Proof using.
    induction Heval1
      using eval_exp_mut_ind
      with (P0 := functional_eval_natrec_prop)
           (P1 := functional_eval_app_prop)
           (P2 := functional_eval_sub_prop);
      unfold_functional_eval; mauto;
      intros; inversion_clear Heval2; subst; do 2 f_equal;
      (on_all_hyp: fun H => try erewrite H in *; mauto); mauto.
  Qed.

  Lemma functional_eval_natrec : forall A MZ MS m p r1 (Heval1 : {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r1 }}), functional_eval_natrec_prop A MZ MS m p r1 Heval1.
  Proof using.
    induction Heval1
      using eval_natrec_mut_ind
      with (P := functional_eval_exp_prop)
           (P1 := functional_eval_app_prop)
           (P2 := functional_eval_sub_prop);
      unfold_functional_eval; mauto;
      intros; inversion Heval2; clear Heval2; subst; do 2 f_equal;
      (on_all_hyp: fun H => try erewrite H in *; mauto); mauto.
  Qed.

  Lemma functional_eval_app : forall m n r1 (Heval1 : {{ $| m & n |↘ r1 }}), functional_eval_app_prop m n r1 Heval1.
  Proof using.
    induction Heval1
      using eval_app_mut_ind
      with (P := functional_eval_exp_prop)
           (P0 := functional_eval_natrec_prop)
           (P2 := functional_eval_sub_prop);
      unfold_functional_eval; mauto;
      intros; inversion Heval2; clear Heval2; subst; do 2 f_equal;
      (on_all_hyp: fun H => try erewrite H in *; mauto); mauto.
  Qed.

  Lemma functional_eval_sub : forall σ p p1 (Heval1 : {{ ⟦ σ ⟧s p ↘ p1 }}), functional_eval_sub_prop σ p p1 Heval1.
  Proof using.
    induction Heval1
      using eval_sub_mut_ind
      with (P := functional_eval_exp_prop)
           (P0 := functional_eval_natrec_prop)
           (P1 := functional_eval_app_prop);
      unfold_functional_eval; mauto;
      intros; inversion Heval2; clear Heval2; subst; do 2 f_equal;
      (on_all_hyp: fun H => try erewrite H in *; mauto); mauto.
  Qed.
End functional_eval.

#[export]
Hint Resolve functional_eval_exp functional_eval_natrec functional_eval_app functional_eval_sub : mcltt.

Ltac functional_eval_rewrite_clear1 :=
  match goal with
  | H1 : {{ ⟦ ~?M ⟧ ~?p ↘ ~?m1 }}, H2 : {{ ⟦ ~?M ⟧ ~?p ↘ ~?m2 }} |- _ =>
      clean replace m2 with m1 by mauto; clear H2
  | H1 : {{ $| ~?m & ~?n |↘ ~?r1 }}, H2 : {{ $| ~?m & ~?n |↘ ~?r2 }} |- _ =>
      clean replace r2 with r1 by mauto; clear H2
  | H1 : {{ rec ~?m ⟦return ~?A | zero -> ~?MZ | succ -> ~?MS end⟧ ~?p ↘ ~?r1 }}, H2 : {{ rec ~?m ⟦return ~?A | zero -> ~?MZ | succ -> ~?MS end⟧ ~?p ↘ ~?r2 }} |- _ =>
      clean replace r2 with r1 by mauto; clear H2
  | H1 : {{ ⟦ ~?σ ⟧s ~?p ↘ ~?p1 }}, H2 : {{ ⟦ ~?σ ⟧s ~?p ↘ ~?p2 }} |- _ =>
      clean replace p2 with p1 by mauto; clear H2
  end.
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.
