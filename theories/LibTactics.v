From Coq Require Export Equivalence Lia Morphisms Program.Equality Program.Tactics Relation_Definitions RelationClasses.
From Equations Require Export Equations.

Open Scope predicate_scope.

Create HintDb mctt discriminated.

(** Transparency setting for generalized rewriting *)
#[export]
Typeclasses Transparent arrows.

(** Destruct existential quantification but keeps the name *)
Ltac deex_once_in H :=
  match type of H with
    | exists (name:_), _ =>
      let name' := fresh name in
      destruct H as [name' H]
    end.

Ltac deex_in H :=
  repeat deex_once_in H.

Ltac deex_once :=
  match goal with
    | [ H: exists (name:_), _ |- _ ] => deex_once_in H
    end.

Ltac deex := repeat deex_once.

(** *** Generalization of Variables *)

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.

(** *** Marking-based Tactics *)

Definition __mark__ (n : nat) A (a : A) : A := a.
Arguments __mark__ n {A} a : simpl never.

Ltac mark H :=
  let t := type of H in
  fold (__mark__ 0 t) in H.
Ltac unmark H := unfold __mark__ in H.

Ltac mark_all :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ _ => fail 2 end); mark H
  end.
Ltac unmark_all := unfold __mark__ in *.

Ltac mark_with H n :=
  let t := type of H in
  fold (__mark__ n t) in H.
Ltac mark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ _ => fail 2 end); mark_with H n
  end.
Ltac unmark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    match P with __mark__ ?n' _ => tryif unify n n' then unmark H else fail 1 end
  end.

Ltac on_all_marked_hyp tac :=
  repeat match goal with
    | [ H : __mark__ _ ?A |- _ ] => unmark H; tac H
    end.
Ltac on_all_marked_hyp_rev tac :=
  repeat match reverse goal with
    | [ H : __mark__ _ ?A |- _ ] => unmark H; tac H
    end.
Tactic Notation "on_all_marked_hyp:" tactic4(tac) := on_all_marked_hyp tac; unmark_all_with 0.
Tactic Notation "on_all_marked_hyp_rev:" tactic4(tac) := on_all_marked_hyp_rev tac; unmark_all_with 0.
Tactic Notation "on_all_hyp:" tactic4(tac) :=
  mark_all_with 0; (on_all_marked_hyp: tac).
Tactic Notation "on_all_hyp_rev:" tactic4(tac) :=
  mark_all_with 0; (on_all_marked_hyp_rev: tac).

(** *** Simple helper *)

Ltac destruct_logic :=
  destruct_one_pair
  || deex_once
  || match goal with
    | [ H : ?X \/ ?Y |- _ ] => destruct H
    | [ ev : { _ } + { _ } |- _ ] => destruct ev
    | [ ev : _ + { _ } |- _ ] => destruct ev
    | [ ev : _ + _ |- _ ] => destruct ev
    end.

Ltac destruct_all := repeat destruct_logic.

Ltac not_let_bind name :=
  match goal with
  | [x := _ |- _] =>
      lazymatch name with
      | x => fail 1
      | _ => fail
      end
  | _ => idtac
  end.

Ltac find_dup_hyp tac non :=
  match goal with
  | [ H : ?X, H' : ?X |- _ ] =>
    not_let_bind H;
    not_let_bind H';
    let T := type of X in
    unify T Prop;
    tac H H' X
  | _ => non
  end.

Ltac fail_at_if_dup n :=
  find_dup_hyp ltac:(fun H H' X => fail n "dup hypothesis" H "and" H' ":" X)
                      ltac:(idtac).

Ltac fail_if_dup := fail_at_if_dup ltac:(1).

Ltac clear_dups :=
  repeat find_dup_hyp ltac:(fun H H' _ => clear H || clear H')
                             ltac:(idtac).

Ltac directed tac :=
  let ng := numgoals in
  tac;
  let ng' := numgoals in
  guard ng' <= ng.

Tactic Notation "directed" tactic2(tac) := directed tac.

Ltac progressive_invert H :=
  (** We use dependent destruction as it is more general than inversion *)
  directed dependent destruction H.

#[local]
Ltac progressive_invert_once H n :=
  let T := type of H in
  lazymatch T with
  | __mark__ _ _ => fail
  | forall _, _ => fail
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => idtac
  | Type => idtac
  end;
  directed inversion H;
  simplify_eqs;
  clear_refl_eqs;
  clear_dups;
  try mark_with H n.

#[global]
Ltac progressive_inversion :=
  clear_dups;
  repeat match goal with
    | H : _ |- _ =>
        progressive_invert_once H 100
    end;
  unmark_all_with 100.

Ltac clean_replace_by exp0 exp1 tac :=
  tryif unify exp0 exp1
  then fail
  else
    (let H := fresh "H" in
     assert (exp0 = exp1) as H by ltac:(tac);
     subst;
     try rewrite <- H in *).

Tactic Notation "clean" "replace" uconstr(exp0) "with" uconstr(exp1) "by" tactic3(tac) := clean_replace_by exp0 exp1 tac.

#[global]
Ltac find_head t :=
  lazymatch t with
  | ?t' _ => find_head t'
  | _ => t
  end.

Ltac unify_by_head_of t head :=
  match t with
  | ?X _ _ _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ => unify X head
  | ?X _ _ _ _ => unify X head
  | ?X _ _ _ => unify X head
  | ?X _ _ => unify X head
  | ?X _ => unify X head
  | ?X => unify X head
  end.

Ltac match_by_head1 head tac :=
  match goal with
  | [ H : ?T |- _ ] => unify_by_head_of T head; tac H
  end.
Ltac match_by_head head tac := repeat (match_by_head1 head ltac:(fun H => tac H; try mark H)); unmark_all.

Ltac inversion_by_head head := match_by_head head ltac:(fun H => inversion H).
Ltac dir_inversion_by_head head := match_by_head head ltac:(fun H => directed inversion H).
Ltac inversion_clear_by_head head := match_by_head head ltac:(fun H => inversion_clear H).
Ltac dir_inversion_clear_by_head head := match_by_head head ltac:(fun H => directed inversion_clear H).
Ltac destruct_by_head head := match_by_head head ltac:(fun H => destruct H).
Ltac dir_destruct_by_head head := match_by_head head ltac:(fun H => directed destruct H).

(** *** McTT automation *)

Tactic Notation "mauto" :=
  eauto with mctt core.

Tactic Notation "mauto" int_or_var(pow) :=
  eauto pow with mctt core.

Tactic Notation "mauto" "using" uconstr(use) :=
  eauto using use with mctt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) :=
  eauto using use1, use2 with mctt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) :=
  eauto using use1, use2, use3 with mctt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) "," uconstr(use4) :=
  eauto using use1, use2, use3, use4 with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use) :=
  eauto pow using use with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) :=
  eauto pow using use1, use2 with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) :=
  eauto pow using use1, use2, use3 with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) "," uconstr(use4) :=
  eauto pow using use1, use2, use3, use4 with mctt core.

Ltac mautosolve_impl pow := unshelve solve [mauto pow]; solve [constructor].

Tactic Notation "mautosolve" := mautosolve_impl integer:(5).
Tactic Notation "mautosolve" int_or_var(pow) := mautosolve_impl pow.

(** Improve type class resolution for Equivalence and PER *)

#[export]
Hint Extern 1 => eassumption : typeclass_instances.

#[export]
Hint Extern 1 (@Reflexive _ (@predicate_equivalence _)) => simple apply @Equivalence_Reflexive : typeclass_instances.
#[export]
Hint Extern 1 (@Symmetric _ (@predicate_equivalence _)) => simple apply @Equivalence_Symmetric : typeclass_instances.
#[export]
Hint Extern 1 (@Transitive _ (@predicate_equivalence _)) => simple apply @Equivalence_Transitive : typeclass_instances.
#[export]
Hint Extern 1 (@Transitive _ (@predicate_implication _)) => simple apply @PreOrder_Transitive : typeclass_instances.


(** Default setting for [intuition] tactic *)
Ltac Tauto.intuition_solver ::= auto with mctt core solve_subterm.

Ltac exvar T tac :=
  lazymatch type of T with
  | Prop =>
      let H := fresh "H" in
      unshelve evar (H : T);
      [|
        let H' := eval unfold H in H in
          clear H; tac H']
  | _ =>
      let x := fresh "x" in
      evar (x : T);
      let x' := eval unfold x in x in
        clear x; tac x'
  end.

(** this tactic traverses to the bottom of a lemma following universals and conjunctions to the bottom and apply a tactic *)
Ltac deepexec lem tac :=
  let T := type of lem in
  let T' := eval simpl in T in
  let ST := eval unfold iff in T' in
  match ST with
  | _ /\ _ => deepexec constr:(proj1 lem) tac
            || deepexec constr:(proj2 lem) tac
  | forall _ : ?T, _ =>
      exvar T ltac:(fun x =>
                      lazymatch type of T with
                      | Prop => match goal with
                            | H : _ |- _ => unify x H; deepexec constr:(lem x) tac
                            | _ => deepexec constr:(lem x) tac
                            end
                      | _ => deepexec constr:(lem x) tac
                      end)
  | _ => tac lem
  end.

(** this tactic is similar to above, but the traversal cuts off when it sees an assumption applicable to a cut-off argument C *)
Ltac cutexec lem C tac :=
  let CT := type of C in
  let T := type of lem in
  let T' := eval simpl in T in
  let ST := eval unfold iff in T' in
  lazymatch ST with
  | _ /\ _ => cutexec constr:(proj1 lem) C tac
            || cutexec constr:(proj2 lem) C tac
  | forall _ : ?T, _ =>
      exvar T ltac:(fun x =>
                      tryif unify T CT
                      then
                        unify x C;
                        tac lem
                      else
                        lazymatch type of T with
                         | Prop => match goal with
                               | H : _ |- _ => unify x H; cutexec constr:(lem x) C tac
                               | _ => cutexec constr:(lem x) C tac
                               end
                         | _ => cutexec constr:(lem x) C tac
                         end)
  | _ => tac lem
  end.


Ltac unify_args H P :=
  lazymatch P with
  | ?P' ?x =>
      let r := unify_args H P' in
      constr:(r x)
  | _ => H
  end.

#[global]
Ltac strong_apply H X :=
  let H' := fresh "H" in
  let T := type of X in
  let R := unify_args H T in
  cutexec R X ltac:(fun L => pose proof (L X) as H'; simpl in H'; clear X; rename H' into X).

#[global]
Ltac apply_equiv_left1 :=
  let tac1 := fun H R H1 T => (let h := find_head T in unify R h; strong_apply H H1) in
  let tac2 := fun H R G => (let h := find_head G in unify R h; apply H; simpl) in
  match goal with
  | H : ?R <∙> _, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : relation_equivalence ?R _, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : ?R <∙> _ |- ?G => progress tac2 H R G
  | H : relation_equivalence ?R _ |- ?G => progress tac2 H R G
  end.

#[global]
Ltac apply_equiv_left := repeat apply_equiv_left1.

#[global]
Ltac apply_equiv_right1 :=
  let tac1 := fun H R H1 T => (let h := find_head T in unify R h; strong_apply H H1) in
  let tac2 := fun H R G => (let h := find_head G in unify R h; apply H; simpl) in
  match goal with
  | H : _ <∙> ?R, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : relation_equivalence _ ?R, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : _ <∙> ?R |- ?G => progress tac2 H R G
  | H : relation_equivalence _ ?R |- ?G => progress tac2 H R G
  end.

#[global]
Ltac apply_equiv_right := repeat apply_equiv_right1.

#[global]
Ltac clear_PER :=
  repeat match goal with
    | H : PER _ |- _ => clear H
    | H : Symmetric _ |- _ => clear H
    | H : Transitive _ |- _ => clear H
    end.


Lemma PER_refl1 A (R : relation A) `(per : PER A R) : forall a b, R a b -> R a a.
Proof.
  intros.
  etransitivity; [eassumption |].
  symmetry. assumption.
Qed.

Lemma PER_refl2 A (R : relation A) `(per : PER A R) : forall a b, R a b -> R b b.
Proof.
  intros. symmetry in H.
  apply PER_refl1 in H;
    auto.
Qed.

#[global]
Ltac saturate_refl :=
  repeat match goal with
    | H : ?R ?a ?b |- _ =>
        tryif unify a b
        then fail
        else
          directed pose proof (PER_refl1 _ _ _ _ _ H);
        directed pose proof (PER_refl2 _ _ _ _ _ H);
        fail_if_dup
    end.

#[global]
Ltac saturate_refl_for hd :=
  repeat match goal with
    | H : ?R ?a ?b |- _ =>
        unify_by_head_of R hd;
        tryif unify a b
        then fail
        else
          directed pose proof (PER_refl1 _ _ _ _ _ H);
        directed pose proof (PER_refl2 _ _ _ _ _ H);
        fail_if_dup
    end.

#[global]
Ltac solve_refl :=
  (** Sometimes `reflexivity` does not work as (simple) unification fails for some unknown reason.
      Thus, we try [Equivalence_Reflexive] as well. *)
  solve [reflexivity || apply Equivalence_Reflexive].

(** *** Helper Instances for Generalized Rewriting *)
#[export]
Hint Extern 1 (subrelation (@predicate_equivalence ?Ts) _) => (let H := fresh "H" in intros ? ? H; exact H) : typeclass_instances.

#[export]
Hint Extern 1 (subrelation iff Basics.impl) => exact iff_impl_subrelation : typeclass_instances.

#[export]
Hint Extern 1 (subrelation iff (Basics.flip Basics.impl)) => exact iff_flip_impl_subrelation : typeclass_instances.

#[export]
Hint Extern 1 (subrelation (@relation_equivalence ?A) _) => (let H := fresh "H" in intros ? ? H; exact H) : typeclass_instances.

#[export]
Hint Extern 1 (subrelation (@predicate_implication ?Ts) _) => (let H := fresh "H" in intros ? ? H; exact H) : typeclass_instances.

#[export]
Hint Extern 1 (subrelation (@subrelation ?A) _) => (let H := fresh "H" in intros ? ? H; exact H) : typeclass_instances.

#[export]
Instance predicate_implication_equivalence Ts : subrelation (@predicate_equivalence Ts) (@predicate_implication Ts).
Proof.
  induction Ts; firstorder eauto 2.
Qed.

Add Parametric Morphism Ts : (@predicate_implication Ts)
    with signature (@predicate_equivalence Ts) ==> (@predicate_equivalence Ts) ==> iff as predicate_implication_morphism.
Proof.
  induction Ts; split; intros; try firstorder.
  - rewrite <- H.
    transitivity x0; try eassumption.
    rewrite H0; reflexivity.
  - rewrite H.
    transitivity y0; try eassumption.
    rewrite <- H0; reflexivity.
Qed.

Add Parametric Morphism A : PER
    with signature (@relation_equivalence A) ==> iff as PER_morphism.
Proof.
  split; intros []; econstructor; unfold Symmetric, Transitive in *; intuition.
Qed.

(** The following facility converts search of Proper from type class instances to the local context *)

Class PERElem (A : Type) (P : A -> Prop) (R : A -> A -> Prop) :=
  per_elem : forall a, P a -> R a a.

#[export]
Instance PERProper (A : Type) (P : A -> Prop) (R : A -> A -> Prop) `(Ins : PERElem A P R) a (H : P a) :
  Proper R a.
Proof.
  cbv. pose proof per_elem; auto.
Qed.


Ltac bulky_rewrite1 :=
  match goal with
  | H : _ |- _ => rewrite H
  | _ => progress (autorewrite with mctt)
  end.

Ltac bulky_rewrite := repeat (bulky_rewrite1; mauto 2).

Ltac bulky_rewrite_in1 HT :=
  match goal with
  | H : _ |- _ => tryif unify H HT then fail else rewrite H in HT
  | _ => progress (autorewrite with mctt in HT)
  end.

Ltac bulky_rewrite_in HT := repeat (bulky_rewrite_in1 HT; mauto 2).


(** This tactic provides a trivial proof for the completeness of a decision procedure. *)
Ltac dec_complete :=
  lazymatch goal with
  | |- exists _, ?L = _ =>
      lazymatch type of L with
      | sumbool _ _ =>
          let Heq := fresh "Heq" in
          destruct L eqn:Heq; eauto;
          contradiction
      end
  end.
