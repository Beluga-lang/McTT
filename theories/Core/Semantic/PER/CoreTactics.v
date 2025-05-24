From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.Definitions.
Import Domain_Notations.

Ltac lazy_destruct H H' :=
  match type of H with
  | forall _ _ _, exists _, _ => pose proof (H _ _ H'); deex_once
  | _ => destruct (H _ _ H') as []
  end.

Ltac destruct_rel_by_assumption in_rel H :=
  repeat
    match goal with
    | H' : {{ Dom ^?c ≈ ^?c' ∈ ?in_rel0 }} |- _ =>
        unify in_rel0 in_rel;
        lazy_destruct H H';
        destruct_all;
        mark_with H' 1
    end;
  unmark_all_with 1.

Ltac destruct_rel_mod_eval :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_eval _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_eval _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_rel_mod_app :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_app _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_app _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_rel_typ :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_typ _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_typ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

(** Universe/Element PER Helper Tactics *)

Ltac basic_invert_per_univ_elem H :=
  progress simp per_univ_elem in H;
  dependent destruction H;
  try rewrite <- per_univ_elem_equation_1 in *.

Ltac basic_per_univ_elem_econstructor :=
  progress simp per_univ_elem;
  econstructor;
  try rewrite <- per_univ_elem_equation_1 in *.
