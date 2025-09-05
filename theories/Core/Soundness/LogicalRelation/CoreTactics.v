From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness.LogicalRelation Require Import Definitions.

Ltac basic_invert_glu_univ_elem H :=
  progress simp glu_univ_elem in H;
  dependent destruction H;
  try rewrite <- glu_univ_elem_equation_1 in *.

(* TODO: unify with the uip version above *)
Ltac basic_invert_glu_univ_elem_nouip H :=
  progress simp glu_univ_elem in H;
  (* TODO: change the following line to `dependent inversion_clear H;` fails some proofs currently *)
  inversion H; subst;
  try rewrite <- glu_univ_elem_equation_1 in *.

Ltac basic_glu_univ_elem_econstructor :=
  progress simp glu_univ_elem;
  econstructor;
  try rewrite <- glu_univ_elem_equation_1 in *.

Ltac invert_glu_rel1 :=
  match goal with
  | H : pi_glu_typ_pred _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : pi_glu_exp_pred _ _ _ _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : sigma_glu_typ_pred _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : sigma_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : eq_glu_typ_pred _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : eq_glu_exp_pred _ _ _ _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_typ_pred _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_exp_pred _ _ _ _ _ _ |- _ =>
      progressive_invert H
  end.

Ltac clear_glu_ctx Δ := 
  repeat 
  match goal with
  | H: ?SbΓ Δ ?σ ?ρ |- _ =>
      match type of SbΓ with
      | glu_sub_pred => clear H
      end
  end.
