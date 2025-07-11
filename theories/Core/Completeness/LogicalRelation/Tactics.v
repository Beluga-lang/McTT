From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.
Import Domain_Notations.

Ltac eexists_rel_exp :=
  eexists;
  split; [eassumption |];
  eexists.

Ltac eexists_rel_exp_with i :=
  eexists;
  split; [eassumption |];
  exists i.

Ltac eexists_rel_sub :=
  eexists;
  split; [eassumption |];
  eexists;
  split; [eassumption |].

Ltac eexists_subtyp :=
  eexists;
  split; [eassumption |];
  eexists.

Ltac eexists_subtyp_with i :=
  eexists;
  split; [eassumption |];
  exists i.

Ltac invert_rel_typ_body :=
  simplify_evals;
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H); subst;
  clear_dups;
  clear_refl_eqs;
  handle_per_univ_elem_irrel;
  clear_dups;
  try rewrite <- per_univ_elem_equation_1 in *.

(* TODO: unify with the uip version above *)
Ltac invert_rel_typ_body_nouip :=
  simplify_evals;
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem_nouip H); subst;
  clear_dups;
  clear_refl_eqs;
  handle_per_univ_elem_irrel;
  clear_dups;
  try rewrite <- per_univ_elem_equation_1 in *.
