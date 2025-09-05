From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import WPER.
Import Domain_Notations.

Ltac eexists_rel_exp :=
  eexists;
  eexists; [eassumption |];
  eexists.

Ltac eexists_rel_exp_with i :=
  eexists;
  eexists; [eassumption |];
  exists i.

Ltac eexists_rel_sub :=
  eexists;
  eexists; [eassumption |];
  eexists;
  eexists; [eassumption |].

Ltac eexists_subtyp :=
  eexists;
  eexists; [eassumption |];
  eexists.

Ltac eexists_subtyp_with i :=
  eexists;
  eexists; [eassumption |];
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
