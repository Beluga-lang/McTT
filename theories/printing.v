From Stdlib Require Import List.
From Stdlib Require Init.
Require Import MetaRocq.Template.All.
From MetaRocq.Utils Require Import utils.
Import MRMonadNotation.
Require Import MetaRocq.Common.BasicAst.
From Translation Require Import trans.

Definition fresh_var (ctx : list string) : string :=
  "x" ^ string_of_nat (List.length ctx).

Fixpoint print_exp_prec (prec : nat) (ctx : list string) (e : exp) : string :=
  let wrap s := if Nat.leb 1 prec then "(" ^ s ^ ")" else s in
  match e with
  | a_var n =>
      match List.nth_error ctx n with
      | Some name => name
      | None => "x?"
      end
  | a_typ n => "Type@" ^ string_of_nat n
  | a_nat => "Nat"
  | a_zero => "0"
  | a_succ e => wrap ("succ " ^ print_exp_prec 1 ctx e)
  | a_fn t e =>
      let x := fresh_var ctx in
      wrap ("fun (" ^ x ^ " : " ^ print_exp_prec 0 ctx t ^ ") -> "
            ^ print_exp_prec 0 (x :: ctx) e)
  | a_pi t1 t2 =>
      let x := fresh_var ctx in
      wrap ("forall (" ^ x ^ " : " ^ print_exp_prec 0 ctx t1 ^ ") -> "
            ^ print_exp_prec 0 (x :: ctx) t2)
  | a_app e1 e2 =>
      wrap (match e1 with
            | a_fn _ _ | a_pi _ _ =>
                           "(" ^ print_exp_prec 0 ctx e1 ^ ") " ^ print_exp_prec 1 ctx e2
            | _ =>
                print_exp_prec 0 ctx e1 ^ " " ^ print_exp_prec 1 ctx e2
            end)
  | a_eq t e1 e2 =>
      wrap (print_exp_prec 1 ctx e1 ^ " ={ " ^ print_exp_prec 0 ctx t
            ^ " } " ^ print_exp_prec 1 ctx e2)
  | a_refl t e =>
      wrap ("refl " ^ print_exp_prec 1 ctx t ^ " " ^ print_exp_prec 1 ctx e)
  | a_natrec n t base step =>
      let y := fresh_var ctx in
      let m := fresh_var (y :: ctx) in
      let r := fresh_var (m :: y :: ctx) in
      wrap ("rec " ^ print_exp_prec 1 ctx n
            ^ " return " ^ y ^ " . " ^ print_exp_prec 0 (y :: ctx) t
            ^ " | zero => " ^ print_exp_prec 0 ctx base
            ^ " | succ " ^ m ^ ", " ^ r ^ " => "
            ^ print_exp_prec 0 (r :: m :: y :: ctx) step
            ^ " end")
  | a_eqrec a m1 motive refl_case m2 n =>
      let x := fresh_var ctx in
      let y := fresh_var (x :: ctx) in
      let z := fresh_var (y :: x :: ctx) in
      wrap ("rec " ^ print_exp_prec 1 ctx n
            ^ " as (" ^ print_exp_prec 1 ctx m1
            ^ " ={ " ^ print_exp_prec 1 ctx a
            ^ " } " ^ print_exp_prec 1 ctx m2 ^ ")"
            ^ " return " ^ x ^ " " ^ y ^ " " ^ z
            ^ " . " ^ print_exp_prec 0 (y :: x :: z :: ctx) motive
            ^ " | refl " ^ x ^ " => " ^ print_exp_prec 0 (x :: List.tl ctx) refl_case
            ^ " end")
  | _ => "TODO"
  end.

Definition print_exp (ctx : list string) (e : exp) : string :=
  print_exp_prec 0 ctx e.
