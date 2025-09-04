From Coq Require Import Lia List MSets PeanoNat String FunInd.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax.

Open Scope string_scope.

Module StrSet := Make String_as_OT.
Module StrSProp := MSetProperties.Properties StrSet.

(** One cannot import notation from module type without
    restricting a module to that exact type.
    Thus, here we repeat the notation from [WSetsOn]. *)
Notation "s [<=] t" := (StrSet.Subset s t) (at level 70, no associativity).

(** De-monadify with pattern matching for now *)
Fixpoint lookup (s : string) (ctx : list string) : option nat :=
  match ctx with
  | nil => None
  | c::cs =>
      if string_dec c s
      then Some 0
      else
        match lookup s cs with
        | Some n => Some (n + 1)%nat
        | None => None
        end
  end
.

Fixpoint elaborate (cst : Cst.obj) (ctx : list string) : option exp :=
  match cst with
  | Cst.var s =>
      match lookup s ctx with
      | Some n => Some (a_var n)
      | None => None
      end
  | Cst.typ n => Some (a_typ n)
  | Cst.nat => Some a_nat
  | Cst.zero => Some a_zero
  | Cst.succ c =>
      match elaborate c ctx with
      | Some a => Some (a_succ a)
      | None => None
      end
  | Cst.natrec n mx m z sx sr s =>
      match elaborate m (mx :: ctx), elaborate z ctx, elaborate s (sr :: sx :: ctx), elaborate n ctx with
      | Some m, Some z, Some s, Some n => Some (a_natrec m z s n)
      | _, _, _, _ => None
      end
  | Cst.pi s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_pi t a)
      | _, _ => None
      end
  | Cst.fn s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_fn t a)
      | _, _ => None
      end
  | Cst.app c1 c2 =>
      match elaborate c1 ctx, elaborate c2 ctx with
      | None, _ => None
      | _, None => None
      | Some a1, Some a2 => Some (a_app a1 a2)
      end
  | Cst.sigma s t c => 
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_sigma t a)
      | _, _ => None
      end
  | Cst.pair c1 t1 c2 s t2 => 
      match elaborate c1 ctx,  elaborate t1 ctx, elaborate c2 ctx, elaborate t2 (s::ctx) with
      | Some a1, Some b1, Some a2, Some b2 => Some (a_pair a1 b1 a2 b2)
      | _, _, _, _ => None
      end
  | Cst.fst c =>
      match elaborate c ctx with
      | Some a => Some (a_fst a)
      | None => None
      end
  | Cst.snd c => 
      match elaborate c ctx with
      | Some a => Some (a_snd a)
      | None => None
      end
  | Cst.prop_eq c1 t c2 =>
      match elaborate c1 ctx, elaborate t ctx, elaborate c2 ctx with
      | Some a1, Some t, Some a2 => Some (a_eq t a1 a2)
      | _, _, _ => None
      end
  | Cst.refl t c =>
      match elaborate t ctx, elaborate c ctx with
      | Some t, Some a => Some (a_refl t a)
      | _, _ => None
      end
  | Cst.eqrec n mx my mz m rx r c1 t c2 =>
      match elaborate n ctx, elaborate m (mz :: my :: mx :: ctx), elaborate r (rx :: ctx), elaborate c1 ctx, elaborate t ctx, elaborate c2 ctx with
      | Some n, Some m, Some r, Some a1, Some t, Some a2 => Some (a_eqrec t m r a1 a2 n)
      | _, _, _, _, _, _ => None
      end
  end
.

Functional Scheme elaborate_fun_ind := Induction for elaborate Sort Prop.

Generalizable All Variables.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp (a_typ i) )
| user_exp_nat :
  `( user_exp a_nat )
| user_exp_zero :
  `( user_exp a_zero )
| user_exp_succ :
  `( user_exp M ->
     user_exp (a_succ M) )
| user_exp_natrec :
  `( user_exp A ->
     user_exp MZ ->
     user_exp MS ->
     user_exp M ->
     user_exp (a_natrec A MZ MS M) )
| user_exp_pi :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_pi A B) )
| user_exp_fn :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_fn A M) )
| user_exp_app :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_app M N) )
| user_exp_sigma : 
  `( user_exp A ->
     user_exp B ->
     user_exp (a_sigma A B) )
| user_exp_pair :
  `( user_exp M ->
     user_exp A ->
     user_exp N ->
     user_exp B ->
     user_exp (a_pair M A N B) )
| user_exp_fst :
  `( user_exp M ->
     user_exp (a_fst M) )
| user_exp_snd :
  `( user_exp M ->
     user_exp (a_snd M) )
| user_exp_eq :
  `( user_exp A ->
     user_exp M1 ->
     user_exp M2 ->
     user_exp (a_eq A M1 M2) )
| user_exp_refl :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_refl A M) )
| user_exp_eqrec :
  `( user_exp A ->
     user_exp B ->
     user_exp BR ->
     user_exp M1 ->
     user_exp M2 ->
     user_exp N ->
     user_exp (a_eqrec A B BR M1 M2 N) )
| user_exp_vlookup :
  `( user_exp (a_var x) ).

#[export]
Hint Constructors user_exp : mctt.

Lemma user_exp_nf : forall M, user_exp (nf_to_exp M)
with user_exp_ne : forall M, user_exp (ne_to_exp M).
Proof.
  - clear user_exp_nf; induction M; mauto 3.
  - clear user_exp_ne; induction M; mauto 3.
Qed.

Lemma elaborator_gives_user_exp : forall O vs M,
    elaborate O vs = Some M ->
    user_exp M.
Proof.
  intros * Heq. gen M.
  functional induction (elaborate O vs) using elaborate_fun_ind;
    intros; inversion_clear Heq; mauto 4.

  - econstructor; mauto 3.
  - econstructor; mauto 3.
  - econstructor; mauto 3.
  - econstructor; mauto 3.
Qed.

Fixpoint cst_variables (cst : Cst.obj) : StrSet.t :=
 match cst with
  | Cst.var s => StrSet.singleton s
  | Cst.typ n => StrSet.empty
  | Cst.nat => StrSet.empty
  | Cst.zero => StrSet.empty
  | Cst.succ c => cst_variables c
  | Cst.natrec n mx m z sx sy s => StrSet.union (StrSet.union (cst_variables n) (StrSet.remove mx (cst_variables m))) (StrSet.union (cst_variables z) (StrSet.remove sx (StrSet.remove sy (cst_variables s))))
  | Cst.pi s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.fn s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.app c1 c2 => StrSet.union (cst_variables c1) (cst_variables c2)
  | Cst.sigma s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.pair c1 t1 c2 s t2 => StrSet.union (StrSet.union (cst_variables c1) (cst_variables t1)) (StrSet.union (cst_variables c2) (StrSet.remove s (cst_variables t2)))
  | Cst.fst c => cst_variables c  
  | Cst.snd c => cst_variables c
  | Cst.prop_eq c1 t c2 => StrSet.union (cst_variables c1) (StrSet.union (cst_variables t) (cst_variables c2))
  | Cst.refl t c => StrSet.union (cst_variables t) (cst_variables c)
  | Cst.eqrec n mx my mz m rx r c1 t c2 => StrSet.union (cst_variables n) (StrSet.union (StrSet.remove mx (StrSet.remove my (StrSet.remove mz (cst_variables m)))) (StrSet.union (StrSet.remove rx (cst_variables r)) (StrSet.union (cst_variables c1) (StrSet.union (cst_variables t) (cst_variables c2)))))
 end
.

Inductive closed_at : exp -> nat -> Prop :=
 | ca_var : `( x < n -> closed_at (a_var x) n )
 | ca_type : `( closed_at (a_typ m) n )
 | ca_nat : `( closed_at (a_nat) n )
 | ca_zero : `( closed_at (a_zero) n )
 | ca_succ : `( closed_at a n -> closed_at (a_succ a) n )
 | ca_natrec : `( closed_at n l -> closed_at m (1+l) -> closed_at z l -> closed_at s (2+l) -> closed_at (a_natrec m z s n) l )
 | ca_pi : `( closed_at t n -> closed_at b (1+n) -> closed_at (a_pi t b) n )
 | ca_lam : `( closed_at t n -> closed_at b (1+n) -> closed_at (a_fn t b) n )
 | ca_app : `( closed_at a1 n -> closed_at a2 n -> closed_at (a_app a1 a2) n )
 | ca_sigma : `( closed_at t n -> closed_at b (1+n) -> closed_at (a_sigma t b) n )
 | ca_pair : `( closed_at a1 n -> closed_at b1 n -> closed_at a2 n -> closed_at b2 (1+n) -> closed_at (a_pair a1 b1 a2 b2) n )
 | ca_fst : `( closed_at a n -> closed_at (a_fst a) n )
 | ca_snd : `( closed_at a n -> closed_at (a_snd a) n )
 | ca_eq : `( closed_at t n -> closed_at a1 n -> closed_at a2 n -> closed_at (a_eq t a1 a2) n )
 | ca_refl : `( closed_at t n -> closed_at a n -> closed_at (a_refl t a) n )
 | ca_eqrec : `( closed_at a l -> closed_at m (3+l) -> closed_at r (1+l) -> closed_at m1 l -> closed_at m2 l -> closed_at n l -> closed_at (a_eqrec a m r m1 m2 n) l )
.
#[local]
Hint Constructors closed_at: mctt.

(** Lemma for the well_scoped proof, lookup succeeds if var is in context *)
Lemma lookup_known (s : string) (ctx : list string) (H_in : List.In s ctx) : exists n : nat, (lookup s ctx = Some n /\ n < List.length ctx).
Proof.
  induction ctx as [| c ctx' IHctx]; simpl in *.
  - contradiction.
  - destruct (string_dec c s); subst.
    + eexists; split; auto. lia.
    + destruct H_in; try contradiction.
      destruct IHctx as [? [? ?]]; [assumption |].
      rewrite H0.
      eexists; split; auto. lia.
Qed.

(** Lemma for the well_scoped proof, lookup result always less than context length *)
Lemma lookup_bound s : forall ctx m, lookup s ctx = Some m -> m < (List.length ctx).
  induction ctx.
  - intros. discriminate H.
  - intros. destruct (string_dec a s).
    + rewrite e in H.
      simpl in H.
      destruct string_dec in H.
      * inversion H.
        unfold Datatypes.length.
        apply (Nat.lt_0_succ).
      * contradiction n. reflexivity.
    + simpl in H.
      destruct string_dec in H.
      * contradiction n.
      * destruct (lookup s ctx);
          try discriminate.
        inversion H.
        rewrite H1.
        simpl.
        pose (IHctx (m-1)).
        rewrite <- H1 in l.
        rewrite (Nat.add_sub n1 1) in l.
        rewrite <- H1.
        specialize (l eq_refl).
        lia.
Qed.

Import StrSProp.Dec.

Lemma Subset_to_In : forall xs x, StrSet.singleton x [<=] StrSProp.of_list xs -> In x xs.
Proof.
  intro xs; induction xs; simpl; intros.
  - rewrite <- F.empty_iff.
    apply (H x).
    fsetdec.
  - specialize (H x).
    rewrite F.add_iff in H.
    destruct H; [fsetdec | auto |].
    right. eapply IHxs.
    intros y Hy.
    assert (y = x); fsetdec.
Qed.

(** *** Well scopedness lemma *)

(** If the set of free variables in a cst are contained in a context
    then elaboration succeeds with that context, and the result is a closed term *)
Lemma well_scoped (cst : Cst.obj) : forall ctx,  cst_variables cst [<=] StrSProp.of_list ctx  ->
exists a : exp, (elaborate cst ctx = Some a) /\ (closed_at a (List.length ctx)).
Proof.
  induction cst; intros; simpl in *; mauto.
  - (* succ *)
    destruct (IHcst _ H) as [ast [-> ?]]; mauto.
  - (* natrec *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    assert (cst_variables cst3 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst4 [<=] StrSProp.of_list (s1 :: s0 :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]];
      destruct (IHcst3 _ H2) as [ast'' [-> ?]];
      destruct (IHcst4 _ H3) as [ast''' [-> ?]]; mauto.
  - (* pi *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* fn *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* app *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list ctx) by fsetdec.
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* sigma *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
    destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* pair *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst3 [<=] StrSProp.of_list ctx) by (simpl; fsetdec).
    assert (cst_variables cst4 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
    destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
    destruct (IHcst3 _ H2) as [ast'' [-> ?]]; mauto.
    destruct (IHcst4 _ H3) as [ast''' [-> ?]]; mauto.
  - (* fst *)
    destruct (IHcst _ H) as [ast [-> ?]]; mauto.
  - (* snd *)
    destruct (IHcst _ H) as [ast [-> ?]]; mauto.
  - (* eq *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst3 [<=] StrSProp.of_list ctx) by fsetdec.
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; 
      destruct (IHcst3 _ H2) as [ast'' [-> ?]]; mauto.
  - (* refl *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list ctx) by fsetdec.
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* eqrec *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s1 :: s0 :: s :: ctx)) by (simpl; fsetdec).
    assert (cst_variables cst3 [<=] StrSProp.of_list (s2 :: ctx)) by (simpl; fsetdec).
    assert (cst_variables cst4 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst5 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst6 [<=] StrSProp.of_list ctx) by fsetdec.
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]];
      destruct (IHcst3 _ H2) as [ast'' [-> ?]];
      destruct (IHcst4 _ H3) as [ast''' [-> ?]];
      destruct (IHcst5 _ H4) as [ast'''' [-> ?]];
      destruct (IHcst6 _ H5) as [ast''''' [-> ?]]; mauto.
  - apply Subset_to_In in H.
    edestruct lookup_known as [? [-> ?]]; [auto |].
    apply (In_nth _ _ s)  in H.
    destruct H as [? [? ?]].
    mauto.
Qed.

Example test_elab : elaborate Cst.nat nil = Some a_nat.
Proof. reflexivity. Qed.

Example test_elab2 : elaborate (Cst.fn "s" Cst.nat (Cst.fn "x" Cst.nat (Cst.fn "s" Cst.nat (Cst.var "q")))) nil = None.
Proof. reflexivity. Qed.
