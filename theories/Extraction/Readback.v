From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Readback Evaluation.
From Mctt.Extraction Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

Inductive read_nf_order : nat -> domain_nf -> Prop :=
| rnf_type :
  `( read_typ_order s a ->
    read_nf_order s d{{{ ⇓ 𝕌@i a }}} )
| rnf_zero :
  `( read_nf_order s d{{{ ⇓ ℕ zero }}} )
| rnf_succ :
  `( read_nf_order s d{{{ ⇓ ℕ m }}} ->
     read_nf_order s d{{{ ⇓ ℕ (succ m) }}} )
| rnf_nat_neut :
  `( read_ne_order s m ->
     read_nf_order s d{{{ ⇓ ℕ (⇑ a m) }}} )
| rnf_fn :
  `( read_typ_order s a ->
     eval_app_order m d{{{ ⇑! a s }}} ->
     eval_exp_order B d{{{ p ↦ ⇑! a s }}} ->
     (forall m' b,
         {{ $| m & ⇑! a s |↘ m' }} ->
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
         read_nf_order (S s) d{{{ ⇓ b m' }}}) ->
     read_nf_order s d{{{ ⇓ (Π a p B) m }}} )
| rnf_pair :
  `( read_typ_order s a ->
     eval_exp_order B d{{{ p ↦ ⇑! a s }}} ->
     eval_fst_order m ->
     eval_snd_order m ->
     (forall b,
          {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
          read_typ_order (S s) b) ->
     (forall m1,
         {{ π₁ m ↘ m1 }} ->
         eval_exp_order B d{{{ p ↦ m1 }}} ) ->
     (forall m1,
         {{ π₁ m ↘ m1 }} ->
         read_nf_order s d{{{ ⇓ a m1 }}}) ->
     (forall m1 m2 b,
         {{ π₁ m ↘ m1 }} ->
         {{ π₂ m ↘ m2 }} ->
         {{ ⟦ B ⟧ p ↦ m1 ↘ b }} ->
         read_nf_order s d{{{ ⇓ b m2 }}}) ->
     read_nf_order s d{{{ ⇓ (Σ a p B) m }}} )
| rnf_refl :
  `( read_typ_order s a ->
     read_nf_order s d{{{ ⇓ a m' }}} ->
     read_nf_order s d{{{ ⇓ (Eq a m1 m2) (refl m') }}} )
| rnf_eq_neut :
  `( read_ne_order s n ->
     read_nf_order s d{{{ ⇓ (Eq a m1 m2) (⇑ b n) }}} )
| rnf_neut :
  `( read_ne_order s m ->
     read_nf_order s d{{{ ⇓ (⇑ a b) (⇑ c m) }}} )

with read_ne_order : nat -> domain_ne -> Prop :=
| rne_var :
  `( read_ne_order s d{{{ !x }}} )
| rne_app :
  `( read_ne_order s m ->
     read_nf_order s n ->
     read_ne_order s d{{{ m n }}} )
| rne_fst : 
  `( read_ne_order s m ->
     read_ne_order s d{{{ fst m }}} )
| rne_snd :
  `( read_ne_order s m ->
     read_ne_order s d{{{ snd m }}} )
| rne_natrec :
  `( eval_exp_order B d{{{ p ↦ ⇑! ℕ s }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         read_typ_order (S s) b) ->
     eval_exp_order B d{{{ p ↦ zero }}} ->
     (forall bz,
         {{ ⟦ B ⟧ p ↦ zero ↘ bz }} ->
         read_nf_order s d{{{ ⇓ bz mz }}}) ->
     eval_exp_order B d{{{ p ↦ succ (⇑! ℕ s) }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         eval_exp_order MS d{{{ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) }}}) ->
     (forall b bs ms,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ s ↘ b }} ->
         {{ ⟦ B ⟧ p ↦ succ (⇑! ℕ s) ↘ bs }} ->
         {{ ⟦ MS ⟧ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) ↘ ms }} ->
         read_nf_order (S (S s)) d{{{ ⇓ bs ms }}}) ->
     read_ne_order s m ->
     read_ne_order s d{{{ rec m under p return B | zero -> mz | succ -> MS end }}} )
| read_ne_eqrec :
  `( read_typ_order s a ->
     read_nf_order s d{{{ ⇓ a m1 }}} ->
     read_nf_order s d{{{ ⇓ a m2 }}} ->
     eval_exp_order B d{{{ p ↦ ⇑! a s ↦ ⇑! a (S s) ↦ ⇑! (Eq a (⇑! a s) (⇑! a (S s))) (S (S s)) }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↦ ⇑! a (S s) ↦ ⇑! (Eq a (⇑! a s) (⇑! a (S s))) (S (S s)) ↘ b }} ->
         read_typ_order (S (S (S s))) b) ->
     eval_exp_order B d{{{ p ↦ ⇑! a s ↦ ⇑! a s ↦ refl (⇑! a s) }}} ->
     eval_exp_order BR d{{{ p ↦ ⇑! a s }}} ->
     (forall b br,
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↦ ⇑! a s ↦ refl (⇑! a s) ↘ b }} ->
         {{ ⟦ BR ⟧ p ↦ ⇑! a s ↘ br }} ->
         read_nf_order (S s) d{{{ ⇓ b br }}}) ->
     read_ne_order s n ->
     read_ne_order s d{{{ eqrec n under p as Eq a m1 m2 return B | refl -> BR end }}} )

with read_typ_order : nat -> domain -> Prop :=
| rtyp_univ :
  `( read_typ_order s d{{{ 𝕌@i }}} )
| rtyp_nat :
  `( read_typ_order s d{{{ ℕ }}} )
| rtyp_pi :
  `( read_typ_order s a ->
     eval_exp_order B d{{{ p ↦ ⇑! a s }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
         read_typ_order (S s) b) ->
     read_typ_order s d{{{ Π a p B }}})
| rtyp_sigma :
  `( read_typ_order s a ->
     eval_exp_order B d{{{ p ↦ ⇑! a s }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! a s ↘ b }} ->
         read_typ_order (S s) b) ->
     read_typ_order s d{{{ Σ a p B }}})
| rtyp_eq :
  `( read_typ_order s a ->
     read_nf_order s d{{{ ⇓ a m1 }}} ->
     read_nf_order s d{{{ ⇓ a m2 }}} ->
     read_typ_order s d{{{ Eq a m1 m2 }}})
| rtyp_neut :
  `( read_ne_order s b ->
     read_typ_order s d{{{ ⇑ a b }}} ).

#[local]
Hint Constructors read_nf_order read_ne_order read_typ_order : mctt.

Lemma read_nf_order_sound : forall s d m,
    {{ Rnf d in s ↘ m }} ->
    read_nf_order s d
with read_ne_order_sound : forall s d m,
    {{ Rne d in s ↘ m }} ->
    read_ne_order s d
with read_typ_order_sound : forall s d m,
    {{ Rtyp d in s ↘ m }} ->
    read_typ_order s d.
Proof with (econstructor; intros; functional_eval_rewrite_clear; mauto).
  - clear read_nf_order_sound; induction 1...
  - clear read_ne_order_sound; induction 1...
  - clear read_typ_order_sound; induction 1...
Qed.

#[export]
Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound : mctt.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : read_nf_order _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ |- _ => progressive_invert H
  | H : read_typ_order _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations read_nf_impl s d (H : read_nf_order s d) : { m | {{ Rnf d in s ↘ m }} } by struct H :=
| s, d{{{ ⇓ 𝕌@i a }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    exist _ A _
| s, d{{{ ⇓ ℕ zero }}}    , H => exist _ n{{{ zero }}} _
| s, d{{{ ⇓ ℕ (succ m) }}}, H =>
    let (M, HM) := read_nf_impl s d{{{ ⇓ ℕ m }}} _ in
    exist _ n{{{ succ M }}} _
| s, d{{{ ⇓ ℕ (⇑ ^_ m) }}}, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ ⇑ M }}} _
| s, d{{{ ⇓ (Π a p B) m }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (m', Hm') := eval_app_impl m d{{{ ⇑! a s }}} _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a s }}} _ in
    let (M, HM) := read_nf_impl (S s) d{{{ ⇓ b m' }}} _ in
    exist _ n{{{ λ A M }}} _
| s, d{{{ ⇓ (Σ a p B) m }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a s }}} _ in
    let (B', HB) := read_typ_impl (S s) b _ in
    let (m1, Hm1) := eval_fst_impl m _ in
    let (m2, Hm2) := eval_snd_impl m _ in
    let (M, HM) := read_nf_impl s d{{{ ⇓ a m1 }}} _ in
    let (b', Hb') := eval_exp_impl B d{{{ p ↦ m1 }}} _ in
    let (N, HN) := read_nf_impl s d{{{ ⇓ b' m2 }}} _ in
    exist _ n{{{ ⟨ M : A ; N : B' ⟩ }}} _
| s, d{{{ ⇓ (Eq a m1 m2) (refl m') }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (M', HM') := read_nf_impl s d{{{ ⇓ a m' }}} _ in
    exist _ n{{{ refl A M' }}} _
| s, d{{{ ⇓ (Eq a m1 m2) (⇑ b n) }}}, H =>
    let (N, HN) := read_ne_impl s n _ in
    exist _ n{{{ ⇑ N }}} _
| s, d{{{ ⇓ (⇑ a b) (⇑ c m) }}}, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ ⇑ M }}} _

with read_ne_impl s d (H : read_ne_order s d) : { m | {{ Rne d in s ↘ m }} } by struct H :=
| s, d{{{ !x }}}, H => exist _ n{{{ #(s - x - 1) }}} _
| s, d{{{ m n }}}, H =>
    let (M, HM) := read_ne_impl s m _ in
    let (N, HN) := read_nf_impl s n _ in
    exist _ n{{{ M N }}} _
| s, d{{{ fst m }}}, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ fst M }}} _
| s, d{{{ snd m }}}, H =>
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ snd M }}} _
| s, d{{{ rec m under p return B | zero -> mz | succ -> MS end }}}, H =>
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! ℕ s }}} _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    let (bz, Hbz) := eval_exp_impl B d{{{ p ↦ zero }}} _ in
    let (MZ, HMZ) := read_nf_impl s d{{{ ⇓ bz mz }}} _ in
    let (bs, Hbs) := eval_exp_impl B d{{{ p ↦ succ (⇑! ℕ s) }}} _ in
    let (ms, Hms) := eval_exp_impl MS d{{{ p ↦ ⇑! ℕ s ↦ ⇑! b (S s) }}} _ in
    let (MS', HMS') := read_nf_impl (S (S s)) d{{{ ⇓ bs ms }}} _ in
    let (M, HM) := read_ne_impl s m _ in
    exist _ n{{{ rec M return B' | zero -> MZ | succ -> MS' end }}} _
| s, d{{{ eqrec n under p as Eq a m1 m2 return B | refl -> BR end }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (M1, HM1) := read_nf_impl s d{{{ ⇓ a m1 }}} _ in
    let (M2, HM2) := read_nf_impl s d{{{ ⇓ a m2 }}} _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a s ↦ ⇑! a (S s) ↦ ⇑! (Eq a (⇑! a s) (⇑! a (S s))) (S (S s)) }}} _ in
    let (B', HB') := read_typ_impl (S (S (S s))) b _ in
    let (bbr, Hbbr) := eval_exp_impl B d{{{ p ↦ ⇑! a s ↦ ⇑! a s ↦ refl (⇑! a s) }}} _ in
    let (br, Hbr) := eval_exp_impl BR d{{{ p ↦ ⇑! a s }}} _ in
    let (BR', HBR') := read_nf_impl (S s) d{{{ ⇓ bbr br }}} _ in
    let (N, HN) := read_ne_impl s n _ in
    exist _ n{{{ eqrec N as Eq A M1 M2 return B' | refl -> BR' end }}} _

with read_typ_impl s d (H : read_typ_order s d) : { m | {{ Rtyp d in s ↘ m }} } by struct H :=
| s, d{{{ 𝕌@i }}}, H => exist _ n{{{ Type@i }}} _
| s, d{{{ ℕ }}}, H => exist _ n{{{ ℕ }}} _
| s, d{{{ Π a p B }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a s }}} _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    exist _ n{{{ Π A B' }}} _
| s, d{{{ Σ a p B }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a s }}} _ in
    let (B', HB') := read_typ_impl (S s) b _ in
    exist _ n{{{ Σ A B' }}} _
| s, d{{{ Eq a m1 m2 }}}, H =>
    let (A, HA) := read_typ_impl s a _ in
    let (M1, HM1) := read_nf_impl s d{{{ ⇓ a m1 }}} _ in
    let (M2, HM2) := read_nf_impl s d{{{ ⇓ a m2 }}} _ in
    exist _ n{{{ Eq A M1 M2 }}} _
| s, d{{{ ⇑ a b }}}, H =>
    let (B, HB) := read_ne_impl s b _ in
    exist _ n{{{ ⇑ B }}} _.

Extraction Inline read_nf_impl_functional
  read_ne_impl_functional
  read_typ_impl_functional.

(** The definitions of [read_*_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of readback. *)

#[local]
Ltac functional_read_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_read_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma read_nf_impl_complete : forall s d m,
    {{ Rnf d in s ↘ m }} ->
    exists H H', read_nf_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_ne_impl_complete : forall s d m,
    {{ Rne d in s ↘ m }} ->
    exists H H', read_ne_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_typ_impl_complete : forall s d m,
    {{ Rtyp d in s ↘ m }} ->
    exists H H', read_typ_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.
