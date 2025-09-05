From Coq Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.WCong Require Import Definitions Lemmas.
From Mctt.Core.Semantic Require Export NbE WPER.
Import Domain_Notations.

Lemma per_nat_then_per_top : forall {n m},
    {{ Dom n ≈≈ m ∈ per_nat }} ->
    {{ Dom ⇓ ℕ n ≈≈ ⇓ ℕ m ∈ per_top }}.
Proof with solve [destruct_conjs; do 2 eexists; repeat split; mauto 3].
  induction 1; simpl in *; intros s;
    try specialize (IHper_nat s);
    try specialize (H s)...
Qed.

#[export]
Hint Resolve per_nat_then_per_top : mctt.

Lemma wrealize_per_univ_elem_gen : forall {i a a' R},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ a' ∈ per_top_typ }}
    /\ (forall {c c'}, {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈≈ ⇓ a' b' ∈ per_top }}).
Proof with (solve [try (try (do 2 eexists; split); econstructor); mauto]).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - subst.
    eexists.
    per_univ_elem_econstructor; mauto. reflexivity.
  - subst.
    destruct_by_head per_univ.
    specialize (H2 _ _ _ H0).
    destruct_conjs.
    intro s.
    specialize (H1 s). destruct_all...
  - eauto...
  - destruct_all.
    intro s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H9 (S s)).
    specialize (H2 s) as [? []].
    destruct_all...
  - intros c0 c0' equiv_c0_c0'.
    destruct_conjs.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough ({{ Dom c ⇓ a c0 ≈≈ c' ⇓ a' c0' ∈ per_bot }}) by eauto.
    intro s.
    specialize (H3 s).
    specialize (H5 _ _ equiv_c0_c0' s) as [? []].
    destruct_all...
  - destruct_conjs.
    intro s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    match goal with
    | _: {{ $| ^?f0 & ⇑! a s |↘ ^_ }},
        _: {{ $| ^?f0' & ⇑! a' s |↘ ^_ }},
          _: {{ ⟦ B ⟧ ρ ↦ ⇑! a s ↘ ^?b0 }},
            _: {{ ⟦ B' ⟧ ρ' ↦ ⇑! a' s ↘ ^?b0' }} |- _ =>
        rename f0 into f;
        rename f0' into f';
        rename b0 into b;
        rename b0' into b'
    end.
    assert {{ Dom ⇓ b fa ≈≈ ⇓ b' f'a' ∈ per_top }} by eauto.
    specialize (H2 s).
    specialize (H16 (S s)) as [? []].
    destruct_all...
  - intro s.
    (on_all_hyp: fun H => destruct (H s)).
    destruct_all...
  - intro s.
    inversion_clear_by_head per_ne.
    (on_all_hyp: fun H => specialize (H s)).
    destruct_all...
Qed.

Lemma realize_per_univ_elem_gen_sub_rev : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    (forall {a' c c'}, 
         {{ Sub a <: a' at i }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R }})
    /\ (forall {a' d d'}, 
         {{ Sub a' <: a at i }} ->
         {{ Dom d ≈≈ d' ∈ R }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with (solve [try (try (do 2 eexists; split); econstructor); mauto]).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst.
    dependent destruction H3.
    econstructor.
    basic_per_univ_elem_econstructor; eauto. reflexivity.
  - subst. dependent destruction H3.
    destruct_by_head per_univ.
    apply wrealize_per_univ_elem_gen in H3 as IH. destruct_all.
    intro s.
    specialize (H4 s). destruct_all...
  - dependent destruction H0.
    eapply per_nat_then_per_top; mauto 3.
  - admit.
  - admit.
  - intros s. progressive_inversion.
    subst.
    dependent destruction H2. dependent destruction H1.
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all...
Admitted.

Lemma realize_per_univ_elem_gen_sub : forall {i a b R},
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    (forall {a' c c' R'}, 
         {{ Sub a <: a' at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a' c ≈≈ ⇑ b c' ∈ R' }})
    /\ (forall {a' d d' R'}, 
         {{ Sub a' <: a at i }} ->
         {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R' }} ->
         {{ Dom d ≈≈ d' ∈ R' }} -> {{ Dom ⇓ a' d ≈≈ ⇓ b d' ∈ per_top }}).
Proof with (solve [try (try (do 2 eexists; split); econstructor); mauto]).
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem using per_univ_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst.
    dependent destruction H3. subst. subst.
    invert_per_univ_elem H4. rewrite H4.
    eexists.
    basic_per_univ_elem_econstructor; eauto. reflexivity.
  - subst. dependent destruction H3. subst.
    invert_per_univ_elem H4. rewrite H4 in H5.
    destruct_all.
    destruct_by_head per_univ.
    apply wrealize_per_univ_elem_gen in H5. destruct_all.
    intro s.
    specialize (H3 s). destruct_all...
  - progressive_inversion. intros.
    rewrite H. econstructor; auto.
  - dependent destruction H0.
    dependent destruction H1.
    eapply per_nat_then_per_top; mauto.
    rewrite <- H. auto. 
  - dependent destruction H3. 
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_all.
    rewrite H10. intros. 
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel }}. {
      eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
      saturate_refl. auto.
    }
    assert {{ Dom c0 ≈≈ c'0 ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel0) (B:=a); mauto 3.
    }
    destruct_rel_mod_eval. simplify_evals.
    econstructor; mauto 3.
    eapply H29; mauto 3.
    + transitivity a'1. 
      eapply H4; mauto 3.
      eapply per_subtyp_refl; eauto.
    + saturate_refl. auto.
    + assert {{ Dom ⇓ a'0 c0 ≈≈ ⇓ a' c'0 ∈ per_top }}.
      eapply H14; eauto.
      intros s.
      specialize (H8 s).
      specialize (H20 s). destruct_all...
  - dependent destruction H3. 
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_conjs.
    intros s.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H13; mauto 3; saturate_refl; mauto.
    }
    assert {{ Dom ⇑! a0 s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
      eapply H13; mauto 3; saturate_refl; mauto.
    }
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel1 }}. {
      eapply per_elem_subtyping with (R:=in_rel) (A:=a); mauto 3.
      saturate_refl. mauto.
    }
    handle_per_univ_elem_irrel.
    assert {{ Dom ⇑! a s ≈≈ ⇑! a' s ∈ in_rel }}. {
      eapply H18; auto.
    }
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    simplify_evals.
    assert (exists WA WA', {{ Rtyp a0 in s ↘ WA }} /\ {{ Rtyp a' in s ↘ WA' }}). {
      specialize (wrealize_per_univ_elem_gen equiv_a_a'); mauto 3. intros.
      assert (per_univ_elem i in_rel0 a' a') as equiv_a'_a'. {
        etransitivity; [symmetry|]; eassumption.
      }
      specialize (wrealize_per_univ_elem_gen equiv_a'_a'); mauto 3. intros.
      destruct_all.
      specialize (H21 s).
      specialize (H26 s).
      destruct_all...
    }
    destruct_all.
    assert (per_top d{{{ ⇓ a2 fa0 }}} d{{{ ⇓ a'5 f'a' }}}). {
      eapply H36; mauto 3.
      transitivity a'0. eapply per_subtyp_refl; symmetry; mauto 3.
      transitivity a'2; auto.
      eapply H4 with (c:= d{{{ ⇑! a' s }}} ); mauto 3.
      etransitivity; [symmetry|]; mauto 3.
      eapply per_subtyp_refl; mauto 3.
      etransitivity; [|symmetry]; mauto 3.
    }
    specialize (H27 (S s)). destruct_all.
    do 2 eexists; repeat split; econstructor; mauto 3.
  - progressive_inversion.
    rewrite H10. econstructor; auto.
  - intros s. progressive_inversion.
    subst.
    rewrite H10 in H3. dependent destruction H3.
    (on_all_hyp: fun H => specialize (H s)). 
    destruct_all... 
Qed.

Corollary per_univ_then_per_top_typ : forall {i a a' R},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom a ≈≈ a' ∈ per_top_typ }}.
Proof.
  intros * ?%wrealize_per_univ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_univ_then_per_top_typ : mctt.

Corollary per_bot_then_per_elem : forall {i a a' R c c'},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈≈ ⇑ a' c' ∈ R }}.
Proof.
  intros * ?%wrealize_per_univ_elem_gen; firstorder.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)

Corollary per_elem_then_per_top : forall {i a a' R b b'},
    {{ DF a ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom b ≈≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈≈ ⇓ a' b' ∈ per_top }}.
Proof.
  intros * ?%wrealize_per_univ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_elem_then_per_top : mctt.

Lemma per_ctx_then_per_env_initial_env : forall {Γ Γ' env_rel},
    {{ EF Γ ≈≈ Γ' ∈ per_ctx_env ↘ env_rel }} ->
    exists ρ ρ', initial_env Γ ρ /\ initial_env Γ' ρ' /\ {{ Dom ρ ≈≈ ρ' ∈ env_rel }}.
Proof.
  induction 1.
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    eexists.
    eapply per_bot_then_per_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
Qed.

Reserved Notation "⊢snf A ⊆ A'" (in custom judg at level 80, A custom nf, A' custom nf).

Definition not_univ_pi (A : nf) : Prop :=
  match A with
  | nf_typ _ | nf_pi _ _ => False
  | _ => True
  end.

Inductive subtyping_nf : nf -> nf -> Prop :=
| asnf_refl : forall M N,
    not_univ_pi M ->
    {{ ⊢nf M ≈≈ N }} ->
    {{ ⊢snf M ⊆ N }}
| asnf_univ : forall i j,
    i <= j ->
    {{ ⊢snf Type@i ⊆ Type@j }}
| asnf_pi : forall A B A' B',
    {{ ⊢snf A' ⊆ A }} ->
    {{ ⊢snf B ⊆ B' }} ->
    {{ ⊢snf Π A B ⊆ Π A' B' }}
where "⊢snf M ⊆ N" := (subtyping_nf M N) (in custom judg) : type_scope.

(* not sure can we further strengthen this *)
Lemma wrealize_persub_gen : forall {A A' W W' i n},
  {{ Sub A <: A' at i }} ->
  {{ Rtyp A in n ↘ W }} ->
  {{ Rtyp A' in n ↘ W' }} ->
  {{ ⊢snf W ⊆ W' }}.
Proof.
  intros * Hsub Htyp Htyp'.
  gen n W W'. induction Hsub; intros;   
    dir_inversion_by_head read_typ; subst.
  - dependent destruction Htyp.
    dependent destruction Htyp'.
    specialize (H s). destruct_all.
    functional_read_rewrite_clear. econstructor; mauto 3.
    econstructor.
  - eapply asnf_refl; mauto 3.  
    constructor.
  - eapply asnf_univ; eauto.
  - eapply asnf_pi; eauto.
    eapply per_subtyp_to_univ_elem in Hsub as IH.
    destruct_all. handle_per_univ_elem_irrel.
    rename in_rel into R.
    (* we cannot (R d{{{ ⇑! a n }}} d{{{ ⇑! a' n }}}). *)
    assert (R' d{{{ ⇑! a n }}} d{{{ ⇑! a' n }}}) by (eapply realize_per_univ_elem_gen_sub; mauto 3).
    rename b into b'. rename b0 into b.
    rename A0 into WA. rename A into WA'.
    rename B'0 into WB'. rename B'1 into WB.
    eapply H1; mauto 3.
    (* but we do want it *)
    admit.
Admitted.

Lemma var_per_elem : forall {a b i R} n,
    {{ DF a ≈≈ b ∈ per_univ_elem i ↘ R }} ->
    {{ Dom ⇑! a n ≈≈ ⇑! b n ∈ R }}.
Proof.
  intros.
  eapply per_bot_then_per_elem; mauto.
Qed.

(** cannot induction on subtyping. probably need a weaker notion of PER
   that subsumers subtyping. *)
Lemma realize_per_sub_elem_gen : forall {i a a' R},
    {{ Sub a <: a' at i }} ->
    {{ DF a' ≈≈ a' ∈ per_univ_elem i ↘ R }} ->
    (forall {c c'}, {{ Dom c ≈≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈≈ ⇓ a' b' ∈ per_top }}).
Proof.
  intros * Hunivelem. simpl in Hunivelem.
  induction Hunivelem; repeat split; intros;
    apply_relation_equivalence; mauto.
Abort.