From Coq Require Import Morphisms_Relations Relation_Definitions.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import LogicalRelation TermStructureCases UniverseCases FunctionCases.
Import Domain_Notations.

Lemma rel_exp_of_sigma_inversion : forall {Γ M M' A B},
    {{ Γ ⊨ M ≈ M' : Σ A B }} ->
    exists env_rel,
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} /\
        exists i,
        forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        exists fst_rel snd_rel,
          rel_typ i A ρ A ρ' fst_rel /\
            (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ fst_rel }}), rel_typ i B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (snd_rel c c' equiv_c_c')) /\
            rel_exp M ρ M' ρ'
              (fun b b' => rel_mod_proj b b' fst_rel (fun c c' => snd_rel c c') ).
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  do 2 eexists; repeat split; mauto.
Qed.

Lemma rel_exp_of_sigma : forall {Γ env_rel M M' i j A B},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} ->
	(forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists fst_rel snd_rel,
        rel_typ i A ρ A ρ' fst_rel /\
          (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ fst_rel }}), rel_typ j B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (snd_rel c c' equiv_c_c')) /\
          rel_exp M ρ M' ρ'
            (fun b b' => rel_mod_proj b b' fst_rel (fun c c' => snd_rel c c') )) ->
    {{ Γ ⊨ M ≈ M' : Σ A B }}.
Proof.
      intros.
  destruct_conjs.
  eexists_rel_exp_with (max i j).
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_rel).
  match goal with
  | _: rel_typ i A ρ A ρ' ?x |- _ =>
      rename x into in_rel
  end.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  eexists; split; econstructor; mauto.
  - per_univ_elem_econstructor; eauto using per_univ_elem_cumu_max_left.
    + intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; eauto using per_univ_elem_cumu_max_right.
    + apply Equivalence_Reflexive.
  - mauto.
Qed.

Ltac eexists_rel_exp_of_sigma :=
  unshelve eapply (rel_exp_of_sigma _); shelve_unifiable; [eassumption |].

(* This is completely symmetrical to rel_exp_pi_cong, 
   so we import rel_exp_pi_core from FunctionCases *)
Lemma rel_exp_sigma_cong : forall {i Γ A A' B B'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊨ B ≈ B' : Type@i }} ->
    {{ Γ ⊨ Σ A B ≈ Σ A' B' : Type@i }}.
Proof with mautosolve.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1 []%rel_exp_of_typ_inversion1.
  destruct_conjs.
  invert_per_ctx_envs.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head per_univ.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  - intros.
    eapply rel_exp_pi_core; mauto 3.
    reflexivity.
  - solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_sigma_cong : mctt.

(* Again, This is completely symmetrical to rel_exp_pi_sub, 
   so we import rel_exp_pi_core from FunctionCases *)
Lemma rel_exp_sigma_sub : forall {i Γ σ Δ A B},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ, A ⊨ B : Type@i }} ->
    {{ Γ ⊨ (Σ A B)[σ] ≈ Σ (A[σ]) (B[q σ]) : Type@i }}.
Proof with mautosolve.
  intros * [env_relΓ] [env_relΔ]%rel_exp_of_typ_inversion1 []%rel_exp_of_typ_inversion1.
  destruct_conjs.
  pose env_relΔ.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΔ ?x |- _ =>
      rename x into elem_relA
  end.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  assert {{ Dom ρ'σ' ≈ ρ'σ' ∈ env_relΔ }} by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head per_univ.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  - eapply rel_exp_pi_core; eauto; try reflexivity.
    intros.
    extract_output_info_with ρσ c ρ'σ' c' (cons_per_ctx_env env_relΔ elem_relA)...
  - solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_sigma_sub : mctt.

Lemma rel_exp_pari_cong : forall {i Γ A A' B B' M N M' N'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊨ B ≈ B' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ N ≈ N' : B[Id,,M] }} ->
    {{ Γ ⊨ ⟨ M ; N : B ⟩ ≈ ⟨ M' ; N' : B' ⟩ : Σ A B }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_pari_cong : mctt.

Lemma rel_exp_pair_sub : forall {i Γ σ Δ A B M N},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ, A ⊨ B : Type@i }} ->
    {{ Δ ⊨ M : A }} ->
    {{ Δ ⊨ N : B[Id,,M] }} ->
    {{ Γ ⊨ ⟨ M ; N : B ⟩[σ] ≈ ⟨ M[σ] ; N[σ] : B[q σ] ⟩ : (Σ A B)[σ] }}.
Proof.
Admitted.

#[export]
Hint Resolve rel_exp_pair_sub : mctt.

Lemma rel_exp_fst_cong : forall {i Γ A B M M'},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ B : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : Σ A B }} ->
    {{ Γ ⊨ fst M ≈ fst M' : A }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_fst_cong : mctt.

Lemma rel_exp_fst_sub : forall {i Γ σ Δ A B M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ, A ⊨ B : Type@i }} ->
    {{ Δ ⊨ M : Σ A B }} ->
    {{ Γ ⊨ (fst M)[σ] ≈ fst (M[σ]) : A[σ] }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_fst_sub : mctt.

Lemma rel_exp_snd_cong : forall {i Γ A B M M'},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ B : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : Σ A B }} ->
    {{ Γ ⊨ snd M ≈ snd M' : B[Id,,fst M] }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_snd_cong : mctt.

Lemma rel_exp_snd_sub : forall {i Γ σ Δ A B M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ, A ⊨ B : Type@i }} ->
    {{ Δ ⊨ M : Σ A B }} ->
    {{ Γ ⊨ (snd M)[σ] ≈ snd (M[σ]) : B[σ,,fst (M[σ])] }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_snd_sub : mctt.

Lemma rel_exp_fst_beta : forall {i Γ A B M N},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ B : Type@i }} ->
    {{ Γ ⊨ M : A }} ->
    {{ Γ ⊨ N : B[Id,,M] }} ->
    {{ Γ ⊨ fst (⟨ M ; N : B⟩) ≈ M : A }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_fst_beta : mctt.

Lemma rel_exp_snd_beta : forall {i Γ A B M N},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ B : Type@i }} ->
    {{ Γ ⊨ M : A }} ->
    {{ Γ ⊨ N : B[Id,,M] }} ->
    {{ Γ ⊨ snd ⟨ M ; N : B ⟩ ≈ N : B[Id,,M] }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_snd_beta : mctt.

Lemma rel_exp_pair_eta : forall {i Γ A B M},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ B : Type@i }} ->
    {{ Γ ⊨ M : Σ A B }} ->
    {{ Γ ⊨ M ≈ ⟨ fst M ; snd M : B ⟩ : Σ A B }}.
Proof with mautosolve.
Admitted.

#[export]
Hint Resolve rel_exp_pair_eta : mctt.