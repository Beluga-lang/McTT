From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions Lemmas.
Import Syntax_Notations.

#[global]
Ltac pi_univ_level_tac :=
  match goal with
  | |- {{ ^_ ;; ^_ ⊢s ^_ : ^_ }} => mauto 4
  | H : {{ ^?Δ ;; ^?Γ ⊢ ^?A : Type@?j }} |- {{ ^?Δ ;; ^?Γ , ^?A ⊢ ^?B : Type@?i }} =>
      eapply lift_exp_max_right; mauto 4
  | |- {{ ^?Δ ;; ^?Γ ⊢ ^?A : Type@?j }} =>
      eapply lift_exp_max_left; mauto 4
  end.

#[export]
Hint Rewrite -> wf_exp_eq_pi_sub wf_exp_eq_sigma_sub using pi_univ_level_tac : mctt.

#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | {{ ^?Δ ⊢ ^?Γ, ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HAi := fresh "HAi" in
      pose proof ctx_decomp H as [HΓ HAi];
      match goal with
      | _: {{ Δ ;; Γ ⊢ A : Type@_ }} |- _ => clear HAi
      | _: __mark__ _ {{ Δ ;; Γ ⊢ A : Type@_ }} |- _ => clear HAi
      | _ =>
          let i := fresh "i" in
          let HA := fresh "HA" in
          destruct HAi as [i HA]
      end
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.

Ltac gen_core_presup H :=
  match type of H with
  | {{ ^_ ⊢ ^?Γ ≈ ^?Γ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      pose proof presup_ctx_eq H as [HΓ HΓ']
  | {{ ^_ ⊢ ^?Γ ⊆ ^?Γ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      pose proof presup_ctx_sub H as [HΓ HΓ']
  | {{ ^?Δ ;; ^?Γ ⊢ ^?M : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HAi := fresh "HAi" in
      pose proof presup_exp H as [HΓ HAi];
      match goal with
      | _: {{ Δ ;; Γ ⊢ A : Type@_ }} |- _ => clear HAi
      | _: __mark__ _ {{ Δ ;; Γ ⊢ A : Type@_ }} |- _ => clear HAi
      | _ =>
          let i := fresh "i" in
          let HA := fresh "HA" in
          destruct HAi as [i HA]
      end
  | {{ ^?Δ ;; ^?Γ ⊢s ^?σ : ^?Γ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      pose proof presup_sub H as [HΓ HΓ']
  end.

Ltac gen_lookup_presup H :=
  match type of H with
  | {{ #?x : ^?A ∈ ^?Γ }} =>
      match goal with
      | _: {{ Δ ;; ^?Γ ⊢ A : Type@_ }} |- _ => fail
      | _: __mark__ _ {{ Δ ;; ^?Γ ⊢ A : Type@_ }} |- _ => fail
      | _ =>
          let i := fresh "i" in
          let HA := fresh "HA" in
          pose proof presup_ctx_lookup_typ ltac:(eassumption) H as [i HA]
      end
  end.

Ltac gen_core_presups := (on_all_hyp: fun H => gen_core_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
