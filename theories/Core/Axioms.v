Require Export Coq.Logic.PropExtensionality.
Require Export Coq.Logic.IndefiniteDescription.
Require Export Coq.Logic.FunctionalExtensionality.


Lemma dep_functional_choice :
  forall (A : Type) (B : A -> Type) (R: forall a, B a -> Prop),
    (forall x : A, exists y : B x, R x y) ->
    (exists f : forall x, B x, forall x : A, R x (f x)).
Proof.
  intros.
  exists (fun x => proj1_sig (constructive_indefinite_description (R x) (H x))).
  intro x.
  apply (proj2_sig (constructive_indefinite_description (R x) (H x))).
Qed.

Lemma dep_functional_choice_equiv :
  forall (A : Type) (B : A -> Type) (R: forall a, B a -> Prop),
    (forall x : A, exists y : B x, R x y) <->
    (exists f : forall x, B x, forall x : A, R x (f x)).
Proof.
  intros; split.
  - apply dep_functional_choice.
  - firstorder.
Qed.

Lemma functional_choice_equiv :
  forall (A B : Type) (R:A->B->Prop),
    (forall x : A, exists y : B, R x y) <->
    (exists f : A->B, forall x : A, R x (f x)).
Proof.
  intros; split.
  - apply functional_choice.
  - firstorder.
Qed.

Lemma exists_absorption :
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (exists x : A, P x) /\ Q <-> (exists x : A, P x /\ Q).
Proof.
  firstorder.
Qed.