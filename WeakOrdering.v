
From Coq Require Import Classical.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Classes.RelationClasses.


(* Not found in Coq's standard library *)

Definition Involutive {T} (f : T->T) :=
  forall x, f (f x) = x.


(* Some formalization for https://en.wikipedia.org/wiki/Weak_ordering#Strict_weak_orderings *)

Context {A : Type}.

Class StrongConnected (R : relation A) :=
  strong_connectedness : forall x y : A, R x y \/ R y x.

Class TotalPreorder (R : relation A) : Prop := {
  TotalPreOrder_Transitive :: Transitive R;
  TotalPreOrder_StrongConnected :: StrongConnected R
}.

Lemma total_preorder_is_reflexive (R: relation A) :
  TotalPreorder R -> Reflexive R.
Proof.
  intro.
  intro.
  destruct H.
  specialize (TotalPreOrder_StrongConnected0 x x).
  elim TotalPreOrder_StrongConnected0.
  tauto.
  tauto.
Qed.

Lemma relation_complement_involutive :
  Involutive (@complement A).
Proof.
  intro.
  unfold complement.
  apply functional_extensionality.
  intro.
  apply functional_extensionality.
  intro.
  apply propositional_extensionality.
  split.
  - intro.
    destruct (classic (x x0 x1)).
    trivial.
    apply H in H0.
    inversion H0.
  - intros.
    apply H0 in H.
    trivial.
Qed.

Definition comparable (P: relation A) (x y: A) :=
  P x y \/ P y x.

Definition incomparable (P: relation A) (x y: A) :=
  ~ comparable P x y.

Class TransitiveIncomparability (P : relation A) :=
  transitive_incomparability : forall x y z: A,
  ((incomparable P x y /\ incomparable P y z) -> incomparable P x z).

Class StrictWeakOrdering (P : relation A) : Prop := {
  StrictWeakOrdering_Irreflexive :: Irreflexive P ;
  StrictWeakOrdering_Transitive :: Transitive P ;
  StrictWeakOrdering_TransitiveIncomparability :: TransitiveIncomparability P
}.

Lemma strict_weak_ordering_iff_complement_total_preorder (P: relation A) :
  StrictWeakOrdering P <-> TotalPreorder (complement P).
Proof.
  split.
  - intro.
    destruct H.
    unfold complement.
    split.
    unfold Transitive.
    intros.
    unfold Transitive in StrictWeakOrdering_Transitive0.
    pose proof (StrictWeakOrdering_Transitive0 x z y).
    pose proof (StrictWeakOrdering_Transitive0 y x z).
    unfold TransitiveIncomparability in StrictWeakOrdering_TransitiveIncomparability0.
    pose proof (StrictWeakOrdering_TransitiveIncomparability0 z y x).
    (*specialize (H2 H1).*)
    unshelve epose proof (H2 _) as H5.
    trivial.
    assert (P y x -> P y z).
    intro.
    apply H3 in H6.
    auto.
    auto.
    assert (P z y -> False).
    intro.
    apply H5 in H7.
    apply H in H7.
    auto.
    assert (P y x -> False).
    intro.
    apply H6 in H8.
    apply H0 in H8.
    auto.
    assert (incomparable P z y).
    unfold incomparable.
    intro.
    destruct H9.
    apply H7 in H9.
    auto.
    apply H0 in H9.
    auto.
    assert (incomparable P y x).
    unfold incomparable.
    intro.
    destruct H10.
    apply H8 in H10.
    auto.
    apply H in H10.
    auto.
    assert (incomparable P z y /\ incomparable P y x).
    split.
    auto.
    auto.
    apply H4 in H11.
    destruct H11.
    unfold comparable.
    right.
    auto.
    intro.
    intro.
    assert (P x y /\ P y x -> False).
    intro.
    destruct H.
    pose proof (StrictWeakOrdering_Transitive0 x y x).
    unshelve epose proof (H1 _).
    auto.
    unshelve epose proof (H2 _).
    auto.
    pose proof (StrictWeakOrdering_Irreflexive0 x).
    destruct H4.
    tauto.
    tauto.
  - intro.
    split.
    apply total_preorder_is_reflexive in H.
    unfold Irreflexive.
    tauto.
    unfold Transitive.
    intros.
    destruct H.
    pose proof (TotalPreOrder_StrongConnected0 x y).
    elim H.
    intro.
    apply H2 in H0.
    tauto.
    intro.
    pose proof (TotalPreOrder_StrongConnected0 y z).
    elim H3.
    intro.
    apply H4 in H1.
    tauto.
    intro.
    pose proof (TotalPreOrder_Transitive0 z y x).
    unshelve epose proof (H5 _) as H6.
    tauto.
    unshelve epose proof (H6 _) as H7.
    tauto.
    assert (complement P x z -> False).
    intro.
    pose proof (TotalPreOrder_Transitive0 y x z).
    unshelve epose proof (H9 _).
    tauto.
    unshelve epose proof (H10 _).
    tauto.
    apply H11 in H1.
    tauto.
    unfold complement in H8.
    tauto.
    intro.
    intros.
    destruct H.
    unfold incomparable in H0.
    unfold comparable in H0.
    intro.
    unfold comparable in H.
    pose proof (TotalPreOrder_Transitive0 x y z).
    unfold complement in H1.
    pose proof (TotalPreOrder_Transitive0 z y x).
    unfold complement in H2.
    tauto.
Qed.

Corollary total_preorder_iff_complement_strict_weak_ordering (R: relation A) :
  TotalPreorder R <-> StrictWeakOrdering (complement R).
Proof.
  assert (TotalPreorder (complement (complement R)) <-> TotalPreorder R).
  assert (Involutive (@complement A)).
  apply relation_complement_involutive.
  assert (complement (complement R) = R).
  apply H.
  assert (TotalPreorder(complement (complement R)) = TotalPreorder R).
  f_equal.
  tauto.
  rewrite H1.
  tauto.
  apply propositional_extensionality in H.
  rewrite <- H.
  pose proof (strict_weak_ordering_iff_complement_total_preorder (complement R)).
  tauto.
Qed.

Definition preference_relation (R: relation A) :=
  TotalPreorder R.


(*
A characterization of preference relations used by Allan Gibbard in
https://www.eecs.harvard.edu/cs286r/courses/fall11/papers/Gibbard73.pdf
*)

Definition ordering (P: relation A) :=
  StrictWeakOrdering P.

Definition indifferent (P: relation A) (x y: A) :=
  incomparable P x y.

Definition no_2_cycle (P: relation A) :=
  forall x y, ~(P x y /\ P y x).

Lemma orering_without_2_cycle (P: relation A) :
  ordering P -> no_2_cycle P.
Proof.
  intro.
  destruct H.
  intro.
  intro.
  intro.
  pose proof (StrictWeakOrdering_Transitive0 x y x).
  destruct H.
  unshelve epose proof (H0 _) as H2.
  tauto.
  unshelve epose proof (H2 _) as H3.
  tauto.
  unfold Irreflexive in StrictWeakOrdering_Irreflexive0.
  unfold complement in StrictWeakOrdering_Irreflexive0.
  unfold Reflexive in StrictWeakOrdering_Irreflexive0.
  pose proof (StrictWeakOrdering_Irreflexive0 x).
  tauto.
Qed.

Lemma no_2_cycle_imlies_irreflexive (P: relation A) :
  no_2_cycle P -> Irreflexive P.
Proof.
  intro.
  intro.
  intro.
  unfold no_2_cycle in H.
  pose proof (H x x).
  tauto.
Qed.

Lemma characterization_ordering (P: relation A) :
  ordering P <-> (
    no_2_cycle P /\
    forall x y z, P x z -> (P x y \/ P y z)
  ).
Proof.
  split.
  - intro.
    split.
    apply orering_without_2_cycle.
    tauto.
    intros.
    destruct H.
    unfold TransitiveIncomparability in StrictWeakOrdering_TransitiveIncomparability0.
    pose proof (StrictWeakOrdering_TransitiveIncomparability0 x y z).
    unfold incomparable in H.
    unfold comparable in H.
    unfold Transitive in StrictWeakOrdering_Transitive0.
    pose proof (StrictWeakOrdering_Transitive0 y x z).
    pose proof (StrictWeakOrdering_Transitive0 x z y).
    tauto.
  - intros.
    destruct H. 
    split.
    intro.
    intro.
    unfold no_2_cycle in H.
    pose proof (H x x).
    tauto.
    intro.
    intros.
    unfold no_2_cycle in H.
    pose proof (H x y).
    pose proof (H y z).
    pose proof (H0 z y x).
    pose proof (H0 x z y).
    tauto.
    intro.
    intros.
    unfold incomparable in H1.
    unfold comparable in H1.
    intro.
    unfold comparable in H2.
    pose proof (H x y).
    pose proof (H y z).
    pose proof (H0 x y z).
    pose proof (H0 z y x).
    tauto.
Qed.
