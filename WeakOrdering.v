
From Coq Require Import Classical.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Program.Basics.


(*
  Some formalization for
  https://en.wikipedia.org/wiki/Weak_ordering#Strict_weak_orderings
*)


(* Not found in Coq's standard library *)

Definition Involutive {T} (f : T->T) :=
  forall x, f (f x) = x.

(* flip just flips the arguments of a relation *)
Lemma flip_rewrite {A B C} (f : A -> B -> C) x y :
  (flip f) x y = f y x.
Proof.
  reflexivity.
Qed.

(* Lemma flip_involutive {A B : Type} :
  Involutive (@flip A A B).
Proof.
  unfold Involutive. reflexivity.
Qed. *)

Context {A : Type}.
(* Variable A : Type. *)

Lemma complement_involutive :
  Involutive (@complement A).
Proof.
  intro.
  unfold complement.
  apply functional_extensionality.
  intro.
  apply functional_extensionality.
  intro.
  apply propositional_extensionality.
  tauto.
Qed.


(* Non-strict orders *)

Class StrongConnected (R : relation A) :=
  strong_connected : forall x y : A, R x y \/ R y x.

(* flip just flips the arguments of a relation *)
Lemma flip_StrongConnected (R : relation A) :
  StrongConnected R <-> StrongConnected (flip R).
Proof.
  split.
    - intro. unfold StrongConnected. intros x y. destruct H with (x:=x) (y:=y).
      * right. unfold flip. apply H0.
      * left. unfold flip. apply H0.
    - intro. unfold StrongConnected. intros x y. destruct H with (x:=x) (y:=y).
      * right. unfold flip. apply H0.
      * left. unfold flip. apply H0.
Qed.

Class TotalPreorder (R : relation A) : Prop := {
  TotalPreOrder_Transitive : Transitive R;
  TotalPreOrder_StrongConnected : StrongConnected R
}.

Lemma total_preorder_is_reflexive (R: relation A) :
  TotalPreorder R -> Reflexive R.
Proof.
  intro.
  intro.
  destruct H eqn:TP.
  specialize (TotalPreOrder_StrongConnected x x).
  tauto.
Qed.

Definition comparable (R: relation A) (x y: A) :=
  R x y \/ R y x.

Definition incomparable (R: relation A) (x y: A) :=
  ~ comparable R x y.

Definition preference_relation (R: relation A) :=
  TotalPreorder R.

Lemma filp_TotalPreorder (R: relation A) :
  TotalPreorder R <-> TotalPreorder (flip R).
Proof.
  split.
  - intro. destruct H. split.
    * apply flip_Transitive. apply TotalPreOrder_Transitive0.
    * apply flip_StrongConnected. apply TotalPreOrder_StrongConnected0.
  - intro. destruct H. split.
    * apply flip_Transitive. apply TotalPreOrder_Transitive0.
    * apply flip_StrongConnected. apply TotalPreOrder_StrongConnected0.
Qed.

(* Strict orders *)

Class TransitiveIncomparability (P : relation A) :=
  transitive_incomparability : forall x y z: A,
  ((incomparable P x y /\ incomparable P y z) -> incomparable P x z).

Lemma flip_TransitiveIncomparability (P: relation A) :
  TransitiveIncomparability P <-> TransitiveIncomparability (flip P).
Proof.
  unfold TransitiveIncomparability. unfold incomparable. unfold comparable.
  repeat rewrite flip_rewrite. split.
  - intro. intros x y z. intro.
    apply H with (x:=z) (y:=y) (z:=x). tauto.
  - intro. intros x y z. intro.
    apply H with (x:=z) (y:=y) (z:=x). tauto.
Qed.

Class StrictWeakOrdering (P : relation A) : Prop := {
  StrictWeakOrdering_Irreflexive :: Irreflexive P ;
  StrictWeakOrdering_Transitive :: Transitive P ;
  StrictWeakOrdering_TransitiveIncomparability :: TransitiveIncomparability P
}.

Lemma flip_StrictWeakOrdering (P: relation A) :
  StrictWeakOrdering P <-> StrictWeakOrdering (flip P).
Proof.
  split.
  - intro. destruct H. split.
    * apply flip_Irreflexive. apply StrictWeakOrdering_Irreflexive0.
    * apply flip_Transitive. apply StrictWeakOrdering_Transitive0.
    * apply flip_TransitiveIncomparability. apply StrictWeakOrdering_TransitiveIncomparability0.
  - intro. destruct H. split.
    * apply flip_Irreflexive. apply StrictWeakOrdering_Irreflexive0.
    * apply flip_Transitive. apply StrictWeakOrdering_Transitive0.
    * apply flip_TransitiveIncomparability. apply StrictWeakOrdering_TransitiveIncomparability0.
Qed.

(* Relationship between strict and non-strict orders *)

Lemma StrictWeakOrdering_iff_complement_TotalPreorder (P: relation A) :
  StrictWeakOrdering P <-> TotalPreorder (complement P).
Proof.
  split.
  {
    intro.
    destruct H eqn:SO.
    unfold complement.
    split.
    {
      unfold Transitive.
      intros.
      unfold Transitive in StrictWeakOrdering_Transitive0.
      pose proof (StrictWeakOrdering_Transitive0 x z y).
      pose proof (StrictWeakOrdering_Transitive0 y x z).
      unfold TransitiveIncomparability in StrictWeakOrdering_TransitiveIncomparability0.
      pose proof (StrictWeakOrdering_TransitiveIncomparability0 z y x).
      specialize (H3 H2).
      (*unshelve epose proof (H3 _) as H6.*)
      trivial.
      assert (P y x -> P y z).
      {
        intro.
        apply H4 in H6.
        auto.
        auto.
      }
      {
        assert (P z y -> False).
        {
          intro.
          apply H3 in H7.
          apply H0 in H7.
          auto.
        }
        {
          assert (P y x -> False).
          {
            intro.
            apply H6 in H8.
            apply H1 in H8.
            auto.
          }
          {
            assert (incomparable P z y).
            {
              unfold incomparable.
              intro.
              unfold comparable in H9.
              destruct H9.
              {
                tauto.
              }
              {
                apply H1 in H9.
                auto.
              }
            }
            {
              assert (incomparable P y x).
              {
                unfold incomparable.
                intro.
                unfold comparable in H10.
                destruct H10.
                {
                  apply H8 in H10.
                  auto.
                }
                {
                  apply H0 in H10.
                  auto.
                }
              }
              {
                assert (incomparable P z y /\ incomparable P y x).
                {
                  split.
                  {
                    auto.
                  }
                  {
                    auto.
                  }
                }
                {
                  apply H5 in H11.
                  destruct H11.
                  right.
                  auto.
                }
              }
            }
          }
        }
      }
    }
    {
      intro.
      intro.
      assert (P x y /\ P y x -> False).
      {
        intro.
        destruct H.
        pose proof (StrictWeakOrdering_Transitive0 x y x).
        destruct H0.
        unshelve epose proof (H _).
        {
          auto.
        }
        {
          unshelve epose proof (H2 _).
          {
            auto.
          }
          {
            pose proof (StrictWeakOrdering_Irreflexive0 x).
            destruct H4.
            tauto.
          }
        }
      }
      {
        tauto.
      }
    }
  }
  {
    intro.
    split.
    {
      apply total_preorder_is_reflexive in H.
      unfold Irreflexive.
      tauto.
    }
    {
      unfold Transitive.
      intros.
      destruct H.
      pose proof (TotalPreOrder_StrongConnected0 x y).
      elim H.
      {
        intro.
        apply H2 in H0.
        tauto.
      }
      {
        intro.
        pose proof (TotalPreOrder_StrongConnected0 y z).
        elim H3.
        {
          intro.
          apply H4 in H1.
          tauto.
        }
        {
          intro.
          pose proof (TotalPreOrder_Transitive0 z y x).
          unshelve epose proof (H5 _) as H6.
          {
            tauto.
          }
          {
            unshelve epose proof (H6 _) as H7.
            {
              tauto.
            }
            {
              assert (complement P x z -> False).
              {
                intro.
                pose proof (TotalPreOrder_Transitive0 y x z).
                unshelve epose proof (H9 _).
                {
                  tauto.
                }
                {
                  unshelve epose proof (H10 _).
                  {
                    tauto.
                  }
                  {
                    apply H11 in H1.
                    tauto.
                  }
                }
              }
              {
                unfold complement in H8.
                tauto.
              }
            }
          }
        }
      }
    }
    {
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
    }
  }
Qed.

Corollary TotalPreorder_iff_complement_StrictWeakOrdering (R: relation A) :
  TotalPreorder R <-> StrictWeakOrdering (complement R).
Proof.
  assert (TotalPreorder (complement (complement R)) <-> TotalPreorder R).
  - assert (Involutive (@complement A)).
    + apply complement_involutive.
    + assert (complement (complement R) = R).
      * apply H.
      * assert (TotalPreorder(complement (complement R)) = TotalPreorder R).
        f_equal.
        tauto.
        rewrite H1.
        tauto.
  - apply propositional_extensionality in H.
    rewrite <- H.
    pose proof (StrictWeakOrdering_iff_complement_TotalPreorder (complement R)).
    tauto.
Qed.

Definition switch_strictness (R : relation A) : relation A :=
  complement (flip R).

Lemma switch_strictness_fundamental_property (R : relation A) (a b : A) :
  switch_strictness R a b = ~ R b a.
Proof.
  unfold switch_strictness. unfold complement. unfold flip. reflexivity.
Qed.

Lemma switch_strictness_involutive (R : relation A) :
  Involutive switch_strictness.
Proof.
  unfold switch_strictness. unfold Involutive. intro. apply functional_extensionality.
  intro. unfold flip. unfold complement. simpl. apply functional_extensionality.
  intro. assert (Decidable.decidable (x x0 x1)).
  { apply classic. }
  apply propositional_extensionality. rewrite Decidable.not_not_iff.
  reflexivity. apply H.
Qed.

Lemma strict_implies_non_strict (R: relation A) (a b: A) :
  TotalPreorder R -> (switch_strictness R) a b -> R a b.
Proof.
  intro. unfold switch_strictness. unfold complement. unfold flip.
  destruct H. assert (R a b \/ R b a).
  { apply TotalPreOrder_StrongConnected0. }
  destruct H.
  - tauto.
  - tauto.
Qed.

Lemma StrictWeakOrdering_iff_switch_strictness_TotalPreorder (P: relation A) :
  StrictWeakOrdering P <-> TotalPreorder (switch_strictness P).
Proof.
  rewrite StrictWeakOrdering_iff_complement_TotalPreorder. unfold switch_strictness.
  rewrite complement_inverse. rewrite filp_TotalPreorder. tauto.
Qed.

Lemma TotalPreorder_iff_switch_strictness_StrictWeakOrdering (R: relation A) :
  TotalPreorder R <-> StrictWeakOrdering (switch_strictness R).
Proof.
  rewrite TotalPreorder_iff_complement_StrictWeakOrdering. unfold switch_strictness.
  rewrite flip_StrictWeakOrdering. tauto.
Qed.


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
  - tauto.
  - unshelve epose proof (H2 _) as H3.
    + tauto.
    + unfold Irreflexive in StrictWeakOrdering_Irreflexive0.
      unfold complement in StrictWeakOrdering_Irreflexive0.
      unfold Reflexive in StrictWeakOrdering_Irreflexive0.
      pose proof (StrictWeakOrdering_Irreflexive0 x).
      tauto.
Qed.

Lemma no_2_cycle_implies_irreflexive (P: relation A) :
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
    + apply orering_without_2_cycle.
      tauto.
      + intros.
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
    + intro.
      intro.
      unfold no_2_cycle in H.
      pose proof (H x x).
      tauto.
    + intro.
      intros.
      unfold no_2_cycle in H.
      pose proof (H x y).
      pose proof (H y z).
      pose proof (H0 z y x).
      pose proof (H0 x z y).
      tauto.
    + intro.
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
