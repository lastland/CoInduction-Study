Require Import Coq.Lists.Streams.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.

Section Stream_LE.
  Context { A : Type }.
  Context { Eq Le : relation A }.

  CoInductive stream_le `{ PartialOrder A Eq Le} :
    Stream A -> Stream A -> Prop :=
  | Stream_le : forall h1 h2 t1 t2,
      Le h1 h2 ->
      (Eq h1 h2 -> stream_le t1 t2) ->
      stream_le (Cons h1 t1) (Cons h2 t2).
End Stream_LE.

Section Stream_LE_Theorem.
  Variable A : Type.
  Variable Eq Le : relation A.
  Context `{ PartialOrder A Eq Le }.
  
  Ltac inv_stream_le :=
    match goal with
    | [H: stream_le _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Theorem stream_le_trans : forall (a b c : Stream A),
      stream_le a b ->
      stream_le b c ->
      stream_le a c.
  Proof.
    cofix. destruct a; destruct b; destruct c. intros.
    constructor; repeat inv_stream_le.
    - eapply PreOrder_Transitive; eassumption.
    - intros. rewrite H0 in H4. apply (antisymmetry H4) in H5.
      rewrite H0 in H8. rewrite H5 in H7.
      eapply stream_le_trans; eauto.
      apply H7. apply Equivalence_Reflexive.
  Qed.
End Stream_LE_Theorem.
