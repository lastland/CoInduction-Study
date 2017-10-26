Require Import Coq.Lists.Streams.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.

Section Stream_LE.
  Context { A : Type }.
  Context { Eq Le : relation A }.

  Inductive stream_le_gen `{ PartialOrder A Eq Le} stream_le :
    Stream A -> Stream A -> Prop :=
  | Stream_le : forall h1 h2 t1 t2 ,
      Le h1 h2 ->
      (Eq h1 h2 -> stream_le t1 t2) ->
      stream_le_gen stream_le (Cons h1 t1) (Cons h2 t2).

  CoInductive stream_le `{ PartialOrder A Eq Le } :
    Stream A -> Stream A -> Prop :=
  | Stream_le_fold : forall s1 s2,
      stream_le_gen stream_le s1 s2 -> stream_le s1 s2.
End Stream_LE.

Section Stream_LE_Theorem.
  Variable A : Type.
  Variable Eq Le : relation A.
  Context `{ PartialOrder A Eq Le }.

  Hint Constructors stream_le_gen stream_le.
  
  Ltac inv_stream_le :=
    match goal with
    | [H: stream_le (Cons _ _) (Cons _ _) |- _ ] =>
      inversion H; subst; clear H
    | [H: stream_le_gen _ _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Theorem stream_le_trans : forall (a b c : Stream A),
      stream_le a b ->
      stream_le b c ->
      stream_le a c.
  Proof.
    cofix. constructor.
    destruct a; destruct b; destruct c.
    repeat inv_stream_le. constructor.
    - eapply PreOrder_Transitive; eassumption.
    - intros. rewrite H0 in H5. apply (antisymmetry H4) in H5.
      rewrite H0 in H7. rewrite H5 in H7.
      eapply stream_le_trans; eauto.
      apply H7. apply Equivalence_Reflexive.
  Qed.
End Stream_LE_Theorem.
