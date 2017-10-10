Require Import Coq.Lists.Streams.

Class Le (A: Type) :=
  {
    le : A -> A -> Prop;
    le_trans : forall a b c, le a b -> le b c -> le a c;
    le_asm : forall a b, le a b -> le b a -> a = b
  }.

Section Stream_LE.
  Variable A : Type.
  Context `{Le A}.
  
  CoInductive stream_le : Stream A -> Stream A -> Prop :=
  | Stream_le : forall h1 h2 t1 t2,
      le h1 h2 ->
      (h1 = h2 -> stream_le t1 t2) ->
      stream_le (Cons h1 t1) (Cons h2 t2).
End Stream_LE.

Arguments stream_le {_} {_}.

Section Stream_LE_Thoerems.
  Variable A : Type.
  Context `{Le A}.

  Ltac destruct_stream_le :=
    match goal with
    | [H: stream_le ?a ?b |- _ ] =>
      destruct a; destruct b; inversion H; subst
    end.

  Lemma hd_le : forall s1 s2, stream_le s1 s2 -> le (hd s1) (hd s2).
  Proof.
    intros. destruct_stream_le.
    simpl; assumption.
  Qed.
  
  Lemma tl_le : forall s1 s2, stream_le s1 s2 ->
                         (hd s1) = (hd s2) ->
                         stream_le (tl s1) (tl s2).
  Proof.
    intros. destruct_stream_le.
    simpl in *; auto.
  Qed.

  Hint Resolve eq_refl.

  Theorem stream_le_trans: forall (a b c : Stream A),
      stream_le a b ->
      stream_le b c ->
      stream_le a c.
  Proof.
    cofix. destruct a; destruct b; destruct c. intros.
    constructor.
    - apply hd_le in H0. apply hd_le in H1. simpl in *.
      eapply le_trans; eassumption.
    - intros; subst. assert (a1 = a2).
      { inversion H0; subst; inversion H1; subst.
        apply (le_asm _ _ H6) in H5; assumption. }
      subst. apply tl_le in H0; apply tl_le in H1; simpl in *; auto.
      + eapply stream_le_trans; eassumption.
  Qed.
End Stream_LE_Thoerems.  
