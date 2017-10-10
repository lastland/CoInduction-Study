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

Ltac inv_stream_le :=
  match goal with
  | [H: stream_le _ _ |- _ ] =>
    inversion H; subst; clear H
  end.

Theorem stream_le_trans {A} `{Le A}: forall (a b c : Stream A),
    stream_le a b ->
    stream_le b c ->
    stream_le a c.
Proof.
  cofix. destruct a; destruct b; destruct c. intros.
  constructor; repeat inv_stream_le.
  - eapply le_trans; eassumption. 
  - intros; subst. apply (le_asm _ _ H4) in H5; subst.
    eapply stream_le_trans; eauto.
Qed.
