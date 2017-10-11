Require Import Coq.Lists.Streams.

Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILInsts.

Set Implicit Arguments.

Section TraceProp.
  Variable T : Type.
  
  Definition TraceProp : Type := Stream T -> Prop.

  Global Instance ILogicOps_TraceProp :
    ILogicOps TraceProp := @ILInsts.ILFun_Ops _ _ _.

  Global Instance ILogic_TraceProp : ILogic TraceProp := _.

End TraceProp.

Section LTL.
  Variable T : Type.
  Variables P Q : TraceProp T.
  
  Inductive _until : TraceProp T -> TraceProp T -> Stream T -> Prop :=
  | ReachUntil: forall (P Q : TraceProp T) s, Q s -> _until P Q s
  | PreservingUntil: forall (P Q : TraceProp T) e s,
      _until P Q s ->
      P (Cons e s) ->
      _until P Q (Cons e s).

  CoInductive _always : TraceProp T -> Stream T -> Prop :=
  | PreservingAlways: forall (P : TraceProp T) e s,
      _always P s ->
      P (Cons e s) ->
      _always P (Cons e s).

  Inductive _eventually : TraceProp T -> Stream T -> Prop :=
  | ReachEventually : forall (P : TraceProp T) s,
      P s -> _eventually P s
  | PreservingEventually : forall (P : TraceProp T) e s,
      _eventually P s -> _eventually P (Cons e s).

  Definition Next : TraceProp T :=
    fun s => match s with
          | Cons h t => P t
          end.

  Definition Until : TraceProp T :=
    fun s => _until P Q s.

  Definition Always : TraceProp T :=
    fun s => _always P s.

  Definition Eventually : TraceProp T :=
    fun s => _eventually P s.
End LTL.

Arguments Next {_}.
Arguments Until {_}.
Arguments Always {_}.
Arguments Eventually {_}.

Local Transparent ILInsts.ILFun_Ops.

Section LTL_Theorems.
  Variable T : Type.
  Variables P Q : TraceProp T.
  Variable s: Stream T.

  Theorem Not_Next :
    (Next P -->> lfalse) s <-> (Next (P -->> lfalse)) s.
  Proof.
    destruct s; simpl; reflexivity.
  Qed.

  Theorem Next_dist :
    (Next (P -->> Q)) s <-> (Next P -->> Next Q) s.
  Proof.
    destruct s; simpl; reflexivity.
  Qed.

  Theorem Always_dist :
    (Always (P -->> Q)) s -> (Always P -->> Always Q) s.
  Proof.
    generalize dependent s; cofix;
      destruct s0; simpl; intros.
    inversion H; subst; inversion H0; subst.
    constructor; try apply Always_dist; auto.
  Qed.

  Theorem Always_Next :
    (Always (P -->> Next P)) s -> (P -->> Always P) s.
  Proof.
    simpl; generalize dependent s; cofix;
      destruct s0; simpl; intros.
    unfold Next in H; inversion H; subst.
    constructor; try apply Always_Next; auto.
  Qed.

  Theorem Always_and_P :
    (Always P) s -> (P //\\ Always P) s.
  Proof.
    simpl; intros; split; auto.
    inversion H; auto.
  Qed.

  Theorem Until_Eventually :
    (Until P Q) s -> (Eventually Q) s.
  Proof.
    induction 1;
      (left + right); solve [auto].
  Qed.

  Theorem Always_Until :
    (Until P Q) s <-> (Q \\// (P //\\ (Next (Until P Q)))) s.
  Proof.
    simpl; split; intros.
    - inversion H; subst;
        (left + right); solve [auto].
    - destruct H; destruct s; try unfold Next in H;
        (left + right); solve [intuition].
  Qed.
      
  Theorem Always_and :
    (Always P //\\ Always Q) s <-> Always (P //\\ Q) s.
  Proof.
    split; simpl.
    - generalize dependent s. cofix.
      intros; destruct s. destruct H as [HP HQ].
      inversion HP; subst; inversion HQ; subst.
      red. constructor; try apply Always_and; intuition.
    - split; generalize dependent s; cofix;
        solve [intros; destruct s; inversion H; subst; constructor;
               solve [apply Always_and; assumption | intuition ] ].
  Qed.
End LTL_Theorems.
