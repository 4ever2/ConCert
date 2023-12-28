From ConCert.Execution Require Import ChainedList.

Section Reachable.
  Context {Point : Type} {Link : Point -> Point -> Type}.
  Context {empty_point : Point}.

  Definition Trace := ChainedList Point Link.

  Definition reachable (to : Point) : Prop :=
    inhabited (Trace empty_point to).

  Lemma trace_reachable : forall {to},
    Trace empty_point to ->
      reachable to.
  Proof.
    constructor.
    assumption.
  Qed.

  (* The empty state is always reachable *)
  Lemma reachable_empty_state :
    reachable empty_point.
  Proof.
    repeat constructor.
  Qed.

  (* Transitivity property of reachable and ChainTrace *)
  Lemma reachable_trans from to :
    reachable from -> Trace from to -> reachable to.
  Proof.
    intros [].
    constructor.
    eapply ChainedList.clist_app; eauto.
  Qed.

  (* Transitivity property of reachable and ChainStep *)
  Lemma reachable_step from to :
    reachable from -> Link from to -> reachable to.
  Proof.
    intros [].
    do 2 econstructor; eauto.
  Qed.

  Hint Resolve trace_reachable
               reachable_empty_state
               reachable_trans
               reachable_step : core.

  (* A state `to` is reachable through `mid` if `mid` is reachable and there exists a trace
      from `mid` to `to`. This captures that there is a valid execution ending up in `to`
      and going through the state `mid` at some point *)
  Definition reachable_through mid to := reachable mid /\ inhabited (Trace mid to).

  (* A state is always reachable through itself *)
  Lemma reachable_through_refl : forall bstate,
    reachable bstate -> reachable_through bstate bstate.
  Proof.
    intros bstate reach.
    split; auto.
    do 2 constructor.
  Qed.

  (* Transitivity property of reachable_through and ChainStep *)
  Lemma reachable_through_trans' : forall from mid to,
    reachable_through from mid -> Link mid to -> reachable_through from to.
  Proof.
    intros * [reach [trace]] step.
    repeat (econstructor; eauto).
  Qed.

  (* Transitivity property of reachable_through *)
  Lemma reachable_through_trans : forall from mid to,
    reachable_through from mid -> reachable_through mid to -> reachable_through from to.
  Proof.
    intros * [[trace_from] [trace_mid]] [_ [trace_to]].
    do 2 constructor.
    assumption.
    eapply ChainedList.clist_app; eauto.
  Qed.

  (* Reachable_through can also be constructed from ChainStep instead of a
    ChainTrace since a ChainTrace can be constructed from a ChainStep *)
  Lemma reachable_through_step : forall from to,
    reachable from -> Link from to -> reachable_through from to.
  Proof.
    intros * reach_from step.
    apply reachable_through_refl in reach_from.
    eapply reachable_through_trans'; eauto.
  Qed.

  (* Any ChainState that is reachable through another ChainState is reachable *)
  Lemma reachable_through_reachable : forall from to,
    reachable_through from to -> reachable to.
  Proof.
    intros * [[trace_from] [trace_to]].
    constructor.
    eapply ChainedList.clist_app; eauto.
  Qed.

  Hint Resolve reachable_through_refl
               reachable_through_trans'
               reachable_through_trans
               reachable_through_step
               reachable_through_reachable : core.
End Reachable.
