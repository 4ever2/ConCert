From ConCert.Examples.PiggyBank Require PiggyBank.
From ConCert.Examples.PiggyBank Require HacspecPiggyBank.
From ConCert.Examples.Hacspec Require ConcordiumImpls.
From ConCert.Examples.Hacspec Require MachineIntegers.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From Coq Require Import ZArith_base.
From Coq Require Import Lia.

Open Scope Z_scope.



(* Utility lemmas and definitions *)
Lemma hacspec_address_neqb : forall (x y : Blockchain.Address),
  @address_neqb ConCertLib.BaseTypes x y =
  negb (HacspecLib.array_eq_ MachineIntegers.eq x y).
Proof.
  intros.
  reflexivity.
Qed.

Record ValidContext (ctx : ContractCallContext) := {
  ctx_origin_valid : address_is_contract ctx.(ctx_origin) = false;
  ctx_contract_address_valid : address_is_contract ctx.(ctx_contract_address) = true;
  ctx_contract_balance_valid : 0 <= ctx.(ctx_contract_balance);
  ctx_amount_valid : 0 <= ctx.(ctx_amount);
}.

Record ValidChain (chain : Chain) := {
  chain_height_valid : (chain.(chain_height) <= chain.(current_slot))%nat;
  finalized_height_valid : (chain.(finalized_height) < S chain.(chain_height))%nat;
}.

Theorem origin_user_address : forall bstate,
  reachable bstate ->
  List.Forall (fun act => address_is_contract act.(act_origin) = false) (chain_state_queue bstate).
Proof.
  intros * [trace].
  remember empty_state.
  induction trace; subst; try auto.
  destruct_chain_step.
  - clear env_eq.
    apply List.Forall_forall.
    rewrite List.Forall_forall in origin_correct.
    rewrite List.Forall_forall in acts_from_accs.
    intros x Hin.
    specialize (origin_correct x Hin).
    specialize (acts_from_accs x Hin).
    unfold act_is_from_account, act_origin_is_eq_from in *.
    destruct_address_eq; try discriminate.
    now rewrite e.
  - rewrite queue_prev in *.
    rewrite queue_new in *.
    specialize (IHtrace eq_refl).
    apply list.Forall_cons in IHtrace as [Hact IHtrace].
    apply All_Forall.app_Forall; auto.
    destruct_action_eval; try (subst; apply List.Forall_nil).
    + subst.
      apply All_Forall.Forall_map.
      cbn in *.
      rewrite Hact.
      apply List.Forall_forall.
      reflexivity.
  - rewrite queue_prev in *.
    rewrite queue_new in *.
    specialize (IHtrace eq_refl).
    apply list.Forall_cons in IHtrace as [Hact IHtrace].
    assumption.
  - eapply Extras.forall_respects_permutation; eauto.
Qed.

Definition context_valid' {from to : ChainState} (trace : ChainTrace from to) : Prop.
Proof.
  induction trace.
  - exact True.
  - destruct_chain_step.
    + apply IHtrace.
    + destruct_action_eval.
      * exact True.
      * match goal with
        | H : wc_init _ _ ?ctx _ = Ok _ |- _ =>
          exact (ValidContext ctx)
        end.
      * match goal with
        | H : wc_receive _ _ ?ctx _ _ = Ok _ |- _ =>
          exact (ValidContext ctx)
        end.
    + apply IHtrace.
    + apply IHtrace.
Defined.

Lemma context_valid : forall bstate (trace : ChainTrace empty_state bstate),
  context_valid' trace.
Proof.
  intros.
  remember empty_state as e.
  induction trace; try apply I.
  destruct_chain_step; try now apply IHtrace.
  destruct_action_eval; try apply I.
  - (* init case *)
    cbn.
    constructor.
    + subst.
      specialize (origin_user_address mid) as H.
      rewrite queue_prev in *.
      apply list.Forall_cons in H as [Hact _].
      * assumption.
      * now apply trace_reachable.
    + assumption.
    + cbn. lia.
    + cbn. lia.
  - (* receive case *)
    cbn.
    constructor.
    + subst.
      specialize (origin_user_address mid) as H.
      rewrite queue_prev in *.
      apply list.Forall_cons in H as [Hact _].
      * assumption.
      * now apply trace_reachable.
    + apply contract_addr_format in deployed.
      assumption.
      subst. now apply trace_reachable.
    + subst.
      rewrite_environment_equiv. cbn.
      destruct_address_eq; subst; try contradiction.
      lia.
      specialize (account_balance_nonnegative _ to_addr (trace_reachable trace)).
      lia.
    + cbn. lia.
Qed.

Lemma current_slot_chain_height bstate :
  reachable bstate ->
  (bstate.(chain_height) <= bstate.(current_slot))%nat.
Proof.
  intros [trace].
  remember empty_state.
  induction trace as [ | Heq from to trace IH step ]; subst.
  - auto.
  - destruct_chain_step;
    try destruct_action_eval;
    rewrite_environment_equiv;
    auto.
    + inversion valid_header. cbn.
      rewrite valid_height.
      specialize (IH eq_refl).
      lia.
Qed.

Definition chain_valid' {from to : ChainState} (trace : ChainTrace from to) : Prop.
Proof.
  induction trace.
  - exact True.
  - destruct_chain_step.
    + apply IHtrace.
    + destruct_action_eval.
      * exact True.
      * match goal with
        | H : wc_init _ ?chain _ _ = Ok _ |- _ =>
          exact (ValidChain chain)
        end.
      * match goal with
        | H : wc_receive _ ?chain _ _ _ = Ok _ |- _ =>
          exact (ValidChain chain)
        end.
    + apply IHtrace.
    + apply IHtrace.
Defined.

From ConCert.Execution Require Import BuildUtils.
Lemma chain_valid : forall bstate (trace : ChainTrace empty_state bstate),
  chain_valid' trace.
Proof.
  intros.
  remember empty_state.
  induction trace; try apply I.
  destruct_chain_step; try now apply IHtrace.
  destruct_action_eval; try apply I.
  - (* init case *)
    cbn. subst.
    constructor.
    + apply current_slot_chain_height.
      now apply trace_reachable.
    + apply finalized_heigh_chain_height.
      now apply trace_reachable.
  - (* receive case *)
    cbn. subst.
    constructor.
    + apply current_slot_chain_height.
      now apply trace_reachable.
    + apply finalized_heigh_chain_height.
      now apply trace_reachable.
Qed.
  


Section ContractTypeEquiv.
(* Define equivalence of Msg types *)

Definition msg_convert (msg : PiggyBank.Msg) : HacspecPiggyBank.Msg :=
  match msg with
  | PiggyBank.Insert => HacspecPiggyBank.INSERT
  | PiggyBank.Smash => HacspecPiggyBank.SMASH
  end.

Definition msg_convert' (msg : HacspecPiggyBank.Msg) : PiggyBank.Msg :=
  match msg with
  | HacspecPiggyBank.INSERT => PiggyBank.Insert
  | HacspecPiggyBank.SMASH => PiggyBank.Smash
  end.

Lemma msg_equiv : forall msg,
  msg_convert (msg_convert' msg) = msg.
Proof.
  now intros [].
Qed.

Lemma msg_equiv' : forall msg,
  msg_convert' (msg_convert msg) = msg.
Proof.
  now intros [].
Qed.

Record MsgEquiv (s1 : option HacspecPiggyBank.Msg) (s2 : option PiggyBank.Msg) : Prop :=
  build_msg_equiv {
    msg_eq : match (s1, s2) with
            | (Some s1, Some s2) => msg_convert' s1 = s2
            | _ => False
            end
  }.



(* Define equivalence of PiggyState types *)
Definition piggyState_convert (msg : PiggyBank.PiggyState) : HacspecPiggyBank.piggy_bank_state_hacspec_t :=
  match msg with
  | PiggyBank.Intact => HacspecPiggyBank.Intact
  | PiggyBank.Smashed => HacspecPiggyBank.Smashed
  end.

Definition piggyState_convert' (msg : HacspecPiggyBank.piggy_bank_state_hacspec_t) : PiggyBank.PiggyState :=
  match msg with
  | HacspecPiggyBank.Intact => PiggyBank.Intact
  | HacspecPiggyBank.Smashed => PiggyBank.Smashed
  end.

Lemma piggyState_equiv : forall s,
  piggyState_convert (piggyState_convert' s) = s.
Proof.
  now intros [].
Qed.

Lemma piggyState_equiv' : forall s,
  piggyState_convert' (piggyState_convert s) = s.
Proof.
  now intros [].
Qed.

Record PiggyStateEquiv (s1 : HacspecPiggyBank.piggy_bank_state_hacspec_t) (s2 : PiggyBank.PiggyState) : Prop :=
  build_piggystate_equiv {
    piggyState_eq : piggyState_convert' s1 = s2
  }.



(* Define equivalence of State types *)
Record StateEquiv (s1 : HacspecPiggyBank.State) (s2 : PiggyBank.State) : Prop :=
  build_state_equiv {
    balance_eq : match (fst s1) with
                 | ConcordiumImpls.Context (_, _, a, _) =>
                    a = (MachineIntegers.repr (PiggyBank.balance s2))
                 end;
    owner_eq : match (fst s1) with
               | ConcordiumImpls.Context (a, _, _, _) =>
                  a = (PiggyBank.owner s2)
               end;
    state_eq : PiggyStateEquiv (snd s1) (PiggyBank.piggyState s2)
  }.
End ContractTypeEquiv.

Section InitEquivalence.
  Context {chain : Chain}.
  Context {ctx : ContractCallContext}.
  Context `{ValidChain chain}.
  Context `{ValidContext ctx}.

  (* Show equivalence of the init functions *)
  Theorem init_equiv_err :
    isErr (HacspecPiggyBank.PiggyBank_State chain ctx tt) =
    isErr (PiggyBank.init chain ctx tt).
  Proof.
    now intros.
  Qed.

  Theorem init_equiv_ok :
    isOk (HacspecPiggyBank.PiggyBank_State chain ctx tt) =
    isOk (PiggyBank.init chain ctx tt).
  Proof.
    now intros.
  Qed.

  Theorem init_equiv : forall s1 s2,
    HacspecPiggyBank.PiggyBank_State chain ctx tt = Ok s1 ->
    PiggyBank.init chain ctx tt = Ok s2 ->
    StateEquiv s1 s2.
  Proof.
    intros * Hs1 Hs2.
    inversion_clear Hs1.
    inversion_clear Hs2.
    constructor.
    - reflexivity.
    - reflexivity.
    - constructor. reflexivity.
  Qed.
End InitEquivalence.

Section ReceiveEquivalence.
  Context {chain : Chain}.
  Context {ctx : ContractCallContext}.
  Context `{ValidChain chain}.
  Context `{ValidContext ctx}.

  (* Show equivlance for receive functions *)
  Lemma receive_equiv_err : forall s1 s2 msg1 msg2,
    StateEquiv s1 s2 ->
    MsgEquiv msg1 msg2 ->
    isErr (HacspecPiggyBank.PiggyBank_receive chain ctx s1 msg1) =
    isErr (PiggyBank.receive chain ctx s2 msg2).
  Proof.
    intros * Hstate_equiv Hmsg_equiv.
    destruct msg1; destruct msg2;
      try reflexivity;
      inversion_clear Hmsg_equiv;
      try contradiction.
    subst.
    destruct s1 as [s1_ctx s1].
    inversion_clear Hstate_equiv.
    inversion_clear state_eq0.
    cbn in piggyState_eq0.
    destruct m; cbn.
    - (* m = insert *)
      destruct ValidContext0 as [_ _ _ amount_pos].  
      apply Z.ltb_ge in amount_pos.
      rewrite amount_pos. cbn.
      unfold PiggyBank.is_smashed.
      rewrite <- piggyState_eq0. clear piggyState_eq0.
      
      unfold HacspecPiggyBank.PiggyBank_receive.
      unfold HacspecPiggyBank.insert.
      unfold HacspecPiggyBank.piggy_insert.
      unfold HacspecPiggyBank.piggy_insert_hacspec.
      
      destruct s1_ctx.
      do 3 destruct p.
      
      destruct s1; reflexivity.
    - (* m = smash *)
      unfold PiggyBank.is_smashed.
      rewrite <- piggyState_eq0. clear piggyState_eq0.
      unfold HacspecPiggyBank.PiggyBank_receive.
      unfold HacspecPiggyBank.smash.
      unfold HacspecPiggyBank.piggy_smash.
      unfold HacspecPiggyBank.piggy_smash_hacspec.
      
      destruct s1_ctx.
      do 3 destruct p.

      cbn in owner_eq0.
      subst.
      rewrite <- hacspec_address_neqb.
      rewrite address_neq_sym.
      (* eliminate case where the caller is not the owner *)
      destruct (Blockchain.address_neqb _ _); try reflexivity. cbn.

      (* case match on whether the piggybank is smashed already *)
      destruct s1; try reflexivity.
  Qed.

  Lemma receive_equiv_ok : forall s1 s2 msg1 msg2,
    StateEquiv s1 s2 ->
    MsgEquiv msg1 msg2 ->
    isOk (HacspecPiggyBank.PiggyBank_receive chain ctx s1 msg1) =
    isOk (PiggyBank.receive chain ctx s2 msg2).
  Proof.
    intros * Hstate_equiv Hmsg_equiv.
    eapply receive_equiv_err in Hmsg_equiv; eauto.
    destruct HacspecPiggyBank.PiggyBank_receive;
      destruct PiggyBank.receive; auto.
  Qed.

  Lemma receive_equiv : forall s1 s2 msg1 msg2 ns1 ns2 acts1 acts2,
    0 <= (PiggyBank.balance s2) ->
    (0 <= (PiggyBank.balance s2 + ctx_amount ctx) < @MachineIntegers.modulus MachineIntegers.WORDSIZE64) ->
    StateEquiv s1 s2 ->
    MsgEquiv msg1 msg2 ->
    HacspecPiggyBank.PiggyBank_receive chain ctx s1 msg1 = Ok (ns1, acts1) ->
    PiggyBank.receive chain ctx s2 msg2 = Ok (ns2, acts2) ->
      StateEquiv ns1 ns2 /\
      acts1 = acts2.
  Proof.
    intros * balance_pos Hoverflow Hstate_equiv Hmsg_equiv Hreceive1 Hreceive2.
    destruct ValidContext0 as [_ _ _ amount_pos].
    destruct msg1; destruct msg2;
      try reflexivity;
      inversion_clear Hmsg_equiv;
      try contradiction.
    subst.
    destruct s1 as [s1_ctx s1].
    inversion_clear Hstate_equiv.
    inversion_clear state_eq0.
    cbn in piggyState_eq0.
    destruct m; cbn in *.
    - (* m = insert *)
      apply Z.ltb_ge in amount_pos as amount_pos_b.
      rewrite amount_pos_b in Hreceive2. cbn in *.
      clear amount_pos_b.
      unfold PiggyBank.is_smashed in Hreceive2.
      rewrite <- piggyState_eq0 in Hreceive2.
      
      unfold HacspecPiggyBank.PiggyBank_receive in Hreceive1.
      unfold HacspecPiggyBank.insert in Hreceive1.
      unfold HacspecPiggyBank.piggy_insert in Hreceive1.
      unfold HacspecPiggyBank.piggy_insert_hacspec in Hreceive1.
      
      destruct s1_ctx.
      do 3 destruct p.
      subst.
      (* dismiss case where the piggybank is smashed *)
      destruct s1; try discriminate.
      inversion_clear Hreceive2.
      inversion_clear Hreceive1.
      (* show equivalence of output *)
      split; auto.
      constructor.
      + cbn.
        apply MachineIntegers.eqm_samerepr.
        cbn.
        rewrite !MachineIntegers.Z_mod_modulus_eq.
        rewrite Z.mod_small by lia.
        rewrite Z.mod_small by lia.
        rewrite Z.add_comm.
        apply MachineIntegers.eqm_refl.
      + reflexivity.
      + constructor.
        assumption.
    - (* m = smash *)
      unfold PiggyBank.is_smashed in Hreceive2.
      rewrite <- piggyState_eq0 in Hreceive2. clear piggyState_eq0.
      unfold HacspecPiggyBank.PiggyBank_receive in Hreceive1.
      unfold HacspecPiggyBank.smash in Hreceive1.
      unfold HacspecPiggyBank.piggy_smash in Hreceive1.
      unfold HacspecPiggyBank.piggy_smash_hacspec in Hreceive1.
      
      destruct s1_ctx.
      do 3 destruct p.
      subst.

      rewrite <- hacspec_address_neqb in Hreceive1.
      rewrite address_neq_sym in Hreceive1.
      (* eliminate case where the caller is not the owner *)
      destruct (Blockchain.address_neqb _ _); try discriminate.

      (* case match on whether the piggybank is smashed already *)
      destruct s1; try discriminate.
      inversion_clear Hreceive2.
      inversion_clear Hreceive1.
      (* show equivalence of output *)
      split.
      + (* Show state equiv *)
        constructor.
        * reflexivity.
        * reflexivity.
        * constructor.
          reflexivity.
      + (* show actions equiv *)
        f_equal.
        f_equal.
        rewrite !MachineIntegers.Z_mod_modulus_eq.
        rewrite <- Z.add_mod.
        rewrite Z.mod_small; auto.
        assert (H : forall x : Z, x > 0 -> x <> 0) by lia.
        apply H.
        apply MachineIntegers.modulus_pos.
  Qed.
End ReceiveEquivalence.
