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
  (* Show equivalence of the init functions *)
  Theorem init_equiv_err : forall chain ctx,
    isErr (HacspecPiggyBank.PiggyBank_State chain ctx tt) =
    isErr (PiggyBank.init chain ctx tt).
  Proof.
    now intros.
  Qed.

  Theorem init_equiv_ok : forall chain ctx,
    isOk (HacspecPiggyBank.PiggyBank_State chain ctx tt) =
    isOk (PiggyBank.init chain ctx tt).
  Proof.
    now intros.
  Qed.

  Theorem init_equiv : forall chain ctx s1 s2,
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
  (* Show equivlance for receive functions *)
  Lemma receive_equiv_err : forall chain ctx s1 s2 msg1 msg2,
    0 <= (ctx_amount ctx) ->
    StateEquiv s1 s2 ->
    MsgEquiv msg1 msg2 ->
    isErr (HacspecPiggyBank.PiggyBank_receive chain ctx s1 msg1) =
    isErr (PiggyBank.receive chain ctx s2 msg2).
  Proof.
    intros * amount_pos Hstate_equiv Hmsg_equiv.
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

  Lemma receive_equiv_ok : forall chain ctx s1 s2 msg1 msg2,
    0 <= (ctx_amount ctx) ->
    StateEquiv s1 s2 ->
    MsgEquiv msg1 msg2 ->
    isOk (HacspecPiggyBank.PiggyBank_receive chain ctx s1 msg1) =
    isOk (PiggyBank.receive chain ctx s2 msg2).
  Proof.
    intros * amount_pos Hstate_equiv Hmsg_equiv.
    eapply receive_equiv_err in Hmsg_equiv; eauto.
    Unshelve. 2: eauto.
    destruct HacspecPiggyBank.PiggyBank_receive;
      destruct PiggyBank.receive; auto.
  Qed.

  Lemma receive_equiv : forall chain ctx s1 s2 msg1 msg2 ns1 ns2 acts1 acts2,
    0 <= (ctx_amount ctx) ->
    0 <= (PiggyBank.balance s2) ->
    (0 <= (PiggyBank.balance s2 + ctx_amount ctx) < @MachineIntegers.modulus MachineIntegers.WORDSIZE64) ->
    StateEquiv s1 s2 ->
    MsgEquiv msg1 msg2 ->
    HacspecPiggyBank.PiggyBank_receive chain ctx s1 msg1 = Ok (ns1, acts1) ->
    PiggyBank.receive chain ctx s2 msg2 = Ok (ns2, acts2) ->
      StateEquiv ns1 ns2 /\
      acts1 = acts2.
  Proof.
    intros * amount_pos balance_pos Hoverflow Hstate_equiv Hmsg_equiv Hreceive1 Hreceive2.
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
