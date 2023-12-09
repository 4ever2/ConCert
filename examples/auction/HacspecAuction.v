(* [[file:auction.org::* auction - Coq code][auction - Coq code:1]] *)

(** This file was automatically generated using Hacspec **)
From ConCert.Examples.Hacspec Require Import HacspecLib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.

From QuickChick Require Import QuickChick.
From ConCert.Examples.Hacspec Require Import QuickChickLib.
From Coq Require Import Morphisms ZArith Basics.
Open Scope Z.
Set Nonrecursive Elimination Schemes.
(* auction - Coq code:1 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:2]] *)
From ConCert.Examples.Hacspec Require Import HacspecLib.
Export HacspecLib.
(* auction - Coq code:2 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:3]] *)
From ConCert.Examples.Hacspec Require Import HacspecConcordium.
Export HacspecConcordium.
(* auction - Coq code:3 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:4]] *)
From ConCert.Examples.Hacspec Require Import ConCertLib.
Export ConCertLib.
(* auction - Coq code:4 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:5]] *)
Inductive auction_state_hacspec_t :=
| NotSoldYet : auction_state_hacspec_t
| Sold : user_address_t -> auction_state_hacspec_t.
Global Instance serializable_auction_state_hacspec_t : Serializable auction_state_hacspec_t :=
  Derive Serializable auction_state_hacspec_t_rect<NotSoldYet,Sold>.


Definition eqb_auction_state_hacspec_t (x y : auction_state_hacspec_t) : bool :=
match x with
   | NotSoldYet => match y with | NotSoldYet=> true | _ => false end
   | Sold a => match y with | Sold b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_auction_state_hacspec_t (x y : auction_state_hacspec_t) : eqb_auction_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_auction_state_hacspec_t : EqDec (auction_state_hacspec_t) :=
  Build_EqDec (auction_state_hacspec_t) (eqb_auction_state_hacspec_t) (eqb_leibniz_auction_state_hacspec_t).

(* auction - Coq code:5 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:6]] *)
Inductive seq_map_t :=
| SeqMap : (public_byte_seq ∏ public_byte_seq) -> seq_map_t.
Global Instance serializable_seq_map_t : Serializable seq_map_t :=
  Derive Serializable seq_map_t_rect<SeqMap>.


Definition eqb_seq_map_t (x y : seq_map_t) : bool :=
match x with
   | SeqMap a => match y with | SeqMap b => a =.? b end
   end.

Definition eqb_leibniz_seq_map_t (x y : seq_map_t) : eqb_seq_map_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_seq_map_t : EqDec (seq_map_t) :=
  Build_EqDec (seq_map_t) (eqb_seq_map_t) (eqb_leibniz_seq_map_t).

(* auction - Coq code:6 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:7]] *)
Inductive state_hacspec_t :=
| StateHacspec : (
  auction_state_hacspec_t ∏
  int64 ∏
  public_byte_seq ∏
  int64 ∏
  seq_map_t
) -> state_hacspec_t.
Global Instance serializable_state_hacspec_t : Serializable state_hacspec_t :=
  Derive Serializable state_hacspec_t_rect<StateHacspec>.


Definition eqb_state_hacspec_t (x y : state_hacspec_t) : bool :=
match x with
   | StateHacspec a => match y with | StateHacspec b => a =.? b end
   end.

Definition eqb_leibniz_state_hacspec_t (x y : state_hacspec_t) : eqb_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_state_hacspec_t : EqDec (state_hacspec_t) :=
  Build_EqDec (state_hacspec_t) (eqb_state_hacspec_t) (eqb_leibniz_state_hacspec_t).

Definition State := context_t ∏ state_hacspec_t.

(* auction - Coq code:7 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:8]] *)
Definition fresh_state_hacspec
  (itm_0 : public_byte_seq)
  (exp_1 : int64): state_hacspec_t :=
  StateHacspec ((
      NotSoldYet,
      @repr WORDSIZE64 0,
      itm_0,
      exp_1,
      SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0)))
    )).

(* auction - Coq code:8 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:9]] *)
Inductive init_parameter_t :=
| InitParameter : (public_byte_seq ∏ int64) -> init_parameter_t.
Global Instance serializable_init_parameter_t : Serializable init_parameter_t :=
  Derive Serializable init_parameter_t_rect<InitParameter>.

(* auction - Coq code:9 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:10]] *)
Notation "'context_state_hacspec_t'" := ((context_t ∏ state_hacspec_t
  )) : hacspec_scope.

(* auction - Coq code:10 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:11]] *)
Definition auction_init
  (ctx_2 : context_t)
  (init_parameter_3 : init_parameter_t): context_state_hacspec_t :=
  (
    ctx_2,
    fresh_state_hacspec (seq_new_ (default) (usize 0)) (@repr WORDSIZE64 0)
  ).
Definition Setup := init_parameter_t.
Definition auction_State (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : ResultMonad.result context_state_hacspec_t unit :=
  ResultMonad.Ok (auction_init (Context (ctx.(ctx_from), ctx.(ctx_origin), repr ctx.(ctx_amount), 0 (* TODO *))) setup).

(* auction - Coq code:11 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:12]] *)
Definition seq_map_entry
  (m_4 : seq_map_t)
  (sender_address_5 : user_address_t): (int64 ∏ seq_map_t) :=
  let 'SeqMap ((m0_6, m1_7)) :=
    m_4 in 
  let res_8 : (int64 ∏ seq_map_t) :=
    (
      @repr WORDSIZE64 0,
      SeqMap ((
          seq_concat ((m0_6)) (array_to_seq (sender_address_5)),
          seq_concat ((m1_7)) (array_to_seq (u64_to_be_bytes (
              @repr WORDSIZE64 0)))
        ))
    ) in 
  let res_8 :=
    foldi (usize 0) ((seq_len ((m0_6))) / (usize 32)) (fun x_9 res_8 =>
      let '(res_8) :=
        if (array_from_seq (32) (seq_slice ((m0_6)) ((x_9) * (usize 32)) (
              usize 32))) array_eq (sender_address_5):bool then (let res_8 :=
            (
              u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_7)) ((
                      x_9) * (usize 8)) (usize 8))),
              SeqMap (((m0_6), (m1_7)))
            ) in 
          (res_8)) else ((res_8)) in 
      (res_8))
    res_8 in 
  res_8.

(* auction - Coq code:12 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:13]] *)
Inductive map_update_t :=
| Update : (int64 ∏ seq_map_t) -> map_update_t.
Global Instance serializable_map_update_t : Serializable map_update_t :=
  Derive Serializable map_update_t_rect<Update>.


Definition eqb_map_update_t (x y : map_update_t) : bool :=
match x with
   | Update a => match y with | Update b => a =.? b end
   end.

Definition eqb_leibniz_map_update_t (x y : map_update_t) : eqb_map_update_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_map_update_t : EqDec (map_update_t) :=
  Build_EqDec (map_update_t) (eqb_map_update_t) (eqb_leibniz_map_update_t).

(* auction - Coq code:13 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:14]] *)
Definition seq_map_update_entry
  (m_10 : seq_map_t)
  (sender_address_11 : user_address_t)
  (amount_12 : int64): map_update_t :=
  let 'SeqMap ((m0_13, m1_14)) :=
    m_10 in 
  let res_15 : map_update_t :=
    Update ((
        amount_12,
        SeqMap ((
            seq_concat ((m0_13)) (array_to_seq (sender_address_11)),
            seq_concat ((m1_14)) (array_to_seq (u64_to_be_bytes (amount_12)))
          ))
      )) in 
  let res_15 :=
    foldi (usize 0) ((seq_len ((m0_13))) / (usize 32)) (fun x_16 res_15 =>
      let '(res_15) :=
        if (array_from_seq (32) (seq_slice ((m0_13)) ((x_16) * (usize 32)) (
              usize 32))) array_eq (sender_address_11):bool then (let res_15 :=
            Update ((
                amount_12,
                SeqMap ((
                    seq_update ((m0_13)) ((x_16) * (usize 32)) (
                      array_to_seq (sender_address_11)),
                    seq_update ((m1_14)) ((x_16) * (usize 8)) (
                      array_to_seq (u64_to_be_bytes (amount_12)))
                  ))
              )) in 
          (res_15)) else ((res_15)) in 
      (res_15))
    res_15 in 
  res_15.

(* auction - Coq code:14 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:15]] *)
Inductive bid_error_hacspec_t :=
| ContractSender : bid_error_hacspec_t
| BidTooLow : bid_error_hacspec_t
| BidsOverWaitingForAuctionFinalization : bid_error_hacspec_t
| AuctionIsFinalized : bid_error_hacspec_t.
Global Instance serializable_bid_error_hacspec_t : Serializable bid_error_hacspec_t :=
  Derive Serializable bid_error_hacspec_t_rect<ContractSender,BidTooLow,BidsOverWaitingForAuctionFinalization,AuctionIsFinalized>.


Definition eqb_bid_error_hacspec_t (x y : bid_error_hacspec_t) : bool :=
match x with
   | ContractSender => match y with | ContractSender=> true | _ => false end
   | BidTooLow => match y with | BidTooLow=> true | _ => false end
   | BidsOverWaitingForAuctionFinalization =>
       match y with
       | BidsOverWaitingForAuctionFinalization=> true
       | _ => false
       end
   | AuctionIsFinalized =>
       match y with
       | AuctionIsFinalized=> true
       | _ => false
       end
   end.

Definition eqb_leibniz_bid_error_hacspec_t (x y : bid_error_hacspec_t) : eqb_bid_error_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_bid_error_hacspec_t : EqDec (bid_error_hacspec_t) :=
  Build_EqDec (bid_error_hacspec_t) (eqb_bid_error_hacspec_t) (eqb_leibniz_bid_error_hacspec_t).

(* auction - Coq code:15 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:16]] *)
Notation "'auction_bid_result_t'" := ((
    result state_hacspec_t bid_error_hacspec_t)) : hacspec_scope.
(* auction - Coq code:16 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:17]] *)
Definition auction_bid_hacspec
  (ctx_17 : context_t)
  (amount_18 : int64)
  (state_19 : state_hacspec_t): auction_bid_result_t :=
  let 'StateHacspec ((
        auction_state_20,
        highest_bid_21,
        st2_22,
        expiry_23,
        st4_24
      )) :=
    (state_19) in 
  ifbnd (negb ((auction_state_20) =.? (NotSoldYet))) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (
        AuctionIsFinalized)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  let 'Context ((owner_25, sender_26, balance_27, slot_time_28)) :=
    ctx_17 in 
  ifbnd (negb ((slot_time_28) <=.? (expiry_23))) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (
        BidsOverWaitingForAuctionFinalization)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(bid_to_update_29, new_map_30) :=
    seq_map_entry ((st4_24)) (sender_26) in 
  let '(updated_bid_31, updated_map_32) :=
    match seq_map_update_entry ((st4_24)) (sender_26) ((bid_to_update_29) .+ (
        amount_18)) with
    | Update (updated_bid_33, updated_map_34) => (updated_bid_33, updated_map_34
    )
    end in 
  ifbnd (negb ((updated_bid_31) >.? (highest_bid_21))) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (BidTooLow)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok state_hacspec_t bid_error_hacspec_t (StateHacspec ((
        auction_state_20,
        updated_bid_31,
        st2_22,
        expiry_23,
        updated_map_32
      )))))).

(* auction - Coq code:17 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:18]] *)
Definition auction_bid
  (ctx_35 : context_state_hacspec_t)
  (amount_36 : int64): (option (context_state_hacspec_t ∏ list_action_t)) :=
  let s_37 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some (context_state_hacspec_t ∏ list_action_t) ((ctx_35, s_37)).

Definition bid (amount : int64) (st : State) :=
  auction_bid st amount.

(* auction - Coq code:18 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:19]] *)
Inductive finalize_error_hacspec_t :=
| BidMapError : finalize_error_hacspec_t
| AuctionStillActive : finalize_error_hacspec_t
| AuctionFinalized : finalize_error_hacspec_t.
Global Instance serializable_finalize_error_hacspec_t : Serializable finalize_error_hacspec_t :=
  Derive Serializable finalize_error_hacspec_t_rect<BidMapError,AuctionStillActive,AuctionFinalized>.


Definition eqb_finalize_error_hacspec_t (x y : finalize_error_hacspec_t) : bool :=
match x with
   | BidMapError => match y with | BidMapError=> true | _ => false end
   | AuctionStillActive =>
       match y with
       | AuctionStillActive=> true
       | _ => false
       end
   | AuctionFinalized => match y with | AuctionFinalized=> true | _ => false end
   end.

Definition eqb_leibniz_finalize_error_hacspec_t (x y : finalize_error_hacspec_t) : eqb_finalize_error_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_finalize_error_hacspec_t : EqDec (finalize_error_hacspec_t) :=
  Build_EqDec (finalize_error_hacspec_t) (eqb_finalize_error_hacspec_t) (eqb_leibniz_finalize_error_hacspec_t).


(* auction - Coq code:19 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:20]] *)
Notation "'finalize_context_t'" := ((int64 ∏ user_address_t ∏ int64
  )) : hacspec_scope.
(* auction - Coq code:20 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:21]] *)
Inductive finalize_action_t :=
| Accept : finalize_action_t
| SimpleTransfer : public_byte_seq -> finalize_action_t.
Global Instance serializable_finalize_action_t : Serializable finalize_action_t :=
  Derive Serializable finalize_action_t_rect<Accept,SimpleTransfer>.


Definition eqb_finalize_action_t (x y : finalize_action_t) : bool :=
match x with
   | Accept => match y with | Accept=> true | _ => false end
   | SimpleTransfer a =>
       match y with
       | SimpleTransfer b => a =.? b
       | _ => false
       end
   end.

Definition eqb_leibniz_finalize_action_t (x y : finalize_action_t) : eqb_finalize_action_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_finalize_action_t : EqDec (finalize_action_t) :=
  Build_EqDec (finalize_action_t) (eqb_finalize_action_t) (eqb_leibniz_finalize_action_t).
(* auction - Coq code:21 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:22]] *)
Inductive bid_remain_t :=
| BidNone : bid_remain_t
| BidSome : int64 -> bid_remain_t.
Global Instance serializable_bid_remain_t : Serializable bid_remain_t :=
  Derive Serializable bid_remain_t_rect<BidNone,BidSome>.


Definition eqb_bid_remain_t (x y : bid_remain_t) : bool :=
match x with
   | BidNone => match y with | BidNone=> true | _ => false end
   | BidSome a => match y with | BidSome b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_bid_remain_t (x y : bid_remain_t) : eqb_bid_remain_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_bid_remain_t : EqDec (bid_remain_t) :=
  Build_EqDec (bid_remain_t) (eqb_bid_remain_t) (eqb_leibniz_bid_remain_t).
(* auction - Coq code:22 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:23]] *)
Notation "'auction_finalize_result_t'" := ((result (
      state_hacspec_t ∏
      finalize_action_t
    ) finalize_error_hacspec_t)) : hacspec_scope.
(* auction - Coq code:23 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:24]] *)
Definition auction_finalize_hacspec
  (ctx_38 : finalize_context_t)
  (state_39 : state_hacspec_t): auction_finalize_result_t :=
  let 'StateHacspec ((
        auction_state_40,
        highest_bid_41,
        st2_42,
        expiry_43,
        SeqMap ((m0_44, m1_45))
      )) :=
    (state_39) in 
  let result_46 : (result (state_hacspec_t ∏ finalize_action_t
      ) finalize_error_hacspec_t) :=
    @Ok (state_hacspec_t ∏ finalize_action_t) finalize_error_hacspec_t ((
        (state_39),
        Accept
      )) in 
  ifbnd (negb ((auction_state_40) =.? (NotSoldYet))) : bool
  thenbnd (bind (@Err (state_hacspec_t ∏ finalize_action_t
      ) finalize_error_hacspec_t (AuctionFinalized)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_47, owner_48, balance_49) :=
    ctx_38 in 
  ifbnd (negb ((slot_time_47) >.? (expiry_43))) : bool
  thenbnd (bind (@Err (state_hacspec_t ∏ finalize_action_t
      ) finalize_error_hacspec_t (AuctionStillActive)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (balance_49) !=.? (@repr WORDSIZE64 0) : bool
  thenbnd (let return_action_50 : finalize_action_t :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (default) (usize 0)) (
            array_to_seq (owner_48))) (array_to_seq (u64_to_be_bytes (
            highest_bid_41)))) in 
    let remaining_bid_51 : bid_remain_t :=
      BidNone in 
    bind (foldibnd (usize 0) to ((seq_len ((m0_44))) / (usize 32)) for (
        auction_state_40,
        return_action_50,
        remaining_bid_51
      ) >> (fun x_52 '(auction_state_40, return_action_50, remaining_bid_51) =>
      let addr_53 : user_address_t :=
        array_from_seq (32) (seq_slice ((m0_44)) ((x_52) * (usize 32)) (
            usize 32)) in 
      let amnt_54 : int64 :=
        u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_45)) ((x_52) * (
                usize 8)) (usize 8))) in 
      ifbnd (amnt_54) <.? (highest_bid_41) : bool
      then (let return_action_50 :=
          match return_action_50 with
          | Accept => Accept
          | SimpleTransfer m_55 => SimpleTransfer (seq_concat (seq_concat (
                m_55) (array_to_seq (addr_53))) (array_to_seq (u64_to_be_bytes (
                amnt_54))))
          end in 
        (auction_state_40, return_action_50, remaining_bid_51))
      elsebnd(ifbnd (negb ((remaining_bid_51) =.? (BidNone))) : bool
        thenbnd (bind (@Err (state_hacspec_t ∏ finalize_action_t
            ) finalize_error_hacspec_t (BidMapError)) (fun _ =>  Ok (tt)))
        else (tt) >> (fun 'tt =>
        let auction_state_40 :=
          Sold (addr_53) in 
        let remaining_bid_51 :=
          BidSome (amnt_54) in 
        Ok ((auction_state_40, return_action_50, remaining_bid_51)))) >> (fun '(
        auction_state_40,
        return_action_50,
        remaining_bid_51
      ) =>
      Ok ((auction_state_40, return_action_50, remaining_bid_51))))) (fun '(
        auction_state_40,
        return_action_50,
        remaining_bid_51
      ) => let result_46 :=
        match remaining_bid_51 with
        | BidSome amount_56 => (if ((negb ((amount_56) =.? (
                  highest_bid_41)))):bool then (@Err (
              state_hacspec_t ∏
              finalize_action_t
            ) finalize_error_hacspec_t (BidMapError)) else (@Ok (
              state_hacspec_t ∏
              finalize_action_t
            ) finalize_error_hacspec_t ((
                StateHacspec ((
                    auction_state_40,
                    highest_bid_41,
                    st2_42,
                    expiry_43,
                    SeqMap (((m0_44), (m1_45)))
                  )),
                return_action_50
              ))))
        | BidNone => @Err (state_hacspec_t ∏ finalize_action_t
        ) finalize_error_hacspec_t (BidMapError)
        end in 
      bind ((result_46)) (fun _ =>  Ok ((auction_state_40, result_46)))))
  else ((auction_state_40, result_46)) >> (fun '(auction_state_40, result_46) =>
  result_46))).

(* auction - Coq code:24 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:25]] *)
Definition auction_finalize
  (ctx_57 : context_state_hacspec_t): (option (
      context_state_hacspec_t ∏
      list_action_t
    )) :=
  let s_58 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some (context_state_hacspec_t ∏ list_action_t) ((ctx_57, s_58)).

Definition finalize (st : State) :=
  auction_finalize st.

(* auction - Coq code:25 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:31]] *)
Inductive Msg :=
| BID
| FINALIZE.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<BID,FINALIZE>.
Definition auction_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : ResultMonad.result (State * list ActionBody) unit :=
  match msg with
  | Some BID => to_action_body_list ctx (bid (repr ctx.(ctx_amount)) state)
  | Some FINALIZE => to_action_body_list ctx (finalize state)
  | None => ResultMonad.Err tt
  end.

Definition auction_contract : Contract Setup Msg State unit :=
  build_contract auction_State auction_receive.

(* auction - Coq code:31 ends here *)