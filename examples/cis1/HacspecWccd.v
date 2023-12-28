(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:1]] *)
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
From Coq Require Import Morphisms ZArith Basics.
Open Scope Z.
Set Nonrecursive Elimination Schemes.
(* wccd - Coq code:1 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:2]] *)
From ConCert.Examples.Hacspec Require Import HacspecLib.
Export HacspecLib.
(* wccd - Coq code:2 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:3]] *)
From ConCert.Examples.Hacspec Require Import HacspecConcordium.
Export HacspecConcordium.
(* wccd - Coq code:3 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:4]] *)
From ConCert.Examples.Hacspec Require Import ConCertLib.
Export ConCertLib.
(* wccd - Coq code:4 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:5]] *)
Definition transfer_event_tag_v : int8 :=
  @repr WORDSIZE8 255.
(* wccd - Coq code:5 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:6]] *)
Definition mint_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 1).
(* wccd - Coq code:6 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:7]] *)
Definition burn_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 2).
(* wccd - Coq code:7 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:8]] *)
Definition update_operator_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 3).
(* wccd - Coq code:8 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:9]] *)
Definition token_metadata_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 4).
(* wccd - Coq code:9 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:10]] *)
Definition sha256_t := nseq (int8) (usize 32).
(* wccd - Coq code:10 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:11]] *)
Inductive metadata_url_t :=
| MetadataUrl : (string_t ∏ (option sha256_t)) -> metadata_url_t.
Global Instance serializable_metadata_url_t : Serializable metadata_url_t :=
  Derive Serializable metadata_url_t_rect<MetadataUrl>.
(* wccd - Coq code:11 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:12]] *)
Inductive token_id_vec_t :=
| TokenIdVec : public_byte_seq -> token_id_vec_t.
Global Instance serializable_token_id_vec_t : Serializable token_id_vec_t :=
  Derive Serializable token_id_vec_t_rect<TokenIdVec>.
(* wccd - Coq code:12 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:13]] *)
Inductive token_id_uint32_t :=
| TokenIdU32 : int32 -> token_id_uint32_t.
Global Instance serializable_token_id_uint32_t : Serializable token_id_uint32_t :=
  Derive Serializable token_id_uint32_t_rect<TokenIdU32>.
(* wccd - Coq code:13 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:14]] *)
Inductive token_id_uint16_t :=
| TokenIdU16 : int16 -> token_id_uint16_t.
Global Instance serializable_token_id_uint16_t : Serializable token_id_uint16_t :=
  Derive Serializable token_id_uint16_t_rect<TokenIdU16>.
(* wccd - Coq code:14 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:15]] *)
Inductive token_id_uint8_t :=
| TokenIdU8 : int8 -> token_id_uint8_t.
Global Instance serializable_token_id_uint8_t : Serializable token_id_uint8_t :=
  Derive Serializable token_id_uint8_t_rect<TokenIdU8>.
(* wccd - Coq code:15 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:16]] *)
Inductive token_id_unit_t :=
| TokenIdUnit : unit -> token_id_unit_t.
Global Instance serializable_token_id_unit_t : Serializable token_id_unit_t :=
  Derive Serializable token_id_unit_t_rect<TokenIdUnit>.
(* wccd - Coq code:16 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:17]] *)
Notation "'token_amount_t'" := (int64) : hacspec_scope.
(* wccd - Coq code:17 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:18]] *)
Inductive operator_update_t :=
| Remove : operator_update_t
| Add : operator_update_t.
Global Instance serializable_operator_update_t : Serializable operator_update_t :=
  Derive Serializable operator_update_t_rect<Remove,Add>.
(* wccd - Coq code:18 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:19]] *)
Inductive update_operator_event_t :=
| UpdateOperatorEvent : (operator_update_t ∏ user_address_t ∏ user_address_t
) -> update_operator_event_t.
Global Instance serializable_update_operator_event_t : Serializable update_operator_event_t :=
  Derive Serializable update_operator_event_t_rect<UpdateOperatorEvent>.
(* wccd - Coq code:19 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:20]] *)
Notation "'contract_token_id_t'" := (token_id_unit_t) : hacspec_scope.
(* wccd - Coq code:20 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:21]] *)
Definition token_id_wccd_v : contract_token_id_t :=
  TokenIdUnit (tt).
(* wccd - Coq code:21 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:22]] *)
Inductive state_hacspec_t :=
| StateHacspec : public_byte_seq -> state_hacspec_t.
Global Instance serializable_state_hacspec_t : Serializable state_hacspec_t :=
  Derive Serializable state_hacspec_t_rect<StateHacspec>.
Definition State := context_t ∏ state_hacspec_t.
(* wccd - Coq code:22 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:23]] *)
Definition contract_init (ctx_0 : context_t): (context_t ∏ state_hacspec_t) :=
  (ctx_0, StateHacspec (seq_new_ (default) (usize 0))).
Definition Setup := unit.
Definition CIS1_wCCD_State (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : ResultMonad.result (
  context_t ∏
  state_hacspec_t
) unit :=
  ResultMonad.Ok (contract_init (Context (ctx.(ctx_from), ctx.(ctx_origin), repr ctx.(ctx_amount), 0 (* TODO *)))).
(* wccd - Coq code:23 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:24]] *)
Definition contract_wrap
  (ctx_1 : (context_t ∏ state_hacspec_t))
  (amount_2 : int64): (option ((context_t ∏ state_hacspec_t) ∏ list_action_t
    )) :=
  let '(Context ((owner_3, sender_4, balance_5, time_6)), state_7) :=
    ctx_1 in 
  let s_8 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_3, sender_4, balance_5, time_6)), state_7),
      s_8
    )).

Definition wrap (amount : int64) (st : State) :=
  contract_wrap st amount.
(* wccd - Coq code:24 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:25]] *)
Definition contract_unwrap
  (ctx_9 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_10, sender_11, balance_12, time_13)), state_14) :=
    ctx_9 in 
  let s_15 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_10, sender_11, balance_12, time_13)), state_14),
      s_15
    )).

Definition unwrap (st : State) :=
  contract_unwrap st.
(* wccd - Coq code:25 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:26]] *)
Definition contract_transfer
  (ctx_16 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_17, sender_18, balance_19, time_20)), state_21) :=
    ctx_16 in 
  let s_22 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_17, sender_18, balance_19, time_20)), state_21),
      s_22
    )).

Definition transfer (st : State) :=
  contract_transfer st.
(* wccd - Coq code:26 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:27]] *)
Definition contract_update_operator
  (ctx_23 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_24, sender_25, balance_26, time_27)), state_28) :=
    ctx_23 in 
  let s_29 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_24, sender_25, balance_26, time_27)), state_28),
      s_29
    )).

Definition updateOperator (st : State) :=
  contract_update_operator st.
(* wccd - Coq code:27 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:28]] *)
Definition contract_balance_of
  (ctx_30 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_31, sender_32, balance_33, time_34)), state_35) :=
    ctx_30 in 
  let s_36 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_31, sender_32, balance_33, time_34)), state_35),
      s_36
    )).

Definition balanceOf (st : State) :=
  contract_balance_of st.
(* wccd - Coq code:28 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:29]] *)
Definition contract_operator_of
  (ctx_37 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_38, sender_39, balance_40, time_41)), state_42) :=
    ctx_37 in 
  let s_43 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_38, sender_39, balance_40, time_41)), state_42),
      s_43
    )).

Definition operatorOf (st : State) :=
  contract_operator_of st.
(* wccd - Coq code:29 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:30]] *)
Definition contract_token_metadata
  (ctx_44 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_45, sender_46, balance_47, time_48)), state_49) :=
    ctx_44 in 
  let s_50 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_45, sender_46, balance_47, time_48)), state_49),
      s_50
    )).

Definition tokenMetadata (st : State) :=
  contract_token_metadata st.
(* wccd - Coq code:30 ends here *)

(* [[file:WCCD.org::*wccd - Coq code][wccd - Coq code:31]] *)
Inductive Msg :=
| WRAP
| UNWRAP
| TRANSFER
| UPDATEOPERATOR
| BALANCEOF
| OPERATOROF
| TOKENMETADATA.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<WRAP,UNWRAP,TRANSFER,UPDATEOPERATOR,BALANCEOF,OPERATOROF,TOKENMETADATA>.
Definition CIS1_wCCD_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : ResultMonad.result (State * list ActionBody) unit :=
  match msg with
  | Some WRAP => to_action_body_list ctx (wrap (repr ctx.(ctx_amount)) state)
  | Some UNWRAP => to_action_body_list ctx (unwrap state)
  | Some TRANSFER => to_action_body_list ctx (transfer state)
  | Some UPDATEOPERATOR => to_action_body_list ctx (updateOperator state)
  | Some BALANCEOF => to_action_body_list ctx (balanceOf state)
  | Some OPERATOROF => to_action_body_list ctx (operatorOf state)
  | Some TOKENMETADATA => to_action_body_list ctx (tokenMetadata state)
  | None => ResultMonad.Err tt
  end.

Definition CIS1_wCCD_contract : Contract Setup Msg State unit :=
  build_contract CIS1_wCCD_State CIS1_wCCD_receive.
(* wccd - Coq code:31 ends here *)
