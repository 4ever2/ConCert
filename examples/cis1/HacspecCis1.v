(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:1]] *)

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
(* cis1 - Coq code:1 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:2]] *)
From ConCert.Examples.Hacspec Require Import HacspecLib.
Export HacspecLib.
(* cis1 - Coq code:2 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:3]] *)
From ConCert.Examples.Hacspec Require Import HacspecConcordium.
Export HacspecConcordium.
(* cis1 - Coq code:3 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:4]] *)
From ConCert.Examples.Hacspec Require Import ConCertLib.
Export ConCertLib.
(* cis1 - Coq code:4 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:5]] *)
Definition transfer_event_tag_v : int8 :=
  @repr WORDSIZE8 255.
(* cis1 - Coq code:5 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:6]] *)
Definition mint_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 1).
(* cis1 - Coq code:6 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:7]] *)
Definition burn_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 2).
(* cis1 - Coq code:7 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:8]] *)
Definition update_operator_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 3).
(* cis1 - Coq code:8 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:9]] *)
Definition token_metadata_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 4).
(* cis1 - Coq code:9 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:10]] *)
Definition sha256_t := nseq (int8) (usize 32).
(* cis1 - Coq code:10 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:11]] *)
Inductive metadata_url_t :=
| MetadataUrl : (string_t ∏ (option sha256_t)) -> metadata_url_t.

(* cis1 - Coq code:11 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:12]] *)
Inductive token_id_vec_t :=
| TokenIdVec : public_byte_seq -> token_id_vec_t.

(* cis1 - Coq code:12 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:13]] *)
Inductive token_id_uint32_t :=
| TokenIdU32 : int32 -> token_id_uint32_t.

(* cis1 - Coq code:13 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:14]] *)
Inductive token_id_uint16_t :=
| TokenIdU16 : int16 -> token_id_uint16_t.

(* cis1 - Coq code:14 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:15]] *)
Inductive token_id_uint8_t :=
| TokenIdU8 : int8 -> token_id_uint8_t.

(* cis1 - Coq code:15 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:16]] *)
Inductive token_id_unit_t :=
| TokenIdUnit : unit -> token_id_unit_t.

(* cis1 - Coq code:16 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:17]] *)
Notation "'token_amount_t'" := (int64) : hacspec_scope.
(* cis1 - Coq code:17 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:18]] *)
Inductive operator_update_t :=
| Remove : operator_update_t
| Add : operator_update_t.

(* cis1 - Coq code:18 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:19]] *)
Inductive update_operator_event_t :=
| UpdateOperatorEvent : (operator_update_t ∏ user_address_t ∏ user_address_t
) -> update_operator_event_t.

(* cis1 - Coq code:19 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:20]] *)
Inductive receiver_hacspec_t :=
| Account : public_byte_seq -> receiver_hacspec_t
| Contract : (public_byte_seq ∏ string_t) -> receiver_hacspec_t.
Global Instance serializable_receiver_hacspec_t : Serializable receiver_hacspec_t :=
  Derive Serializable receiver_hacspec_t_rect<Account,Contract>.

(* cis1 - Coq code:20 ends here *)

(* [[file:WCCD.org::* cis1 - Coq code][cis1 - Coq code:21]] *)
Inductive additional_data_hacspec_t :=
| AdditionalDataHacspec : seq int8 -> additional_data_hacspec_t.
Global Instance serializable_additional_data_hacspec_t : Serializable additional_data_hacspec_t :=
  Derive Serializable additional_data_hacspec_t_rect<AdditionalDataHacspec>.

(* cis1 - Coq code:21 ends here *)

