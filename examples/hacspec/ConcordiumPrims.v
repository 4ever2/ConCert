(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:1]] *)

(** This file was automatically generated using Hacspec **)
From ConCert.Examples.Hacspec Require Import HacspecLib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

(* concordium_prims - Coq code:1 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:2]] *)
From ConCert.Examples.Hacspec Require Import HacspecLib.
Export HacspecLib.
(* concordium_prims - Coq code:2 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:3]] *)
Definition accept_hacspec : int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:3 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:4]] *)
Definition simple_transfer_hacspec
  (buf_0 : public_byte_seq)
  (amount_1 : int64): int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:4 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:5]] *)
Definition send_hacspec
  (addr_index_2 : int64)
  (addr_subindex_3 : int64)
  (receive_name_4 : public_byte_seq)
  (amount_5 : int64)
  (parameter_6 : public_byte_seq): int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:5 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:6]] *)
Definition combine_and_hacspec (l_7 : int32) (r_8 : int32): int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:6 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:7]] *)
Definition combine_or_hacspec (l_9 : int32) (r_10 : int32): int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:7 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:8]] *)
Definition get_parameter_size_hacspec : int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:8 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:9]] *)
Definition get_parameter_section_hacspec
  (buf_11 : public_byte_seq)
  (offset_12 : int32): (public_byte_seq ∏ int32) :=
  (buf_11, @repr WORDSIZE32 1).

(* concordium_prims - Coq code:9 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:10]] *)
Definition get_policy_section_hacspec
  (policy_bytes_13 : public_byte_seq)
  (offset_14 : int32): (public_byte_seq ∏ int32) :=
  (policy_bytes_13, @repr WORDSIZE32 1).

(* concordium_prims - Coq code:10 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:11]] *)
Definition log_event_hacspec
  (start_15 : public_byte_seq): (public_byte_seq ∏ int32) :=
  (start_15, @repr WORDSIZE32 1).

(* concordium_prims - Coq code:11 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:12]] *)
Definition load_state_hacspec
  (buf_16 : public_byte_seq)
  (offset_17 : int32): (public_byte_seq ∏ int32) :=
  (buf_16, @repr WORDSIZE32 1).

(* concordium_prims - Coq code:12 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:13]] *)
Definition write_state_hacspec
  (buf_18 : public_byte_seq)
  (offset_19 : int32): (public_byte_seq ∏ int32) :=
  (buf_18, @repr WORDSIZE32 1).

(* concordium_prims - Coq code:13 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:14]] *)
Definition resize_state_hacspec (new_size_20 : int32): int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:14 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:15]] *)
Definition state_size_hacspec : int32 :=
  @repr WORDSIZE32 1.

(* concordium_prims - Coq code:15 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:16]] *)
Definition get_init_origin_hacspec
  (start_21 : public_byte_seq): public_byte_seq :=
  start_21.

(* concordium_prims - Coq code:16 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:17]] *)
Definition get_receive_invoker_hacspec
  (start_22 : public_byte_seq): public_byte_seq :=
  start_22.

(* concordium_prims - Coq code:17 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:18]] *)
Definition get_receive_self_address_hacspec
  (start_23 : public_byte_seq): public_byte_seq :=
  start_23.

(* concordium_prims - Coq code:18 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:19]] *)
Definition get_receive_self_balance_hacspec : int64 :=
  @repr WORDSIZE64 1.

(* concordium_prims - Coq code:19 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:20]] *)
Definition get_receive_sender_hacspec
  (start_24 : public_byte_seq): public_byte_seq :=
  start_24.

(* concordium_prims - Coq code:20 ends here *)

(* [[file:concordium.org::* concordium_prims - Coq code][concordium_prims - Coq code:21]] *)
Definition get_slot_time_hacspec : int64 :=
  @repr WORDSIZE64 1.

(* concordium_prims - Coq code:21 ends here *)

