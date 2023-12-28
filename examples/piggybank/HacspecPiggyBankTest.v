From ConCert.Examples.PiggyBank Require Import HacspecPiggyBank.
(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:1]] *)

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
(* piggybank - Coq code:1 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:2]] *)
From ConCert.Examples.Hacspec Require Import HacspecLib.
Export HacspecLib.
(* piggybank - Coq code:2 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:3]] *)
From ConCert.Examples.Hacspec Require Import HacspecConcordium.
Export HacspecConcordium.
(* piggybank - Coq code:3 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:4]] *)
From ConCert.Examples.Hacspec Require Import ConCertLib.
Export ConCertLib.
(* piggybank - Coq code:4 ends here *)



Global Instance show_piggy_bank_state_hacspec_t : Show (piggy_bank_state_hacspec_t) :=
 @Build_Show (piggy_bank_state_hacspec_t) (fun x =>
 match x with
 Intact => ("Intact")%string
 | Smashed => ("Smashed")%string
 end).
Definition g_piggy_bank_state_hacspec_t : G (piggy_bank_state_hacspec_t) := oneOf_ (returnGen Intact) [returnGen Intact;returnGen Smashed].
Global Instance gen_piggy_bank_state_hacspec_t : Gen (piggy_bank_state_hacspec_t) := Build_Gen piggy_bank_state_hacspec_t g_piggy_bank_state_hacspec_t.


(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:15]] *)
Definition test_init_hacspec : bool :=
  (piggy_init_hacspec ) =.? (Intact).

(* piggybank - Coq code:15 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:16]] *)
Definition test_insert_intact (ctx_32 : context_t) (amount_33 : int64): bool :=
  (piggy_insert_hacspec (ctx_32) (amount_33) (Intact)) =.? (@Ok unit unit (tt)).

(* QuickChick (forAll g_context_t (fun ctx_32 : context_t =>
  forAll g_int64 (fun amount_33 : int64 =>
  test_insert_intact ctx_32 amount_33))). *)
(* piggybank - Coq code:16 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:17]] *)
Definition test_insert_smashed (ctx_34 : context_t) (amount_35 : int64): bool :=
  (piggy_insert_hacspec (ctx_34) (amount_35) (Smashed)) =.? (@Err unit unit (
      tt)).

(* QuickChick (forAll g_context_t (fun ctx_34 : context_t =>
  forAll g_int64 (fun amount_35 : int64 =>
  test_insert_smashed ctx_34 amount_35))). *)
(* piggybank - Coq code:17 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:18]] *)
Definition test_smash_intact
  (owner_36 : user_address_t)
  (balance_37 : int64)
  (metadata_38 : int64): bool :=
  let sender_39 : user_address_t :=
    owner_36 in 
  let ctx_40 : context_t :=
    Context ((owner_36, sender_39, balance_37, metadata_38)) in 
  (piggy_smash_hacspec (sender_39) (ctx_40) (Intact)) =.? (
    @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed)).

(* QuickChick (forAll g_user_address_t (fun owner_36 : user_address_t =>
  forAll g_int64 (fun balance_37 : int64 =>
  forAll g_int64 (fun metadata_38 : int64 =>
  test_smash_intact owner_36 balance_37 metadata_38)))). *)
(* piggybank - Coq code:18 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:19]] *)
Definition test_smash_intact_not_owner
  (owner_41 : user_address_t)
  (sender_42 : user_address_t)
  (balance_43 : int64)
  (metadata_44 : int64): bool :=
  let ctx_45 : context_t :=
    Context ((owner_41, sender_42, balance_43, metadata_44)) in 
  ((owner_41) array_eq (sender_42)) || ((piggy_smash_hacspec (sender_42) (ctx_45) (
        Intact)) =.? (@Err piggy_bank_state_hacspec_t smash_error_t (
        NotOwner))).

(* QuickChick (forAll g_user_address_t (fun owner_41 : user_address_t =>
  forAll g_user_address_t (fun sender_42 : user_address_t =>
  forAll g_int64 (fun balance_43 : int64 =>
  forAll g_int64 (fun metadata_44 : int64 =>
  test_smash_intact_not_owner owner_41 sender_42 balance_43 metadata_44))))). *)
(* piggybank - Coq code:19 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:20]] *)
Definition test_smash_smashed
  (owner_46 : user_address_t)
  (balance_47 : int64)
  (metadata_48 : int64): bool :=
  let sender_49 : user_address_t :=
    owner_46 in 
  let ctx_50 : context_t :=
    Context ((owner_46, sender_49, balance_47, metadata_48)) in 
  (piggy_smash_hacspec (sender_49) (ctx_50) (Smashed)) =.? (
    @Err piggy_bank_state_hacspec_t smash_error_t (AlreadySmashed)).

(* QuickChick (forAll g_user_address_t (fun owner_46 : user_address_t =>
  forAll g_int64 (fun balance_47 : int64 =>
  forAll g_int64 (fun metadata_48 : int64 =>
  test_smash_smashed owner_46 balance_47 metadata_48)))). *)
(* piggybank - Coq code:20 ends here *)