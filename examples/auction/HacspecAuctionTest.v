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

From ConCert.Examples.Auction Require Import HacspecAuction.

Global Instance show_auction_state_hacspec_t : Show (auction_state_hacspec_t) :=
 @Build_Show (auction_state_hacspec_t) (fun x =>
 match x with
 NotSoldYet => ("NotSoldYet")%string
 | Sold a => ("Sold" ++ show a)%string
 end).
Definition g_auction_state_hacspec_t : G (auction_state_hacspec_t) := oneOf_ (returnGen NotSoldYet) [returnGen NotSoldYet;bindGen arbitrary (fun a => returnGen (Sold a))].
Global Instance gen_auction_state_hacspec_t : Gen (auction_state_hacspec_t) := Build_Gen auction_state_hacspec_t g_auction_state_hacspec_t.

Global Instance show_seq_map_t : Show (seq_map_t) :=
 @Build_Show (seq_map_t) (fun x =>
 match x with
 SeqMap a => ("SeqMap" ++ show a)%string
 end).
Definition g_seq_map_t : G (seq_map_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (SeqMap a))) [bindGen arbitrary (fun a => returnGen (SeqMap a))].
Global Instance gen_seq_map_t : Gen (seq_map_t) := Build_Gen seq_map_t g_seq_map_t.

Global Instance show_state_hacspec_t : Show (state_hacspec_t) :=
 @Build_Show (state_hacspec_t) (fun x =>
 match x with
 StateHacspec a => ("StateHacspec" ++ show a)%string
 end).
Definition g_state_hacspec_t : G (state_hacspec_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (StateHacspec a))) [bindGen arbitrary (fun a => returnGen (StateHacspec a))].
Global Instance gen_state_hacspec_t : Gen (state_hacspec_t) := Build_Gen state_hacspec_t g_state_hacspec_t.

Global Instance show_init_parameter_t : Show (init_parameter_t) :=
 @Build_Show (init_parameter_t) (fun x =>
 match x with
 InitParameter a => ("InitParameter" ++ show a)%string
 end).
Definition g_init_parameter_t : G (init_parameter_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (InitParameter a))) [bindGen arbitrary (fun a => returnGen (InitParameter a))].
Global Instance gen_init_parameter_t : Gen (init_parameter_t) := Build_Gen init_parameter_t g_init_parameter_t.


Global Instance show_context_state_hacspec_t : Show (context_state_hacspec_t) :=
Build_Show context_state_hacspec_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_context_state_hacspec_t : G (context_state_hacspec_t) :=
bindGen arbitrary (fun x0 : context_t =>
  bindGen arbitrary (fun x1 : state_hacspec_t =>
  returnGen (x0,x1))).
Global Instance gen_context_state_hacspec_t : Gen (context_state_hacspec_t) := Build_Gen context_state_hacspec_t g_context_state_hacspec_t.

Global Instance show_map_update_t : Show (map_update_t) :=
 @Build_Show (map_update_t) (fun x =>
 match x with
 Update a => ("Update" ++ show a)%string
 end).
Definition g_map_update_t : G (map_update_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (Update a))) [bindGen arbitrary (fun a => returnGen (Update a))].
Global Instance gen_map_update_t : Gen (map_update_t) := Build_Gen map_update_t g_map_update_t.

Global Instance show_bid_error_hacspec_t : Show (bid_error_hacspec_t) :=
 @Build_Show (bid_error_hacspec_t) (fun x =>
 match x with
 ContractSender => ("ContractSender")%string
 | BidTooLow => ("BidTooLow")%string
 | BidsOverWaitingForAuctionFinalization => (
   "BidsOverWaitingForAuctionFinalization")%string
 | AuctionIsFinalized => ("AuctionIsFinalized")%string
 end).
Definition g_bid_error_hacspec_t : G (bid_error_hacspec_t) := oneOf_ (returnGen ContractSender) [returnGen ContractSender;returnGen BidTooLow;returnGen BidsOverWaitingForAuctionFinalization;returnGen AuctionIsFinalized].
Global Instance gen_bid_error_hacspec_t : Gen (bid_error_hacspec_t) := Build_Gen bid_error_hacspec_t g_bid_error_hacspec_t.

Global Instance show_finalize_error_hacspec_t : Show (finalize_error_hacspec_t) :=
 @Build_Show (finalize_error_hacspec_t) (fun x =>
 match x with
 BidMapError => ("BidMapError")%string
 | AuctionStillActive => ("AuctionStillActive")%string
 | AuctionFinalized => ("AuctionFinalized")%string
 end).
Definition g_finalize_error_hacspec_t : G (finalize_error_hacspec_t) := oneOf_ (returnGen BidMapError) [returnGen BidMapError;returnGen AuctionStillActive;returnGen AuctionFinalized].
Global Instance gen_finalize_error_hacspec_t : Gen (finalize_error_hacspec_t) := Build_Gen finalize_error_hacspec_t g_finalize_error_hacspec_t.

Global Instance show_finalize_context_t : Show (finalize_context_t) :=
Build_Show finalize_context_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_finalize_context_t : G (finalize_context_t) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address_t =>
  bindGen arbitrary (fun x2 : int64 =>
  returnGen (x0,x1,x2)))).
Global Instance gen_finalize_context_t : Gen (finalize_context_t) := Build_Gen finalize_context_t g_finalize_context_t.

Global Instance show_finalize_action_t : Show (finalize_action_t) :=
 @Build_Show (finalize_action_t) (fun x =>
 match x with
 Accept => ("Accept")%string
 | SimpleTransfer a => ("SimpleTransfer" ++ show a)%string
 end).
Definition g_finalize_action_t : G (finalize_action_t) := oneOf_ (returnGen Accept) [returnGen Accept;bindGen arbitrary (fun a => returnGen (SimpleTransfer a))].
Global Instance gen_finalize_action_t : Gen (finalize_action_t) := Build_Gen finalize_action_t g_finalize_action_t.

Global Instance show_bid_remain_t : Show (bid_remain_t) :=
 @Build_Show (bid_remain_t) (fun x =>
 match x with
 BidNone => ("BidNone")%string
 | BidSome a => ("BidSome" ++ show a)%string
 end).
Definition g_bid_remain_t : G (bid_remain_t) := oneOf_ (returnGen BidNone) [returnGen BidNone;bindGen arbitrary (fun a => returnGen (BidSome a))].
Global Instance gen_bid_remain_t : Gen (bid_remain_t) := Build_Gen bid_remain_t g_bid_remain_t.

(* [[file:auction.org::* auction - Coq code][auction - Coq code:26]] *)
Definition auction_test_init
  (item_59 : public_byte_seq)
  (time_60 : int64): bool :=
  (fresh_state_hacspec ((item_59)) (time_60)) =.? (StateHacspec ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_59),
        time_60,
        SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0)))
      ))).


Theorem ensures_auction_test_init : forall result_61 (
  item_59 : public_byte_seq) (time_60 : int64),
 @auction_test_init item_59 time_60 = result_61 ->
 (result_61) =.? (true).
 Proof. Admitted.
(* QuickChick (forAll g_public_byte_seq (fun item_59 : public_byte_seq =>
  forAll g_int64 (fun time_60 : int64 =>
  auction_test_init item_59 time_60))). *)
(* auction - Coq code:26 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:27]] *)
Definition verify_bid
  (item_62 : public_byte_seq)
  (state_63 : state_hacspec_t)
  (account_64 : user_address_t)
  (ctx_65 : context_t)
  (amount_66 : int64)
  (bid_map_67 : seq_map_t)
  (highest_bid_68 : int64)
  (time_69 : int64): (state_hacspec_t ∏ seq_map_t ∏ bool ∏ bool) :=
  let t_70 : (result state_hacspec_t bid_error_hacspec_t) :=
    auction_bid_hacspec (ctx_65) (amount_66) ((state_63)) in 
  let '(state_71, res_72) :=
    match t_70 with
    | Err e_73 => (state_63, false)
    | Ok s_74 => (s_74, true)
    end in 
  let bid_map_75 : seq_map_t :=
    match seq_map_update_entry ((bid_map_67)) (account_64) (highest_bid_68) with
    | Update (_, updated_map_76) => updated_map_76
    end in 
  (
    (state_71),
    (bid_map_75),
    res_72,
    ((state_71)) =.? (StateHacspec ((
          NotSoldYet,
          highest_bid_68,
          (item_62),
          time_69,
          (bid_map_75)
        )))
  ).

(* auction - Coq code:27 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:28]] *)
Definition useraddress_from_u8 (i_77 : int8): user_address_t :=
  array_from_list int8 (let l :=
      [
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77;
        i_77
      ] in  l).

(* auction - Coq code:28 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:29]] *)
Definition new_account
  (time_78 : int64)
  (i_79 : int8): (user_address_t ∏ context_t) :=
  let addr_80 : user_address_t :=
    useraddress_from_u8 (i_79) in 
  let ctx_81 : context_t :=
    Context ((addr_80, addr_80, @repr WORDSIZE64 0, time_78)) in 
  (addr_80, ctx_81).

(* auction - Coq code:29 ends here *)

(* [[file:auction.org::* auction - Coq code][auction - Coq code:30]] *)
Definition test_auction_bid_and_finalize
  (item_82 : public_byte_seq)
  (time_83 : int64)
  (input_amount_84 : int64): bool :=
  let time_85 : int64 :=
    (if ((time_83) =.? (@repr WORDSIZE64 18446744073709551615)):bool then (
        @repr WORDSIZE64 18446744073709551614) else (time_83)) in 
  let input_amount_86 : int64 :=
    (if ((input_amount_84) >.? (((@repr WORDSIZE64 18446744073709551615) ./ (
              @repr WORDSIZE64 5)) .- (@repr WORDSIZE64 1))):bool then (
        @repr WORDSIZE64 100) else (input_amount_84)) in 
  let amount_87 : int64 :=
    (input_amount_86) .+ (@repr WORDSIZE64 1) in 
  let winning_amount_88 : int64 :=
    (amount_87) .* (@repr WORDSIZE64 3) in 
  let big_amount_89 : int64 :=
    (amount_87) .* (@repr WORDSIZE64 5) in 
  let bid_map_90 : seq_map_t :=
    SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0))) in 
  let state_91 : state_hacspec_t :=
    fresh_state_hacspec ((item_82)) (time_85) in 
  let '(alice_92, alice_ctx_93) :=
    new_account (time_85) (@repr WORDSIZE8 0) in 
  let 'Context ((_, ac0_94, _, ac1_95)) :=
    alice_ctx_93 in 
  let '(state_96, bid_map_97, res_0_98, result_0_99) :=
    verify_bid ((item_82)) (state_91) (alice_92) (alice_ctx_93) (amount_87) (
      bid_map_90) (amount_87) (time_85) in 
  let '(state_100, bid_map_101, res_1_102, result_1_103) :=
    verify_bid ((item_82)) (state_96) (alice_92) (alice_ctx_93) (amount_87) (
      bid_map_97) ((amount_87) .+ (amount_87)) (time_85) in 
  let '(bob_104, bob_ctx_105) :=
    new_account (time_85) (@repr WORDSIZE8 1) in 
  let 'Context ((_, bc1_106, _, bc2_107)) :=
    bob_ctx_105 in 
  let '(state_108, bid_map_109, res_2_110, result_2_111) :=
    verify_bid ((item_82)) (state_100) (bob_104) (bob_ctx_105) (
      winning_amount_88) (bid_map_101) (winning_amount_88) (time_85) in 
  let owner_112 : user_address_t :=
    useraddress_from_u8 (@repr WORDSIZE8 0) in 
  let balance_113 : int64 :=
    @repr WORDSIZE64 100 in 
  let ctx4_114 : (int64 ∏ user_address_t ∏ int64) :=
    (time_85, owner_112, balance_113) in 
  let finres_115 : (result (state_hacspec_t ∏ finalize_action_t
      ) finalize_error_hacspec_t) :=
    auction_finalize_hacspec (ctx4_114) ((state_108)) in 
  let '(state_116, result_3_117) :=
    match finres_115 with
    | Err err_118 => ((state_108), (err_118) =.? (AuctionStillActive))
    | Ok (state_119, _) => (state_119, false)
    end in 
  let '(carol_120, carol_ctx_121) :=
    new_account (time_85) (@repr WORDSIZE8 2) in 
  let ctx5_122 : (int64 ∏ user_address_t ∏ int64) :=
    ((time_85) .+ (@repr WORDSIZE64 1), carol_120, winning_amount_88) in 
  let finres2_123 : (result (state_hacspec_t ∏ finalize_action_t
      ) finalize_error_hacspec_t) :=
    auction_finalize_hacspec (ctx5_122) ((state_116)) in 
  let '(state_124, result_4_125) :=
    match finres2_123 with
    | Err _ => ((state_116), false)
    | Ok (state_126, action_127) => (
      state_126,
      (action_127) =.? (SimpleTransfer (seq_concat (seq_concat (seq_concat (
                seq_concat (seq_new_ (default) (usize 0)) (
                  array_to_seq (carol_120))) (array_to_seq (u64_to_be_bytes (
                  winning_amount_88)))) (array_to_seq (alice_92))) (
            array_to_seq (u64_to_be_bytes ((amount_87) .+ (amount_87))))))
    )
    end in 
  let result_5_128 : bool :=
    ((state_124)) =.? (StateHacspec ((
          Sold (bob_104),
          winning_amount_88,
          (item_82),
          time_85,
          (bid_map_109)
        ))) in 
  let finres3_129 : (result (state_hacspec_t ∏ finalize_action_t
      ) finalize_error_hacspec_t) :=
    auction_finalize_hacspec (ctx5_122) ((state_124)) in 
  let '(state_130, result_6_131) :=
    match finres3_129 with
    | Err err_132 => (state_124, (err_132) =.? (AuctionFinalized))
    | Ok (state_133, action_134) => (state_133, false)
    end in 
  let t_135 : (result state_hacspec_t bid_error_hacspec_t) :=
    auction_bid_hacspec (bob_ctx_105) (big_amount_89) ((state_130)) in 
  let result_7_136 : bool :=
    match t_135 with
    | Err e_137 => (e_137) =.? (AuctionIsFinalized)
    | Ok _ => false
    end in 
  (((((((result_0_99) && (result_1_103)) && (result_2_111)) && (
            result_3_117)) && (result_4_125)) && (result_5_128)) && (
      result_6_131)) && (result_7_136).


Theorem ensures_test_auction_bid_and_finalize : forall result_61 (
  item_82 : public_byte_seq) (time_83 : int64) (input_amount_84 : int64),
 @test_auction_bid_and_finalize item_82 time_83 input_amount_84 = result_61 ->
 (result_61) =.? (true).
 Proof. Admitted.
(* QuickChick (forAll g_public_byte_seq (fun item_82 : public_byte_seq =>
  forAll g_int64 (fun time_83 : int64 =>
  forAll g_int64 (fun input_amount_84 : int64 =>
  test_auction_bid_and_finalize item_82 time_83 input_amount_84)))). *)
(* auction - Coq code:30 ends here *)
