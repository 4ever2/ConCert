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

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:5]] *)
Inductive piggy_bank_state_hacspec_t :=
| Intact : piggy_bank_state_hacspec_t
| Smashed : piggy_bank_state_hacspec_t.
Global Instance serializable_piggy_bank_state_hacspec_t : Serializable piggy_bank_state_hacspec_t :=
  Derive Serializable piggy_bank_state_hacspec_t_rect<Intact,Smashed>.


Definition eqb_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : bool :=
match x with
   | Intact => match y with | Intact=> true | _ => false end
   | Smashed => match y with | Smashed=> true | _ => false end
   end.

Definition eqb_leibniz_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : eqb_piggy_bank_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_piggy_bank_state_hacspec_t : EqDec (piggy_bank_state_hacspec_t) :=
  Build_EqDec (piggy_bank_state_hacspec_t) (eqb_piggy_bank_state_hacspec_t) (eqb_leibniz_piggy_bank_state_hacspec_t).


Definition State := context_t ∏ piggy_bank_state_hacspec_t.

(* piggybank - Coq code:5 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:6]] *)
Definition piggy_init_hacspec : piggy_bank_state_hacspec_t :=
  Intact.

(* piggybank - Coq code:6 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:7]] *)
Definition piggy_init
  (ctx_0 : context_t): (context_t ∏ piggy_bank_state_hacspec_t) :=
  (ctx_0, piggy_init_hacspec ).
Definition Setup := unit.
Definition PiggyBank_State (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : ResultMonad.result (
  context_t ∏
  piggy_bank_state_hacspec_t
) unit :=
  ResultMonad.Ok (piggy_init (Context (ctx.(ctx_from), ctx.(ctx_origin), repr ctx.(ctx_amount), 0 (* TODO *)))).

(* piggybank - Coq code:7 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:8]] *)
Notation "'piggy_insert_result_t'" := ((result unit unit)) : hacspec_scope.
(* piggybank - Coq code:8 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:9]] *)
Definition piggy_insert_hacspec
  (ctx_1 : context_t)
  (amount_2 : int64)
  (state_3 : piggy_bank_state_hacspec_t): piggy_insert_result_t :=
  match state_3 with
  | Intact => @Ok unit unit (tt)
  | Smashed => @Err unit unit (tt)
  end.

(* piggybank - Coq code:9 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:10]] *)
Definition piggy_insert
  (ctx_state_4 : (context_t ∏ piggy_bank_state_hacspec_t))
  (amount_5 : int64): (option (
      (context_t ∏ piggy_bank_state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(ctx_6, state_7) :=
    ctx_state_4 in 
  let 'Context ((a_8, c_9, balance_10, d_11)) :=
    ctx_6 in 
  let _ : int32 :=
    accept_hacspec  in 
  let temp_12 : (result unit unit) :=
    piggy_insert_hacspec (ctx_6) (amount_5) (state_7) in 
  bind (match temp_12 with
    | Ok _ => @Some unit (tt)
    | Err _ => @None unit
    end) (fun _ =>  let s_13 : seq has_action_t :=
      seq_new_ (default) (usize 0) in 
    let s_13 :=
      seq_upd s_13 (usize 0) (accept_action ) in 
    @Some ((context_t ∏ piggy_bank_state_hacspec_t) ∏ list_action_t) ((
        (Context ((a_8, c_9, (balance_10) .+ (amount_5), d_11)), state_7),
        s_13
      ))).

Definition insert (amount : int64) (st : State) :=
  piggy_insert st amount.

(* piggybank - Coq code:10 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:11]] *)
Inductive smash_error_t :=
| NotOwner : smash_error_t
| AlreadySmashed : smash_error_t.

Definition eqb_smash_error_t (x y : smash_error_t) : bool :=
match x with
   | NotOwner => match y with | NotOwner=> true | _ => false end
   | AlreadySmashed => match y with | AlreadySmashed=> true | _ => false end
   end.

Definition eqb_leibniz_smash_error_t (x y : smash_error_t) : eqb_smash_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_smash_error_t : EqDec (smash_error_t) :=
  Build_EqDec (smash_error_t) (eqb_smash_error_t) (eqb_leibniz_smash_error_t).

Global Instance show_smash_error_t : Show (smash_error_t) :=
 @Build_Show (smash_error_t) (fun x =>
 match x with
 NotOwner => ("NotOwner")%string
 | AlreadySmashed => ("AlreadySmashed")%string
 end).
Definition g_smash_error_t : G (smash_error_t) := oneOf_ (returnGen NotOwner) [returnGen NotOwner;returnGen AlreadySmashed].
Global Instance gen_smash_error_t : Gen (smash_error_t) := Build_Gen smash_error_t g_smash_error_t.

(* piggybank - Coq code:11 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:12]] *)
Notation "'piggy_smash_result_t'" := ((
    result piggy_bank_state_hacspec_t smash_error_t)) : hacspec_scope.
(* piggybank - Coq code:12 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:13]] *)
Definition piggy_smash_hacspec
  (from : user_address_t)
  (ctx_14 : context_t)
  (state_15 : piggy_bank_state_hacspec_t): piggy_smash_result_t :=
  let 'Context ((owner_16, sender_17, balance_18, metadata_19)) :=
    ctx_14 in 
  ifbnd (negb ((owner_16) array_eq (from))) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (negb ((state_15) =.? (Intact))) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (
        AlreadySmashed)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed))).

(* piggybank - Coq code:13 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:14]] *)
Definition piggy_smash (from : user_address_t) (amount : int64)
  (ctx_state_20 : (context_t ∏ piggy_bank_state_hacspec_t)): (option (
      (context_t ∏ piggy_bank_state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(ctx_21, state_22) :=
    ctx_state_20 in 
  let 'Context ((a_23, c_24, balance_25, d_26)) :=
    ctx_21 in 
  let _ : int32 :=
    accept_hacspec  in 
  let smash_27 : (result piggy_bank_state_hacspec_t smash_error_t) :=
    piggy_smash_hacspec from (ctx_21) (state_22) in 
  bind (match smash_27 with
    | Ok a_28 => @Some piggy_bank_state_hacspec_t (a_28)
    | Err b_29 => @None piggy_bank_state_hacspec_t
    end) (fun new_state_30 =>  let s_31 : seq has_action_t :=
      seq_new_ (SimpleTransfer (a_23, balance_25 .+ amount)) 1 in
    @Some ((context_t ∏ piggy_bank_state_hacspec_t) ∏ list_action_t) ((
        (Context ((a_23, c_24, @repr WORDSIZE64 0, d_26)), new_state_30),
        s_31
      ))).

Definition smash (from : user_address_t) (amount : int64) (st : State) :=
  piggy_smash from amount st.

(* piggybank - Coq code:14 ends here *)

(* [[file:piggybank.org::* piggybank - Coq code][piggybank - Coq code:21]] *)
Inductive Msg :=
| INSERT
| SMASH.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<INSERT,SMASH>.
Definition PiggyBank_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : ResultMonad.result (State * list ActionBody) unit :=
  to_action_body_list ctx (match msg with
    | Some INSERT => (insert (repr ctx.(ctx_amount)) state)
    | Some SMASH => (smash ctx.(ctx_from) (repr ctx.(ctx_amount)) state)
    | None => None
    end).

Definition PiggyBank_contract : Contract Setup Msg State unit :=
  build_contract PiggyBank_State PiggyBank_receive.

(* piggybank - Coq code:21 ends here *)