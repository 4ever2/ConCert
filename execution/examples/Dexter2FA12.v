From Coq Require Import ZArith Bool.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Import ListNotations.
Import RecordSetNotations.

Section LQTFA12.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(* Dummy implementation of callbacks. *)
Record callback (A : Type) := {
  blob : option A;
}.

Record transfer_param :=
  build_transfer_param{
    from : Address;
    to : Address;
    value : N
}.

Record approve_param :=
  build_approve_param{
    spender : Address;
    value_ : N
}.

Record mintOrBurn_param :=
  build_mintOrBurn_param{
    quantity : Z;
    target : Address
}.

Record getAllowance_param :=
  build_getAllowance_param{
    request : (Address * Address);
    allowance_callbak : callback N
}.

Record getBalance_param :=
  build_getBalance_param{
    owner_ : Address;
    balance_callbak : callback N
}.

Record getTotalSupply_param :=
  build_getTotalSupply_param{
    request_ : unit;
    supply_callbak : callback N
}.

Record State :=
  build_state {
    tokens : FMap Address N;
    allowances : FMap (Address * Address) N;
    admin : Address;
    total_supply : N
}.

Record Setup :=
  build_setup {
    admin_ : Address
}.

(* Any contract that wants to receive callback messages from the FA1.2 liquidity contract
   should have this type as its Msg type. The contract may have other endpoints,
   as composed in the 'other_msg' constructor. *)
Inductive FA12ReceiverMsg {Msg' : Type} `{Serializable Msg'} :=
  | receive_allowance : N ->  FA12ReceiverMsg
  | receive_balance_of : N -> FA12ReceiverMsg
  | receive_total_supply : N -> FA12ReceiverMsg
  | other_msg : Msg' -> FA12ReceiverMsg.

(* Liquidity FA1.2 Endpoints. *)
Inductive Msg :=
  | msg_transfer : transfer_param -> Msg
  | msg_approve : approve_param -> Msg
  | msg_mint_or_burn : mintOrBurn_param -> Msg
  | msg_get_allowance : getAllowance_param -> Msg
  | msg_get_balance : getBalance_param -> Msg
  | msg_get_total_supply : getTotalSupply_param -> Msg.

MetaCoq Run (make_setters transfer_param).
MetaCoq Run (make_setters approve_param).
MetaCoq Run (make_setters mintOrBurn_param).
MetaCoq Run (make_setters getAllowance_param).
MetaCoq Run (make_setters getBalance_param).
MetaCoq Run (make_setters getTotalSupply_param).
MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Setup).

Section Serialization.

Instance callback_serializable {A : Type} `{serA : Serializable A} : Serializable (callback A) :=
Derive Serializable (callback_rect A) <(Build_callback A)>.

Global Instance transfer_param_serializable : Serializable transfer_param :=
  Derive Serializable transfer_param_rect <build_transfer_param>.

Global Instance approve_param_serializable : Serializable approve_param :=
  Derive Serializable approve_param_rect <build_approve_param>.

Global Instance mintOrBurn_param_serializable : Serializable mintOrBurn_param :=
  Derive Serializable mintOrBurn_param_rect <build_mintOrBurn_param>.

Global Instance getAllowance_param_serializable : Serializable getAllowance_param :=
  Derive Serializable getAllowance_param_rect <build_getAllowance_param>.

Global Instance getBalance_param_serializable : Serializable getBalance_param :=
  Derive Serializable getBalance_param_rect <build_getBalance_param>.

Global Instance getTotalSupply_param_serializable : Serializable getTotalSupply_param :=
  Derive Serializable getTotalSupply_param_rect <build_getTotalSupply_param>.

Global Instance FA12ReceiverMsg_serializable {Msg : Type} `{serMsg : Serializable Msg} : Serializable (@FA12ReceiverMsg Msg serMsg) :=
  Derive Serializable (@FA12ReceiverMsg_rect Msg serMsg) <
    (@receive_allowance Msg serMsg),
    (@receive_balance_of Msg serMsg),
    (@receive_total_supply Msg serMsg),
    (@other_msg Msg serMsg)>.

Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <msg_transfer,
                                msg_approve,
                                msg_mint_or_burn,
                                msg_get_allowance,
                                msg_get_balance,
                                msg_get_total_supply>.

Global Instance state_serializable : Serializable State :=
  Derive Serializable State_rect <build_state>.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

End Serialization.

Definition returnIf (cond : bool) := if cond then None else Some tt.

(* Transfers <amount> tokens, if <from> has enough tokens to transfer
    and <sender> is allowed to send that much on behalf of <from> *)
Definition try_transfer (sender : Address) (param : transfer_param) (state : State) : option State :=
  let allowances_ := state.(allowances) in
  let tokens_ := state.(tokens) in
  do allowances_ <- (* Update allowances *)
    (if address_eqb sender param.(from)
    then Some allowances_
    else
      let allowance_key := (param.(from), sender) in
      let authorized_value := with_default 0 (FMap.find allowance_key allowances_) in
        do _ <- returnIf (authorized_value <? param.(value)) ; (* NotEnoughAllowance *)
        Some (FMap.add allowance_key (authorized_value - param.(value)) allowances_)
    ) ;
  do tokens_ <- (* Update from balance *)
    (let from_balance := with_default 0 (FMap.find param.(from) tokens_) in
      do _ <- returnIf (from_balance <? param.(value)) ; (* NotEnoughBalance *)
      Some (FMap.add param.(from) (from_balance - param.(value)) tokens_)
    ) ;
  let tokens_ :=
    let to_balance := with_default 0 (FMap.find param.(to) tokens_) in
      FMap.add param.(to) (to_balance + param.(value)) tokens_ in
    Some (state<|tokens := tokens_|>
               <|allowances := allowances_|>).

(* The caller approves the <spender> to transfer up to <amount> tokens on behalf of the <sender> *)
Definition try_approve (sender : Address) (param : approve_param) (state : State) : option State :=
  let allowances_ := state.(allowances) in
  let allowance_key := (sender, param.(spender)) in
  let previous_value := with_default 0 (FMap.find allowance_key allowances_) in
  do _ <- returnIf (andb (0 <? previous_value) (0 <? param.(value_))) ; (* UnsafeAllowanceChange *)
  let allowances_ := FMap.add allowance_key param.(value_) allowances_ in
    Some (state<|allowances := allowances_|>).

(* If <quantitiy> is positive
   then creates <quantity> tokens and gives them to <target> 
   else removes <quantity> tokens from <target>.
   Can only be called by <admin> *)
Definition try_mint_or_burn (sender : Address) (param : mintOrBurn_param) (state : State) : option State :=
  do _ <- returnIf (negb (address_eqb sender state.(admin))) ;
  let tokens_ := state.(tokens) in
  let old_balance := with_default 0 (FMap.find param.(target) tokens_) in
  let new_balance := (Z.of_N old_balance + param.(quantity))%Z in
  do _ <- returnIf (new_balance <? 0)%Z ; (* Cannot burn more than the target's balance. *)
  let tokens_ := FMap.add param.(target) (Z.to_N new_balance) tokens_ in
  let total_supply_ := Z.abs_N (Z.of_N state.(total_supply) + param.(quantity))%Z in
    Some (state<|tokens := tokens_|>
               <|total_supply := total_supply_|>).

(* Get the quantity that <snd request> is allowed to spend on behalf of <fst request> *)
Definition try_get_allowance (sender : Address) (param : getAllowance_param) (state : State) : list ActionBody :=
  let value := with_default 0 (FMap.find param.(request) state.(allowances)) in
    [act_call sender 0 (serialize (receive_allowance value))].

(* Get the quantity of tokens belonging to <owner> *)
Definition try_get_balance (sender : Address) (param : getBalance_param) (state : State) : list ActionBody :=
  let value := with_default 0 (FMap.find param.(owner_) state.(tokens)) in
    [act_call sender 0 (serialize (receive_balance_of value))].

(* Get the total supply of tokens *)
Definition try_get_total_supply (sender : Address) (param : getTotalSupply_param) (state : State) : list ActionBody :=
  let value := state.(total_supply) in
    [act_call sender 0 (serialize (receive_total_supply value))].

Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : option State :=
  Some {|
    tokens := FMap.empty;
    allowances := FMap.empty;
    admin := setup.(admin_);
    total_supply := 0
  |}.

Open Scope Z_scope.
Definition receive (chain : Chain) (ctx : ContractCallContext)
                   (state : State) (maybe_msg : option Msg)
                    : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
  let without_statechange acts := Some (state, acts) in
  if 0 <? ctx.(ctx_amount)
  then None (* DontSendTez *)
  else match maybe_msg with
  | Some (msg_transfer param) => without_actions (try_transfer sender param state)
  | Some (msg_approve param) => without_actions (try_approve sender param state)
  | Some (msg_mint_or_burn param) => without_actions (try_mint_or_burn sender param state)
  | Some (msg_get_allowance param) => without_statechange (try_get_allowance sender param state)
  | Some (msg_get_balance param) => without_statechange (try_get_balance sender param state)
  | Some (msg_get_total_supply param) => without_statechange (try_get_total_supply sender param state)
  | None => None (* Transfer actions to this contract are not allowed *)
  end.
Close Scope Z_scope.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.



Section Theories.

(* receive only returns Some if the sender amount is zero *)
Lemma contract_not_payable : forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    ((ctx_amount ctx) <= 0)%Z.
Proof.
  intros * receive_some.
  unfold receive in receive_some.
  destruct_match eqn:amount in receive_some.
  - (* case: ctx_amount > 0 *)
    congruence.
  - (* case: ctx_amount <= 0 *)
    now rewrite Z.ltb_ge in amount.
Qed.

Lemma contract_not_payable' : forall prev_state chain ctx msg,
  (0 < (ctx_amount ctx))%Z ->
    receive chain ctx prev_state msg = None.
Proof.
  intros * ctx_amount_positive.
  unfold receive.
  destruct_match eqn:amount.
  - (* case: ctx_amount > 0 *)
    reflexivity.
  - (* case: ctx_amount <= 0 *)
    now apply Z.ltb_ge in amount.
Qed.

Ltac receive_simpl_step :=
  match goal with
  | H : receive _ _ _ _ = Some (_, _) |- _ =>
      apply contract_not_payable in H as ctx_amount_zero;
      apply Z.ltb_ge in ctx_amount_zero;
      unfold receive in H;
      rewrite ctx_amount_zero in H;
      cbn in H
  | |- receive _ _ _ _ = _ =>
      unfold receive; cbn
  | H : Some _ = Some _ |- _ =>
      inversion_clear H
  | H : Some _ = None |- _ =>
      inversion H
  | H : None = Some _ |- _ =>
      inversion H
  | H : returnIf _ = None |- _ =>
    let G := fresh "G" in
      unfold returnIf in H;
      destruct_match eqn:G in H; try congruence;
      clear H;
      rename G into H
  | H : returnIf _ = Some ?u |- _ =>
    let G := fresh "G" in
      unfold returnIf in H;
      destruct_match eqn:G in H; try congruence;
      clear H u;
      rename G into H
  | H : option_map (fun s : State => (s, _)) match ?m with | Some _ => _ | None => None end = Some _ |- _ =>
    let a := fresh "H" in
    destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
  | H : option_map (fun s : State => (s, _)) (if ?m then ?a else ?b) = Some _ |- _ =>
    match a with
    | None =>
      let a := fresh "H" in
      destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
    | _ => match b with
           | None =>
             let a := fresh "H" in
             destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
           | _ => idtac
    end end
  | H : (if ?m then ?a else ?b) = Some _ |- _ =>
    match a with
    | None =>
      let a := fresh "H" in
      destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
    | _ => match b with
           | None =>
             let a := fresh "H" in
             destruct m eqn:a in H; try setoid_rewrite a; cbn in *; try congruence
           | _ => idtac
    end end
  end.
(*
  | H : context[receive] |- _ => unfold receive in H
  | |- context[receive] => unfold receive
  | H : context[Blockchain.receive] |- _ => unfold Blockchain.receive; cbn in H
  | H : context[try_transfer] |- _ => unfold try_transfer in H
  | H : context[try_transfer_from] |- _ => unfold try_transfer_from in H
  | H : context[try_approve] |- _ => unfold try_approve in H
  | |- context[Blockchain.receive] => unfold Blockchain.receive; cbn
  | |- context[try_transfer] => unfold try_transfer
  | |- context[try_transfer_from] => unfold try_transfer_from
  | |- context[try_approve] => unfold try_approve
*)

Tactic Notation "receive_simpl" := repeat receive_simpl_step.



(* ------------------- Admin is constant ------------------- *)

(* admin cannot be changed *)
Lemma admin_constant : forall prev_state new_state chain ctx new_acts msg,
  receive chain ctx prev_state msg = Some (new_state, new_acts) ->
    admin prev_state = admin new_state.
Proof.
  intros * receive_some.
  receive_simpl.
  destruct msg. destruct m.
  all : now receive_simpl.
Qed.



(* ------------------- Default entrypoint correct ------------------- *)

(* Default entrypoint should never succeed *)
Lemma default_entrypoint_none : forall prev_state chain ctx,
  receive chain ctx prev_state None = None.
Proof.
  intros *.
  receive_simpl.
  now destruct_match.
Qed.



(* ------------------- Transfer correct ------------------- *)

Definition transfer_balance_update_correct old_state new_state from to amount :=
  let get_balance addr state := with_default 0 (FMap.find addr state.(tokens)) in
  let from_balance_before := get_balance from old_state in
  let to_balance_before := get_balance to old_state in
  let from_balance_after := get_balance from new_state in
  let to_balance_after := get_balance to new_state in
  (* if the transfer is a self-transfer, balances should remain unchained *)
  if address_eqb from to
  then
    (from_balance_before =? from_balance_after) &&
    (to_balance_before =? to_balance_after)
  else
    (from_balance_before =? from_balance_after + amount) &&
    (to_balance_before + amount =? to_balance_after).

(* try_transfer correctly moves <amount> from <from> to <to> *)
Lemma try_transfer_balance_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_transfer param)) = Some (new_state, new_acts) ->
  transfer_balance_update_correct prev_state new_state param.(from) param.(to) param.(value) = true.
Proof.
  intros * receive_some.
  receive_simpl.
  rename H1 into enough_balance.
  rewrite N.ltb_ge in enough_balance.
  unfold transfer_balance_update_correct.
  cbn.
  destruct_match eqn:from_to_eqb.
  - (* from = to *)
    destruct (address_eqb_spec param.(from) param.(to)) as [<-|]; auto.
    rewrite !FMap.find_add.
    cbn.
    rewrite !N.sub_add; auto.
    now setoid_rewrite N.eqb_refl.
  - (* from <> to *)
    destruct (address_eqb_spec param.(from) param.(to)) as [| from_to_eq]; auto.
    rewrite FMap.find_add_ne; auto.
    rewrite ?FMap.find_add.
    rewrite FMap.find_add_ne; auto.
    cbn.
    rewrite !N.sub_add; auto.
    now setoid_rewrite N.eqb_refl.
Qed.

Definition transfer_allowances_update_correct old_state new_state sender from amount :=
  let get_allowance addr1 addr2 state := with_default 0 (FMap.find (addr1, addr2) state.(allowances)) in
  let allowance_before := get_allowance from sender old_state in
  let allowance_after := get_allowance from sender new_state in
  (* if the from and sender is equal, allowances should remain unchained *)
  if address_eqb sender from
  then
    (allowance_before =? allowance_after)
  else
    (allowance_before =? allowance_after + amount).

(* try_transfer correctly subtracts <amount> from allowances if <sender> is not <from> *)
Lemma try_transfer_allowance_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_transfer param)) = Some (new_state, new_acts) ->
  transfer_allowances_update_correct prev_state new_state ctx.(ctx_from) param.(from) param.(value) = true.
Proof.
  intros * receive_some.
  receive_simpl.
  clear g0 H1.
  unfold transfer_allowances_update_correct.
  cbn.
  destruct_match eqn:sender_from_eqb.
  - (* sender = from *)
    rename H into allowances_eq.
    inversion_clear allowances_eq.
    now rewrite N.eqb_refl.
  - (* sender <> from *)
    receive_simpl.
    rename H0 into enough_allowance.
    rewrite N.ltb_ge in enough_allowance.
    rewrite FMap.find_add.
    cbn.
    rewrite N.sub_add; auto.
    now rewrite N.eqb_refl.
Qed.

(* try_transfer does not produce any new actions *)
Lemma try_transfer_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_transfer param)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* try_transfer does not change the total supply of tokens *)
Lemma try_transfer_preserves_total_supply : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_transfer param)) = Some (new_state, new_acts) ->
    total_supply prev_state = total_supply new_state.
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* try_transfer only modifies the <from> and <to> balances *)
Lemma try_transfer_preserves_other_balances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_transfer param)) = Some (new_state, new_acts) ->
    forall account, account <> param.(from) -> account <> param.(to) ->
      FMap.find account (tokens prev_state) = FMap.find account (tokens new_state).
Proof.
  intros * receive_some account account_not_from account_not_to.
  receive_simpl.
  cbn.
  rewrite !FMap.find_add_ne; auto.
Qed.

(* try_transfer only modifies the <sender> and <from> allowances *)
Lemma try_transfer_preserves_other_allowances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_transfer param)) = Some (new_state, new_acts) ->
    forall allowance_key, allowance_key <> (param.(from), ctx.(ctx_from)) ->
      FMap.find allowance_key (allowances prev_state) = FMap.find allowance_key (allowances new_state).
Proof.
  intros * receive_some account allowance_key_ne.
  receive_simpl.
  cbn.
  rename H into allowance_eq.
  destruct_address_eq.
  - (* from = sender *)
    now inversion_clear allowance_eq.
  - (* from <> sender *)
    destruct_match in allowance_eq;
      inversion_clear allowance_eq;
      rewrite !FMap.find_add_ne; auto.
Qed.

(* If the requirements are met then then receive on transfer msg must succeed and
    if receive on transfer msg succeeds then requirements must hold *)
Lemma try_transfer_is_some : forall state chain ctx param,
  (ctx_amount ctx <= 0)%Z /\
  param.(value) <= with_default 0 (FMap.find param.(from) (tokens state)) /\
  (param.(from) <> ctx.(ctx_from) ->
    param.(value) <= with_default 0 (FMap.find (param.(from), ctx.(ctx_from)) (allowances state)))
    <-> exists new_state new_acts, receive chain ctx state (Some (msg_transfer param)) = Some (new_state, new_acts).
Proof.
  split.
  - intros (amount_zero & enough_balance & enough_allowance).
    (*do 2 eexists.
    receive_simpl.*)
    unfold receive.
    apply Z.ltb_ge in amount_zero.
    rewrite amount_zero.
    cbn.
    destruct_match eqn:allowances_eq;
    destruct_match eqn:sender_from_eqb in allowances_eq; try congruence;
    try destruct_match eqn:enough_allowance_check in allowances_eq; try congruence;
    try destruct_match eqn:new_balance;
    try destruct_match eqn:enough_balance_check in new_balance; try congruence.
    + (* case no contradictions *)
      inversion_clear allowances_eq.
      now inversion_clear new_balance.
    + (* enough balances contradiction *)
      receive_simpl.
      apply N.ltb_lt in enough_balance_check.
      now apply N.le_ngt in enough_balance.
    + (* case: no contradictions *)
      inversion_clear allowances_eq.
      now inversion_clear new_balance.
    + (* enough balances contradiction *)
      receive_simpl.
      apply N.ltb_lt in enough_balance_check.
      now apply N.le_ngt in enough_balance.
    + (* enough allowance contradiction *)
      receive_simpl.
      apply N.ltb_lt in enough_allowance_check.
      destruct (address_eqb_spec ctx.(ctx_from) param.(from)) as [| sender_from_ne]; try discriminate.
      now apply not_eq_sym, enough_allowance, N.le_ngt in sender_from_ne.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    split; try now apply Z.ltb_ge in ctx_amount_zero.
    clear ctx_amount_zero g0.
    rename H1 into enough_balance.
    apply N.ltb_ge in enough_balance.
    rename H into allowance_check.
    destruct_match eqn:sender_from_eqb in allowance_check;
      destruct (address_eqb_spec ctx.(ctx_from) param.(from)) as
        [send_from_eq | sender_from_ne]; try discriminate.
    + (* sender = from *)
      now split.
    + (* sender <> from *)
      destruct_match eqn:enough_allowance in allowance_check; try congruence.
      receive_simpl.
      now apply N.ltb_ge in enough_allowance.
Qed.



(* ------------------- Approve correct ------------------- *)

(* try_approve correctly sets allowance of (<sender>, <spender>) to <value_> *)
Lemma try_approve_allowance_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_approve param)) = Some (new_state, new_acts) ->
    FMap.find (ctx.(ctx_from), param.(spender)) (allowances new_state) = Some param.(value_).
Proof.
  intros * receive_some.
  receive_simpl.
  clear H ctx_amount_zero.
  cbn.
  now rewrite FMap.find_add.
Qed.

(* try_approve does not produce any new actions *)
Lemma try_approve_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_approve param)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros * receive_some.
  receive_simpl.
Qed.

(* try_approve does not change allowances map of other addresses *)
Lemma try_approve_preserves_other_allowances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_approve param)) = Some (new_state, new_acts) ->
    forall allowance_key, allowance_key <> (ctx.(ctx_from), param.(spender)) ->
      FMap.find allowance_key (allowances prev_state) = FMap.find allowance_key (allowances new_state).
Proof.
  intros * receive_some allowance_key allowance_key_ne.
  receive_simpl.
  clear H ctx_amount_zero.
  cbn.
  now rewrite FMap.find_add_ne.
Qed.

(* try_approve does not change total supply of tokens *)
Lemma try_approve_preserves_total_supply : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_approve param)) = Some (new_state, new_acts) ->
    total_supply prev_state = total_supply new_state.
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* try_approve does not change balances *)
Lemma try_approve_preserves_balances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_approve param)) = Some (new_state, new_acts) ->
    tokens prev_state = tokens new_state.
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* If the requirements are met then then receive on approve msg must succeed and
    if receive on approve msg succeeds then requirements must hold *)
Lemma try_approve_is_some : forall state chain ctx param,
  (ctx_amount ctx <= 0)%Z /\
  (with_default 0 (FMap.find (ctx.(ctx_from), param.(spender)) (allowances state)) = 0 \/ param.(value_) = 0)
    <-> exists new_state new_acts, receive chain ctx state (Some (msg_approve param)) = Some (new_state, new_acts).
Proof.
  split.
  - intros (amount_zero & safe_approval).
    do 2 eexists.
    receive_simpl.
    apply Z.ltb_ge in amount_zero.
    rewrite amount_zero.
    destruct_match eqn:safe_approval_check; eauto.
    receive_simpl.
    apply andb_prop in safe_approval_check as
      (?%N.ltb_lt & ?%N.ltb_lt).
    now destruct safe_approval.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    split; try now apply Z.ltb_ge in ctx_amount_zero.
    rename H into safe_approval.
    now apply andb_false_iff in safe_approval as [?%N.ltb_ge | ?%N.ltb_ge].
Qed.



(* ------------------- Burn or mint correct ------------------- *)

(* try_mint_or_burn correctly mints/burns <amount> from/to <target> *)
Lemma try_mint_or_burn_balance_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_mint_or_burn param)) = Some (new_state, new_acts) ->
    (Z.of_N (with_default 0%N (FMap.find param.(target) (tokens prev_state))) + param.(quantity) =
    Z.of_N (with_default 0%N (FMap.find param.(target) (tokens new_state))))%Z.
Proof.
  intros * receive_some.
  receive_simpl.
  rename H0 into enough_tokens.
  clear ctx_amount_zero H.
  rewrite Z.ltb_ge in enough_tokens.
  cbn.
  rewrite FMap.find_add.
  cbn.
  now rewrite Z2N.id.
Qed.

(* try_mint_or_burn correctly updates total_supply *)
Lemma try_mint_or_burn_total_supply_correct : forall prev_state new_state chain ctx new_acts param,
  with_default 0 (FMap.find param.(target) (tokens prev_state)) <= total_supply prev_state ->
  receive chain ctx prev_state (Some (msg_mint_or_burn param)) = Some (new_state, new_acts) ->
    (Z.of_N prev_state.(total_supply) + param.(quantity) =
    Z.of_N new_state.(total_supply))%Z.
Proof.
  intros * balance_le_total_supply receive_some.
  receive_simpl.
  rename H0 into enough_tokens.
  clear ctx_amount_zero H.
  rewrite Z.ltb_ge in enough_tokens.
  cbn.
  rewrite N2Z.inj_abs_N, Z.abs_eq; auto.
  eapply Z.le_trans; try apply enough_tokens.
  now apply Zplus_le_compat_r, N2Z.inj_le.
Qed.


(* try_mint_or_burn produces no new actions *)
Lemma try_mint_or_burn_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_mint_or_burn param)) = Some (new_state, new_acts) ->
    new_acts = [].
Proof.
  intros.
  receive_simpl.
Qed.

(* try_mint_or_burn only modifies the <target> balance *)
Lemma try_mint_or_burn_preserves_other_balances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_mint_or_burn param)) = Some (new_state, new_acts) ->
    forall account, account <> param.(target) ->
      FMap.find account (tokens prev_state) = FMap.find account (tokens new_state).
Proof.
  intros * receive_some account account_not_target.
  receive_simpl.
  cbn.
  rewrite FMap.find_add_ne; auto.
Qed.

(* try_mint_or_burn does not change allowances *)
Lemma try_mint_or_burn_preserves_allowances : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_mint_or_burn param)) = Some (new_state, new_acts) ->
      allowances prev_state = allowances new_state.
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* If the requirements are met then then receive on mint_or_burn msg must succeed and
    if receive on mint_or_burn msg succeeds then requirements must hold *)
Lemma try_mint_or_burn_is_some : forall state chain ctx param,
  (ctx_amount ctx <= 0)%Z /\
  ctx.(ctx_from) = state.(admin) /\
  (0 <= Z.of_N (with_default 0%N (FMap.find param.(target) (tokens state))) + param.(quantity))%Z
    <-> exists new_state new_acts, receive chain ctx state (Some (msg_mint_or_burn param)) = Some (new_state, new_acts).
Proof.
  split.
  - intros (amount_zero & from_admin & enough_balance).
    do 2 eexists.
    receive_simpl.
    apply Z.ltb_ge in amount_zero.
    rewrite amount_zero.
    destruct_address_eq; try congruence.
    clear e from_admin. cbn.
    destruct_match eqn:enough_balance_check; eauto.
    receive_simpl.
    now apply Z.ltb_lt in enough_balance_check.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    split; try now apply Z.ltb_ge in ctx_amount_zero.
    split; try now destruct_address_eq.
    now apply Z.ltb_ge.
Qed.



(* ------------------- Get allowance correct ------------------- *)

(* try_get_allowance produces a callback to the correct contract with
    the requested allowance, the call should carry no balance *)
Lemma try_get_allowance_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_get_allowance param)) = Some (new_state, new_acts) ->
    new_acts = [
      act_call ctx.(ctx_from) 0%Z (serialize
        (receive_allowance (with_default 0 (FMap.find param.(request) (allowances prev_state)))))
    ].
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* try_get_allowance does not modify state *)
Lemma try_get_allowance_preserves_state : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_get_allowance param)) = Some (new_state, new_acts) ->
    prev_state = new_state.
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* If the requirements are met then then receive on get_allowance msg must succeed and
    if receive on get_allowance msg succeeds then requirements must hold *)
Lemma try_get_allowance_is_some : forall prev_state chain ctx param,
  (ctx_amount ctx <= 0)%Z <->
  exists new_state new_acts, receive chain ctx prev_state (Some (msg_get_allowance param)) = Some (new_state, new_acts).
Proof.
  split.
  - intros amount_zero.
    unfold receive.
    apply Z.ltb_ge in amount_zero.
    now rewrite amount_zero.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    now apply Z.ltb_ge in ctx_amount_zero.
Qed.



(* ------------------- Get balance correct ------------------- *)

(* try_get_balance produces a callback to the correct contract with
    the requested balance, the call should carry no balance *)
Lemma try_get_balance_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_get_balance param)) = Some (new_state, new_acts) ->
    new_acts = [
      act_call ctx.(ctx_from) 0%Z (serialize
        (receive_balance_of (with_default 0 (FMap.find param.(owner_) (tokens prev_state)))))
    ].
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* try_get_balance does not modify state *)
Lemma try_get_balance_preserves_state : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_get_balance param)) = Some (new_state, new_acts) ->
    prev_state = new_state.
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* If the requirements are met then then receive on get_balance msg must succeed and
    if receive on get_balance msg succeeds then requirements must hold *)
Lemma try_get_balance_is_some : forall prev_state chain ctx param,
  (ctx_amount ctx <= 0)%Z <->
  exists new_state new_acts, receive chain ctx prev_state (Some (msg_get_balance param)) = Some (new_state, new_acts).
Proof.
  split.
  - intros amount_zero.
    unfold receive.
    apply Z.ltb_ge in amount_zero.
    now rewrite amount_zero.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    now apply Z.ltb_ge in ctx_amount_zero.
Qed.



(* ------------------- Get total supply correct ------------------- *)

(* try_get_total_supply produces a callback to the correct contract with
    the tptal supply of tokens, the call should carry no balance *)
Lemma try_get_total_supply_new_acts_correct : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_get_total_supply param)) = Some (new_state, new_acts) ->
    new_acts = [
      act_call ctx.(ctx_from) 0%Z (serialize
        (receive_total_supply prev_state.(total_supply)))
    ].
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* try_get_total_supply does not modify state *)
Lemma try_get_total_supply_preserves_state : forall prev_state new_state chain ctx new_acts param,
  receive chain ctx prev_state (Some (msg_get_total_supply param)) = Some (new_state, new_acts) ->
    prev_state = new_state.
Proof.
  intros * receive_some.
  now receive_simpl.
Qed.

(* If the requirements are met then then receive on get_total_supply msg must succeed and
    if receive on get_total_supply msg succeeds then requirements must hold *)
Lemma try_get_total_supply_is_some : forall prev_state chain ctx param,
  (ctx_amount ctx <= 0)%Z <->
  exists new_state new_acts, receive chain ctx prev_state (Some (msg_get_total_supply param)) = Some (new_state, new_acts).
Proof.
  split.
  - intros amount_zero.
    unfold receive.
    apply Z.ltb_ge in amount_zero.
    now rewrite amount_zero.
  - intros (new_state & new_acts & receive_some).
    receive_simpl.
    now apply Z.ltb_ge in ctx_amount_zero.
Qed.



(* ------------------- Total supply / token balance facts ------------------- *)

(* sum of all token balances *)
Definition sum_balances state :=
  sumN (fun '(k, v) => v) (FMap.elements (tokens state)).

Lemma sum_balances_eq_total_supply : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ total_supply cstate = sum_balances cstate.
Proof.
Admitted.

Lemma token_balance_le_total_supply : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ forall addr, with_default 0 (FMap.find addr (tokens cstate)) <= total_supply cstate.
Proof.
Admitted.





(*
  TODO
    init correct
    sum of balances eq total_supply
    single token balance less than total supply
*)




End Theories.
End LQTFA12.
