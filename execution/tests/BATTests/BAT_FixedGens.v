From ConCert Require Import Blockchain BAT_Fixed.
From ConCert Require Import Serializable.
From ConCert Require Import Containers.
From ConCert.Execution.QCTests Require Import
  TestUtils EIP20TokenGens.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List ZArith. Import ListNotations.

Module Type BATGensInfo.
  Parameter contract_addr : Address.
  Parameter accounts : list Address.
  Parameter gAccount : Chain -> G Address.
  Parameter bat_addr : Address.
  Parameter fund_addr : Address.
End BATGensInfo.

Module BATGens (Info : BATGensInfo).
Import Info.
Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Definition account_balance (env : Environment) (addr : Address) : Amount :=
  (env_account_balances env) addr.

Definition get_refundable_accounts state : list (G (option Address)) :=
  let balances_list := FMap.elements (balances state) in
  let filtered_balances := filter (fun x => (negb (address_eqb bat_addr (fst x))) && (0 <? (snd x))%N) balances_list in
    map returnGen (map Some (map fst filtered_balances)).

Definition get_fundable_accounts env : list (G (option Address)) :=
  let filtered_accounts := filter (fun addr => (0 <? (account_balance env addr))%Z) accounts in
    map returnGen (map Some filtered_accounts).

Definition gFund_amount env state addr : G Z :=
  (choose (1, Z.min (account_balance env addr) (Z.of_N ((state.(tokenCreationCap) - (total_supply state)) / state.(tokenExchangeRate)))))%Z.

Definition gCreateTokens (env : Environment) (state : BAT_Fixed.State) : GOpt (Address * Amount * Msg) :=
  let current_slot := current_slot (env_chain env) in
  if (state.(isFinalized)
          || (Nat.ltb current_slot state.(fundingStart))
          || (Nat.ltb state.(fundingEnd) current_slot) (* Funding can only happen in funding period *)
          || (N.ltb (state.(tokenCreationCap) - (total_supply state)) state.(tokenExchangeRate))) (* No funding if cap was hit or we are too clos to it *)
  then
    returnGen None
  else
    from_addr <- oneOf_ (returnGen None) (get_fundable_accounts env) ;;
    value <- bindGen (gFund_amount env state from_addr) returnGenSome ;;
    returnGenSome (from_addr, value, create_tokens).

Definition gCreateTokensInvalid (env : Environment) (state : BAT_Fixed.State) : GOpt (Address * Amount * Msg) :=
  from_addr <- oneOf_ (returnGen None) (get_fundable_accounts env) ;;
  value <- bindGen (choose (1, account_balance env from_addr)%Z) returnGenSome ;;
  returnGenSome (from_addr, value, create_tokens).

Definition gRefund (env : Environment) (state : BAT_Fixed.State) : GOpt (Address * Msg) :=
  let current_slot := current_slot (env_chain env) in
  let accounts := get_refundable_accounts state in
  if ((state.(isFinalized)
          || (Nat.leb current_slot state.(fundingEnd))
          || (state.(tokenCreationMin) <=? (total_supply state))%N))
  then
    returnGen None
  else 
    from_addr <- oneOf_ (returnGen None) accounts ;;
    returnGenSome (from_addr, refund).

Definition gRefundInvalid (env : Environment) (state : BAT_Fixed.State) : G (Address * Msg) :=
  from_addr <- gAccount env ;;
  returnGen (from_addr, refund).

Definition gFinalize (env : Environment) (state : BAT_Fixed.State) : GOpt (Address * Msg) :=
  let current_slot := current_slot (env_chain env) in
  if (state.(isFinalized)
        || ((total_supply state) <? state.(tokenCreationMin))%N
        || ((Nat.leb current_slot state.(fundingEnd)) && negb ((total_supply state) =? state.(tokenCreationCap))%N))
  then
    returnGen None
  else
    returnGenSome (fund_addr, finalize).

Definition gFinalizeInvalid (env : Environment) (state : BAT_Fixed.State) : G (Address * Msg) :=
  from_addr <- gAccount env ;;
  returnGen (from_addr, finalize).

Module EIP20 := EIP20Gens Info.

Definition gTransfer (env : Environment) (state : BAT_Fixed.State) : GOpt (Address * Msg) :=
  if state.(isFinalized)
  then
    '(caller, msg) <- EIP20.gTransfer env (token_state state) ;;
    returnGenSome (caller, tokenMsg msg)
  else
    returnGen None.

Definition gApprove (state : BAT_Fixed.State) : GOpt (Address * Msg) :=
  if state.(isFinalized)
  then
    bindGenOpt (EIP20.gApprove (token_state state))
        (fun '(caller, msg) => returnGenSome (caller, tokenMsg msg))
  else
    returnGen None.

Definition gTransfer_from (state : BAT_Fixed.State) : GOpt (Address * Msg) :=
  if state.(isFinalized)
  then
    bindGenOpt (EIP20.gTransfer_from (token_state state))
        (fun '(caller, msg) => returnGenSome (caller, tokenMsg msg))
  else
    returnGen None.

(* BAT valid call generator 
   Generator that will always return BAToken contract calls that are valid on their own,
   i.e. guaranteed to be valid if it is the first action executed in the block.
*)
Definition gBATActionValid (env : Environment) : GOpt Action :=
  let call contract_addr caller_addr value msg :=
    returnGenSome (build_act caller_addr (act_call contract_addr value ((@serialize BAT_Fixed.Msg _) msg))) in
  state <- returnGen (get_contract_state BAT_Fixed.State env contract_addr) ;;
  backtrack [
    (* transfer *)
    (2, bindGenOpt (gTransfer env state)
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) msg
        )
    );
    (* transfer_from *)
    (3, bindGenOpt (gTransfer_from state)
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) msg
        )
    );
    (* approve *)
    (2, bindGenOpt (gApprove state)
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) msg
        )
    );
    (* create_tokens *)
    (5, bindGenOpt (gCreateTokens env state)
        (fun '(caller, value, msg) =>
          call contract_addr caller value msg
        )
    );
    (* refund *)
    (1, bindGenOpt (gRefund env state)
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) msg
        )
    );
    (* finalize *)
    (1, bindGenOpt (gFinalize env state)
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) msg
        )
    )
  ].

(* BAT invalid call generator 
   Generator likely to generate invalid BAToken contract calls.
   It treats the BAToken code mostly as blackbox and only know the expected types of input
    but does not make any assumptions/checks on which values will result in valid or invalid calls
*)
Definition gBATActionInvalid (env : Environment) : GOpt Action :=
  let call contract_addr caller_addr value msg :=
    returnGenSome (build_act caller_addr (act_call contract_addr value ((@serialize BAT_Fixed.Msg _) msg))) in
  state <- returnGen (get_contract_state BAT_Fixed.State env contract_addr) ;;
  backtrack [
    (* transfer *)
    (2, '(caller, msg) <- EIP20.gTransfer env (token_state state) ;;
        call contract_addr caller (0%Z) (tokenMsg msg)
    ) ;
    (* transfer_from *)
    (3, bindGenOpt (EIP20.gTransfer_from (token_state state))
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) (tokenMsg msg)
        )
    );
    (* approve *)
    (2, bindGenOpt (EIP20.gApprove (token_state state))
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) (tokenMsg msg)
        )
    );
    (* create_tokens *)
    (5, bindGenOpt (gCreateTokensInvalid env state)
        (fun '(caller, value, msg) =>
          call contract_addr caller value msg
        )
    );
    (* refund *)
    (1, '(caller, msg) <- gRefundInvalid env state ;;
        call contract_addr caller (0%Z) msg
    );
    (* finalize *)
    (1, '(caller, msg) <- gFinalizeInvalid env state ;;
        call contract_addr caller (0%Z) msg
    )
  ].

(* BAT call generator
   Has a 0.3% chance to attempt to generate an invalid contract call
    More specifically it has:
    - 0.06% chance of generating a valid call and then replacing the amount of money sent with that call.
      For BAT contract this is likely to result in an invalid call as most contract calls on BAToken are 
      not allowed to include money in them.
    - 0.24% chance of using the invalid action generator. This generator is likely to generate an invalid call
      since it treats the contract as a black box and thus does not check any of the expected requirements for
      a contract call to be valid.
    The reamaining 99.7% of the time it will generate a call that is guaranteed to be valid (only guaranteed to
    be valid on its own, since the generator cannot know what other calls may be included in the same block and
    which order they will be executed in)
*)
Definition gBATAction (env : Environment) : GOpt Action :=
  state <- returnGen (get_contract_state BAT_Fixed.State env contract_addr) ;;
  freq [
    (6, bindGenOpt (gBATActionValid env)
        (fun '(action) =>
          match action.(act_body) with
          | act_transfer _ _ => returnGen None
          | act_deploy _ _ _ => returnGen None
          | act_call to _ msg =>
            amount <- choose (0, account_balance env action.(act_from))%Z ;;
            returnGenSome (build_act action.(act_from) (act_call to amount msg))
          end
        ));
    (24, gBATActionInvalid env);
    (970, gBATActionValid env)
  ].

End BATGens.