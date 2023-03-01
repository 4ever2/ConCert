(**  PancakeSwap Router
     Based on https://github.com/pancakeswap/pancake-smart-contracts/blob/master/projects/exchange-protocol/contracts/PancakeRouter.sol
     As well as: https://github.com/pancakeswap/pancake-smart-contracts/blob/master/projects/exchange-protocol/contracts/libraries/PancakeLibrary.sol
*)

From Coq Require Import ZArith_base.
From Coq Require Import List.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Basics.
From Coq Require Import Lia.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.

Open Scope Z.

(** Definition *)
Section Pancake.
    Context {BaseTypes : ChainBase}.
    Definition TokenValue := N.

    Open Scope N_scope.
    Open Scope bool.

    Set Nonrecursive Elimination Schemes.

    Definition Error : Type := nat.
    Definition default_error : Error := 1%nat.

    Definition error {T : Type} : result T Error :=
        Err default_error.

    Record State :=
    build_state {
        all_pairs : AddressMap.AddrMap Address;

    }.

    Definition Result : Type := result (State * list ActionBody) Error.    

    Inductive Msg :=
    | swap : TokenValue -> TokenValue -> Msg.

    Record Setup :=
        build_setup {
            owner : Address;
        }.

      (* begin hide *)
    MetaCoq Run (make_setters State).
    MetaCoq Run (make_setters Setup).

    Section Serialization.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.
  (* end hide *)


    Definition init (chain : Chain)
    (ctx : ContractCallContext)
    (setup : Setup)
    : result State Error :=
    Ok {| all_pairs := AddressMap.empty;
    |}.

    Definition check_if_pair_exists (token0: Address) (s: AddressMap.AddrMap Address) : bool :=
        match AddressMap.find token0 s with
        | Some _ => true
        | None => false
        end.
    
    Definition try_createPair (tokenA: Address)
                              (tokenB: Address)
                              (state: State)
                              : result State Error :=
    do _ <- throwIf (address_eqb tokenA tokenB) default_error; (* Pancake: IDENTICAL_ADDRESS*)
    (* TODO: Add check to see if address is the "0x0" address *)
    do _ <- throwIf (check_if_pair_exists tokenA state.(all_pairs)) default_error; (* Pancake: PAIR_EXISTS*)
    Ok(state<|all_pairs := AddressMap.add tokenA tokenB state.(all_pairs)|>). (* Add the new pair to the state/list of pairs*)


    Definition get_reserves 
    (tokenA: Address)
    (tokenB: Address)
    : (TokenValue * TokenValue) :=
    (* TODO: Store/fetch reserves correctly *)
    (50000 , 100000) 
    .
    

    Definition get_amount_in (amountOut: TokenValue)
                             (reserveIn: TokenValue)
                             (reserveOut: TokenValue)
                             : TokenValue :=
    (* Add check for outpunt amount *)
    (* Add check for sufficient liquidity *)
    let numerator := reserveIn * amountOut * 10000 in
    let denominator := reserveOut - amountOut * 9975 in
    (numerator/denominator) + 1                              
    .
    

    Definition get_amounts_in
                              (amountOut: TokenValue)
                              (tokenA: Address)
                              (tokenB: Address)
                              : (TokenValue * TokenValue) := 
    (* Should check if "path" is >= 2, but in this case we only work with two tokens *)
    (* We already know the output value for tokenB, so we are only calculating for tokenA *)
    let amount1 := amountOut in
    let (reserveIn, reserveOut) := get_reserves  tokenA tokenB in
    let amount2 := get_amount_in amount1 reserveIn reserveOut in
    (amount1, amount2)
    .

    Definition swap_tokens_for_exact_tokens (amountOut: TokenValue)
                                           (amountInMax: TokenValue)
                                           (tokenA: Address)
                                           (tokenB: Address)
                                           (state: State)
                                           : result State Error := 
    let amounts := get_amounts_in amountOut tokenA tokenB in
    (* call to correct swap function*)
    (* Check if amount[0] is less than amountInMax *)
    
    Ok(state)
    .
    



