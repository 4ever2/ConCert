(**  PancakeSwap Swap transaction
     Based on https://github.com/pancakeswap/pancake-smart-contracts/blob/master/projects/exchange-protocol/contracts/PancakeRouter.sol
     As well as: https://github.com/pancakeswap/pancake-smart-contracts/blob/master/projects/exchange-protocol/contracts/libraries/PancakeLibrary.sol
     & https://github.com/pancakeswap/pancake-smart-contracts/blob/master/projects/exchange-protocol/contracts/PancakePair.sol

     The code is a combining the 3 contracts by traversing the swap function and implementing needed helper functions.
     The implementation is a simplified version and does not consider liquidity nor following a 'path' for swapping. eg. token -> BNB -> token

*)

From Coq Require Import ZArith_base.
From Coq Require Import List.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Basics.
From Coq Require Import Lia.
From ConCert.Execution.Test Require Import QCTest.
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

    Definition WETH := addr_of_Z 11.

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

    Definition check_if_pair_exists (token0: Address)
                                    (s: AddressMap.AddrMap Address) 
                                    : bool :=
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

    (* TODO: Figure out how to correctly retrieve resereves of a token pair*)
    Definition get_reserves (tokenA: Address)
                            (tokenB: Address)
                            : (TokenValue * TokenValue) :=
    (* TODO: Store/fetch reserves correctly *)
    (50000 , 100000).
    
    Definition get_amount_in (amountOut: TokenValue)
                             (reserveIn: TokenValue)
                             (reserveOut: TokenValue)
                             : TokenValue :=
    (* Add check for output amount *)
    (* Add check for sufficient liquidity *)
    let numerator := reserveIn * amountOut * 10000 in
    let denominator := reserveOut - amountOut * 9975 in
    (numerator/denominator) + 1.
    
    Definition get_amounts_in (amountOut: TokenValue)
                              (tokenA: Address)
                              (tokenB: Address)
                              : (TokenValue * TokenValue) := 
    (* Should check if "path" is >= 2, but in this case we only work with two tokens *)
    (* We already know the output value for tokenB, so we are only calculating for tokenA *)
    let amount0 := amountOut in
    let (reserveIn, reserveOut) := get_reserves  tokenA tokenB in
    let amount1 := get_amount_in amount0 reserveIn reserveOut in
    (amount0, amount1).

    (* Given input amount (BNB) and token pair reserves, returns the maximum output amount of the other asset*)
    Definition get_amount_out (amountIn: TokenValue)
                              (reserveIn: TokenValue)
                              (reserveOut: TokenValue)
                              : TokenValue :=
    (* Add check for input amount *)
    (* Add check for sufficient liquidity *)
    let amountInWithFee := amountIn * 9975 in
    let numerator := amountInWithFee * reserveOut in
    let denominator := reserveIn * 10000 + amountInWithFee in
    (numerator/denominator). (* Maximum output of asset *)
  
    (* Almost the same as get_amounts_in. We only work with two tokens and not a path. *)
    Definition get_amounts_out (amountIn: TokenValue)
                               (tokenA: Address) 
                               (tokenB: Address)
                               : (TokenValue * TokenValue) := 
    let amount0 := amountIn in (* The amount of swapped BNB *)
    let (reserveIn, reserveOut) := get_reserves  tokenA tokenB in
    let amount1 := get_amount_out amount0 reserveIn reserveOut in
    (amount0, amount1).
    
    Definition swap_exact_eth_for_tokens   (value: TokenValue)
                                           (amountOutMin: TokenValue)
                                           (tokenA: Address)
                                           (tokenB: Address)
                                           (state: State)
                                           : result State Error :=
    (*   *)
    (* do _ <- throwIf (address_eqb tokenA WETH) default_error; (* Pancake: INVALID_PATH*) *)                                        
    let amounts := get_amounts_out value tokenA tokenB in

    (* Check if the amount calculated in amounts[1] is greater than our amountOutMin value *)
    (* Conversion from BNB to WBNB happens here *)

    Ok(state).
End Pancake.
