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

    Record swap_param :=
      build_swap_param {
        value : TokenValue;
        amountOutMin: TokenValue;
        tokenA : Address;
        tokenB : Address;
        amount0 : TokenValue;
        amount1 : TokenValue;
        amount0Out: TokenValue;
        amount1Out: TokenValue;
        to : Address
    }.

    Record State :=
      build_state {
          pair : (Address * Address);
          created : bool;
          reserves : (TokenValue * TokenValue);
      }.

    (* Definition WETH : Address := addr_of_Z 128. *)

    Definition error {T : Type} : result T Error :=
        Err default_error.

    Definition Result : Type := result (State * list ActionBody) Error.    

    Inductive Msg :=
    | swap : swap_param -> Msg.

    Record Setup :=
        build_setup {
            init_address : Address;
            init_amount: TokenValue;
            pair_created: bool;
        }.

    (* begin hide *)
    MetaCoq Run (make_setters State).
    MetaCoq Run (make_setters swap_param).
    MetaCoq Run (make_setters Setup).

    Section Serialization.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

    Axiom set_param_serializable : Serializable swap_param.
      Existing Instance set_param_serializable.

    End Serialization.
    (* end hide *)

    Definition init (chain : Chain)
                    (ctx : ContractCallContext)
                    (setup : Setup)
                    : result State Error :=
    Ok {| pair := (setup.(init_address), setup.(init_address));
          reserves := (setup.(init_amount), setup.(init_amount));
          created := setup.(pair_created)
    |}.

    Definition check_amount (in_amount: TokenValue)
                            (min_amount: TokenValue)
                            : bool :=
    (in_amount <? min_amount).
    
    Definition try_createPair (chain : Chain)
                              (ctx : ContractCallContext)
                              (tokenA: Address)
                              (tokenB: Address)
                              (param : swap_param)
                              (state: State)
                              : result State Error :=
    do _ <- throwIf (address_eqb tokenA tokenB) default_error; (* Pancake: IDENTICAL_ADDRESS*)
    (* TODO: Add check to see if address is the "0x0" address *)
    do _ <- throwIf (state.(created)) default_error; (* Pancake: PAIR_EXISTS*)

    (* Could later on have the addLiqudity functionality.
       For now we manually set the liqudity for each token *)

    Ok(state<|created := true|>). 
    


    Definition get_reserves (tokenA: Address)
                            (tokenB: Address)
                            (state: State)
                            : (TokenValue * TokenValue) :=
    (fst state.(reserves) , snd state.(reserves)).
    
    Definition get_amount_in (amountOut: TokenValue)
                             (reserveIn: TokenValue)
                             (reserveOut: TokenValue)
                             : TokenValue :=
    (* Add check for output amount *)
    (* Add check for sufficient liquidity *)
    let numerator := reserveIn * amountOut * 10000 in
    let denominator := reserveOut - amountOut * 9975 in
    (numerator/denominator) + 1.
    
(*     Definition get_amounts_in (amountOut: TokenValue)
                              (tokenA: Address)
                              (tokenB: Address)
                              : (TokenValue * TokenValue) := 
    (* Should check if "path" is >= 2, but in this case we only work with two tokens *)
    (* We already know the output value for tokenB, so we are only calculating for tokenA *)
    let amount0 := amountOut in
    let (reserveIn, reserveOut) := get_reserves tokenA tokenB in
    let amount1 := get_amount_in amount0 reserveIn reserveOut in
    (amount0, amount1). *)

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
  
    Definition get_amounts_out (amountIn: TokenValue)
                               (tokenA: Address) 
                               (tokenB: Address)
                               (state: State)
                               : (TokenValue * TokenValue) := 
    let amount0 := amountIn in (* The amount of swapped BNB *)
    let (reserveIn, reserveOut) := get_reserves  tokenA tokenB state in
    let amount1 := get_amount_out amount0 reserveIn reserveOut in
    (amount0, amount1).

    Definition real_swap (chain : Chain)
                         (ctx : ContractCallContext)
                         (state : State)
                         (param : swap_param)
                    : result State Error :=
    (* Require that amounts are greater than 0 *)
    do _ <- throwIf (check_amount 0 param.(amount0Out)) default_error; (* Pancake: INSUFFICIENT_OUTPUT_AMOUNT*)
    do _ <- throwIf (check_amount 0 param.(amount1Out)) default_error; (* Pancake: INSUFFICIENT_OUTPUT_AMOUNT*)

    let (reserve0, reserve1) := get_reserves param.(tokenA) param.(tokenB) state in

    (* Require that there is sufficient liquidity *)
    do _ <- throwIf (check_amount param.(amount0Out) reserve0) default_error; (* Pancake: INSUFFICIENT_LIQUIDITY*)
    do _ <- throwIf (check_amount param.(amount1Out) reserve1) default_error; (* Pancake: INSUFFICIENT_LIQUIDITY*)

    (* Require that 'to' address is not equal to the address of tokenA or tokenB *)

    (* We transfer the amount0Out and amount1Out *)

    (* Update the balance of tokenA and tokenB *)

    let balance0 := fst state.(reserves) in
    let balance1 := snd state.(reserves) in

    (* Update the reserves *)

    let new_state := state<|reserves := (balance0, balance1)|> in 

    Ok(new_state).

    (* This function can probably be omitted. It is mainly focusing on a Path > 2, and therefore sorting the input
       In our simple example with only 2 Tokens, it should be possible to leave this out.
       SHOULD CALCULATE THE 2 AMOUNTS OUT 
    Definition pre_swap (chain : Chain)
                        (ctx : ContractCallContext)
                        (state : State)
                        (param : swap_param)
                    : result State Error := 
    Ok(state). *)
        
    Definition swap_exact_eth_for_tokens   (chain : Chain)
                                           (ctx : ContractCallContext)
                                           (state : State)
                                           (param : swap_param)
                                           : result State Error :=
    (* TokenA has to be BNB  *)
    (* do _ <- throwIf (address_eqb tokenA WETH) default_error; (* Pancake: INVALID_PATH*) *)                                        
    let (cal_amount0, cal_amount1) := get_amounts_out param.(value) param.(tokenA) param.(tokenB) state in
    let new_param := param<|amount0 := cal_amount0|> in 
    (* Require that the output amount is greater than our amountOutMin *)
    do _ <- throwIf (check_amount cal_amount1 (new_param.(amountOutMin))) default_error; (* Pancake: INSUFFICIENT_OUTPUT_AMOUNT*) 

    (* Conversion from BNB to WBNB happens here and is deposited *)

    (* Call the pre_swap function to get correct amounts *)
    real_swap chain ctx state new_param.
   
End Pancake.


Section Theories.
  Context {BaseTypes : ChainBase}.
  Open Scope N_scope.
  Open Scope bool.

    (** Initialization should always succeed *)
  Lemma init_is_some : forall chain ctx setup,
    exists state, init chain ctx setup = state.
  Proof.
    eauto.
  Qed.

  Lemma pair_created_updates_correctly :
  forall (chain : Chain)
         (ctx : ContractCallContext)
         (tokenA tokenB : Address)
         (param : swap_param)
         (reserves : (TokenValue * TokenValue)),
    let state := {| pair := (tokenA, tokenB); created := false; reserves := reserves |} in
    try_createPair chain ctx tokenA tokenB param state = 
      Ok (state<|created:=true|>).
      Proof.
        intros chain ctx tokenA tokenB param reserves.
        unfold try_createPair.
        simpl.
    Admitted.
    
    Lemma swap_updates_reserves :
    forall (chain : Chain)
           (ctx : ContractCallContext)
           (tokenA tokenB : Address)
           (params : swap_param)
           (reserves_before reserves_after : (TokenValue * TokenValue)),
      let state_before := {| pair := (tokenA, tokenB); created := true; reserves := reserves_before |} in
      let state_after := swap_exact_eth_for_tokens chain ctx state_before params in
      state_after = Ok {| pair := (tokenA, tokenB); created := true; reserves := reserves_after |} ->
      reserves_after <> reserves_before.
    Proof.
        intros.
        unfold swap_exact_eth_for_tokens in H.
        destruct state_before.
        simpl in H.
        inversion H.
        subst.
        simpl.
        intro H_contra.
        inversion H_contra.
        subst.
    Admitted.

    (* The two resulting states should be equal *)
    Lemma amm_transition_deterministic :
    forall (chain : Chain)
           (ctx : ContractCallContext)
           (state : State)
           (params : swap_param)
           (state' state'' : State),
      swap_exact_eth_for_tokens chain ctx state params = Ok state' ->
      swap_exact_eth_for_tokens chain ctx state params = Ok state'' ->
      state' = state''.
  Proof.
    intros.
    unfold swap_exact_eth_for_tokens in *.
    destruct state.
    simpl in *.
    inversion H.
    inversion H0.
    subst.
    Admitted.

End Theories.