From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
#[warnings="-notation-incompatible-prefix"]
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.iTokenBuggy Require Import iTokenBuggy.

Local Open Scope string_scope.

#[export]
Instance showMsg : Show Msg :=
{|
  show m :=
    match m with
    | transfer_from from to amount =>
        "transfer_from " ++ show from ++ " " ++ show to ++ " " ++ show amount
    | approve delegate amount =>
        "approve " ++ show delegate ++ " " ++ show amount
    | mint amount => "mint " ++ show amount
    | burn amount => "burn " ++ show amount
    end
|}.

#[export]
Instance showTokenSetup : Show Setup :=
{|
  show setup := "Setup{owner: " ++ show setup.(owner) ++ sep ++
                  "init_amount: " ++ show setup.(init_amount) ++ "}"
|}.

#[export]
Instance showTokenState : Show iTokenBuggy.State :=
{|
  show s := "State{total_supply: " ++ show s.(total_supply) ++ sep
               ++ "balances: " ++ show s.(balances) ++ sep
               ++ "allowances: " ++ show s.(allowances) ++ "}"
|}.

#[export]
Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg < Msg, Setup >.
