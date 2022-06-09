From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Printing.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Examples.EIP20 Require Import EIP20Token.
From ConCert.Utils Require Import StringExtra.
From Coq Require Import Bool.
From Coq Require Import String.
From MetaCoq.Template Require Import All.
Open Scope string.

Definition EIP20_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "EIP20"%string;
     concmd_init := @EIP20Token.init;
     concmd_receive := @EIP20Token.receive;
     concmd_extra := []; |}.

Definition should_inline kn :=
  eq_kername kn <%% @Monads.bind %%>
  || eq_kername kn <%% Monads.Monad_option %%>
  || if String.index 0 "setter_from_getter" (string_of_kername kn) then true else false.

Definition map_find : string :=
  <$ "fn ##name##<K : 'a + Ord, V : Clone>(&'a self, key : K , m : immutable_map::TreeMap<K, V>) -> Option<V> {";
     "  match m.get(&key) {";
     "    Some(v) => Some(v.clone()),";
     "    None => None";
     "  }";
     "}" $>.

Definition map_add : string :=
  <$"fn ##name##<K : Clone + Ord, V : Clone>(&'a self, key : K, value : V, m : immutable_map::TreeMap<K, V>) -> TreeMap<K, V> {";
    "  m.insert(key,value)";
    "}"$>.

Definition map_empty : string :=
  <$ "fn ##name##<K, V> (&'a self, _ : ()) -> immutable_map::TreeMap<K, V> {";
     "  TreeMap::new()";
     "}" $>.

Definition remap_eip20token : list (kername * string) :=
  [ (<! @ContractCommon.AddressMap.add !>, map_add) ;
    (<! @ContractCommon.AddressMap.find !>, map_find) ;
    (<! @ContractCommon.AddressMap.empty !>, map_empty)
  ].

Definition remap_map : remapped_inductive :=
  {| re_ind_name := "TreeMap";
     re_ind_ctors := [];
     re_ind_match := None |}.
Definition remap_fmap :=
  [ (<! FMap !>, remap_map) ]%list.

Existing Instance DefaultPrintConfig.RustConfig.

Redirect "../extraction/tests/extracted-code/concordium-extract/eip20.rs"
MetaCoq Run (concordium_extraction
               EIP20_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith
                    ++ remap_eip20token
                    ++ ConcordiumRemap.remap_blockchain_consts)
                  ConcordiumRemap.remap_inline_bool_ops
                  (ConcordiumRemap.remap_std_types
                    ++ ConcordiumRemap.remap_blockchain_inductives
                    ++ remap_fmap))
               should_inline).

(*
Definition remap_nat : remapped_inductive:=
  {| re_ind_name := "u64";
     re_ind_ctors := ["0"; "__nat_succ"];
     re_ind_match := Some "__nat_elim!" |}.

Definition remap_positive : remapped_inductive :=
  {| re_ind_name := "u64";
     re_ind_ctors := ["__pos_onebit"; "__pos_zerobit"; "1"];
     re_ind_match := Some "__pos_elim!"
  |}.

Definition remap_Z : remapped_inductive :=
  {| re_ind_name := "i64";
     re_ind_ctors := ["0"; "__Z_frompos"; "__Z_fromneg"];
     re_ind_match := Some "__Z_elim!";
  |}.

Definition remap_bool : remapped_inductive :=
  {| re_ind_name := "bool";
     re_ind_ctors := ["true"; "false"];
     re_ind_match := None
  |}.

Definition remap_pair : remapped_inductive :=
  {| re_ind_name := "__pair";
     re_ind_ctors := ["__mk_pair"];
     re_ind_match := Some "__pair_elim!"
  |}.

Definition remap_option : remapped_inductive :=
  {| re_ind_name := "Option";
     re_ind_ctors := ["Some"; "None"];
     re_ind_match := None
  |}.

Definition remap_unit : remapped_inductive :=
  {| re_ind_name := "()";
     re_ind_ctors := ["()"];
     re_ind_match := None
  |}.

Definition remap_string : remapped_inductive :=
  {| re_ind_name := "&'a String";
     re_ind_ctors := [];
     re_ind_match := None |}.

Definition remap_std_types :=
  [ (<! nat !>, remap_nat)
  ; (<! positive !>, remap_positive)
  ; (<! Z !>,  remap_Z)
  ; (<! bool !>, remap_bool)
  ; (<! prod !>, remap_pair)
  ; (<! option !>, remap_option)
  ; (<! unit !>, remap_unit)
  ; (<! string !>, remap_string) ].

Definition remap_SerializedValue : remapped_inductive :=
  {| re_ind_name := "&'a SerializedValue<'a>";
     re_ind_ctors := ["__SerializedValue__Is__Opaque"];
     re_ind_match := None |}.

Definition remap_ActionBody : remapped_inductive :=
  {| re_ind_name := "ActionBody<'a>";
     re_ind_ctors := ["ActionBody::Transfer"; "ActionBody::Call"; "__Deploy__Is__Not__Supported"];
     re_ind_match := None |}.

Definition remap_blockchain_inductives : list (inductive * remapped_inductive) :=
  [ (<! Serializable.SerializedValue !>, remap_SerializedValue);
    (<! @ActionBody !>, remap_ActionBody) ].
*)