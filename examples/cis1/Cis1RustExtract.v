From ConCert.Execution Require Import Serializable.
From ConCert.Examples.CIS1 Require Cis1wccd.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import RustExtract.
From Coq Require Import Bool.
From Coq Require Import String.
From MetaCoq.Template Require Import All.

Open Scope string.

Definition CIS1_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "cis1wccd";
     concmd_init := @ConCert.Examples.CIS1.Cis1wccd.wccd_init;
     concmd_receive := @ConCert.Examples.CIS1.Cis1wccd.wccd_receive;
     concmd_extra := []; |}.

(* NOTE: it is important to declare a priting config, otherwise MetaCoq evaluation tries to normalise a term with an unresolved instance and runs out of memory. *)
Instance RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := false |}.

Definition remap_arith : list (kername * string) := Eval compute in
  [  remap <%% Serializable.serialize %%> ""].
   
Redirect "../extraction/tests/extracted-code/concordium-extract/cis1wccd.rs"
MetaCoq Run (concordium_extraction
               CIS1_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith ++ ConcordiumRemap.remap_blockchain_consts)
                  []
                  (ConcordiumRemap.remap_blockchain_inductives
                     ++ ConcordiumRemap.remap_std_types))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).

(*
        (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith
                     ++ ConcordiumRemap.remap_blockchain_consts)
                  ConcordiumRemap.remap_inline_bool_ops
                  (ConcordiumRemap.remap_std_types
                     ++ ConcordiumRemap.remap_blockchain_inductives))
               should_inline).
*)