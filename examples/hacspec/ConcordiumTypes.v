(* [[file:concordium.org::* concordium_types - Coq code][concordium_types - Coq code:1]] *)

(** This file was automatically generated using Hacspec **)
From ConCert.Examples.Hacspec Require Import HacspecLib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

(* concordium_types - Coq code:1 ends here *)

(* [[file:concordium.org::* concordium_types - Coq code][concordium_types - Coq code:2]] *)
Inductive log_error_t :=
| Full : log_error_t
| Malformed : log_error_t.

Definition eqb_log_error_t (x y : log_error_t) : bool :=
match x with
   | Full => match y with | Full=> true | _ => false end
   | Malformed => match y with | Malformed=> true | _ => false end
   end.

Definition eqb_leibniz_log_error_t (x y : log_error_t) : eqb_log_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Global Instance eq_dec_log_error_t : EqDec (log_error_t) :=
  Build_EqDec (log_error_t) (eqb_log_error_t) (eqb_leibniz_log_error_t).

(* concordium_types - Coq code:2 ends here *)

