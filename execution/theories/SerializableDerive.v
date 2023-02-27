From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import OptionMonad.
From Coq Require Import List.

Import ListNotations.


Inductive Bool :=
| _true : bool -> nat -> Bool
| _false : bool -> Bool.

Module oldLtac.
  Ltac make_serializer_case ty :=
    match ty with
    | ?T1 -> ?T2 =>
      let rest := make_serializer_case T2 in
      constr:(fun (f : SerializedValue -> SerializedValue) (v : T1) =>
                rest (fun (cur : SerializedValue) => f (serialize (v, cur))))
    | SerializedValue =>
      constr:(fun (f : SerializedValue -> SerializedValue) => f (serialize tt))
    end.

  Ltac make_serializer_aux term tag :=
    match type of term with
    | ?T1 -> (?T2 -> ?T3) =>
      let cs := make_serializer_case T1 in
      let cs := constr:(cs (fun x => serialize (tag, x))) in
      let term := (eval hnf in (term cs)) in
      make_serializer_aux term (S tag)
    | ?T -> SerializedValue =>
      term
    end.

  Ltac make_serializer eliminator :=
    let term := (eval hnf in (eliminator (fun _ => SerializedValue))) in
    let serializer := make_serializer_aux term 0 in
    eval cbn in serializer.

  Ltac make_deserializer_case ty :=
    match ty with
    | ?T1 -> ?T2 =>
      let rest := make_deserializer_case T2 in
      constr:(fun builder sv =>
                do '(a, sv) <- (deserialize sv : option (T1 * SerializedValue));
                rest (builder a) sv)
    | ?T => constr:(fun (value : T) (sv : SerializedValue) =>
                do _ <- (deserialize sv : option unit);
                Some value)
    end.

  Ltac make_deserializer_aux ctors rty :=
    match ctors with
    | (?ctor, ?tl) =>
      let ty := type of ctor in
      let cs := make_deserializer_case ty in
      let rest := make_deserializer_aux tl rty in
      constr:(
        fun tag sv =>
          match tag with
          | 0 => cs ctor sv
          | S tag => rest tag sv
          end)
    | tt => constr:(fun (tag : nat) (sv : SerializedValue) => @None rty)
    end.

  Ltac make_deserializer ctors rty :=
    let deser := make_deserializer_aux ctors rty in
    let deser := constr:(fun sv => do '(tag, sv) <- deserialize sv; deser tag sv) in
    deser.
      (* eval cbn in deser. *)

  Ltac get_ty_from_elim_ty ty :=
    match ty with
    | forall (_ : ?T -> Type), _ => T
    end.

  Ltac make_serializable eliminator ctors :=
    let ser := make_serializer eliminator in
    let elim_ty := type of eliminator in
    let ty := get_ty_from_elim_ty elim_ty in
    let deser := make_deserializer ctors ty in
    exact
      {| serialize := ser;
        deserialize := deser;
        deserialize_serialize :=
          ltac:(intros []; repeat (cbn in *; try rewrite deserialize_serialize; auto)) |}.

  Notation "'Derive' 'Serializable' rect" :=
    ltac:(make_serializable rect tt) (at level 0, rect at level 10, only parsing).

  Notation "'Derive' 'Serializable' rect < c0 , .. , cn >" :=
    (let pairs := pair c0 .. (pair cn tt) .. in
    ltac:(
      (* This matches last-to-first so it always finds 'pairs' *)
      match goal with
      | [pairs := ?x |- _] => make_serializable rect x
      end))
      (at level 0, rect at level 10, c0, cn at level 9, only parsing).

    #[local]
  Instance test : Serializable Bool := Derive Serializable Bool_rect < _true, _false >.
  (* Print test. *)
  (* MetaCoq Run (tmQuote (Derive Serializable Bool_rect < _true, _false >) >>= tmPrint). *)
End oldLtac.

Module newLtac.
  (* Check Bool_rect. *)
  (* Eval hnf in (Bool_rect (fun _ => SerializedValue)). *)

  Require Import Ltac2.Ltac2.

  Local Ltac2 rec get_constructors_fix (data : Ind.data) (n : int) : constructor list :=
    match Int.equal n 0 with
    | true => []
    | false =>
      let n' := Int.sub n 1 in
      (Ind.get_constructor data n') :: (get_constructors_fix data n')
    end.

  Local Ltac2 get_constructors (ty : constr) : constructor list :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.Ind ind _ =>
      let data := Ind.data ind in
      let n := Ind.nconstructors data in
      get_constructors_fix data n
    | _ => Control.throw (Invalid_argument
      (Some (Message.of_string "Not an inductive type")))
    end.

  Local Ltac2 make_serializer_aux a b : constr :=
    let a_ty := Constr.type a in
    a.
  (*
  Ltac make_serializer_aux term tag :=
    match type of term with
    | ?T1 -> (?T2 -> ?T3) =>
      let cs := make_serializer_case T1 in
      let cs := constr:(cs (fun x => serialize (tag, x))) in
      let term := (eval hnf in (term cs)) in
      make_serializer_aux term (S tag)
    | ?T -> SerializedValue =>
      term
    end.

  *)

  Local Ltac2 make_serializer rect : constr :=
    let term := Std.eval_hnf (rect (fun _ => constr:(SerializedValue))) in
    let serializer := make_serializer_aux term 0 in
    Std.eval_cbn {
      Std.rBeta := false;
      Std.rMatch := false;
      Std.rFix := false;
      Std.rCofix := false;
      Std.rZeta := false;
      Std.rDelta := false;
      Std.rConst := [] } serializer.

(*   Ltac2 derive_serializable (ty : constr) (rect : constr) :=
    let ctors := get_constructors ty in
    let ser := make_serializer rect in
    (* let deser := make_deserializer ctors ty in *)
    exact (True). *)
  (* exact
      {| serialize := ser;
        deserialize := deser;
        deserialize_serialize :=
          ltac:(intros []; repeat (cbn in *; try rewrite deserialize_serialize; auto)) |}. *)

  (*

  Ltac make_serializer_case ty :=
    match ty with
    | ?T1 -> ?T2 =>
      let rest := make_serializer_case T2 in
      constr:(fun (f : SerializedValue -> SerializedValue) (v : T1) =>
                rest (fun (cur : SerializedValue) => f (serialize (v, cur))))
    | SerializedValue =>
      constr:(fun (f : SerializedValue -> SerializedValue) => f (serialize tt))
    end.

  Ltac make_serializer_aux term tag :=
    match type of term with
    | ?T1 -> (?T2 -> ?T3) =>
      let cs := make_serializer_case T1 in
      let cs := constr:(cs (fun x => serialize (tag, x))) in
      let term := (eval hnf in (term cs)) in
      make_serializer_aux term (S tag)
    | ?T -> SerializedValue =>
      term
    end.
  *)
(*   Compute (
    let x := ltac2:(derive_serializable constr:(Bool) constr:(Bool_rect)) in x).
  Compute (
    let x := ltac2:(derive_serializable constr:(0)) in x). *)
End newLtac.



From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import AstUtils.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.

Import MCMonadNotation.

Global Unset Asymmetric Patterns.
Local Set Universe Polymorphism.

Definition get_inductive (T : Type) : TemplateMonad inductive := 
  Tast <- tmQuote T;;
  match Tast with
  | tInd ind _ => ret ind
  | tApp (tInd ind _) _ => ret ind
  | _ => tmFail "Cannot extract inductive, are you sure you passed a type?"
  end.

  Definition get_inductive_ (t : term) : TemplateMonad inductive := 
  match t with
  | tInd ind _ => ret ind
  | tApp (tInd ind _) _ => ret ind
  | _ => tmFail "Cannot extract inductive, are you sure you passed a type?"
  end.

Definition get_mib (ind : inductive) : TemplateMonad mutual_inductive_body :=
  tmQuoteInductive (inductive_mind ind).

Definition get_nth_oib (mib : mutual_inductive_body) (n : nat) : TemplateMonad one_inductive_body :=
  match nth_error (ind_bodies mib) n with
  | Some oib => ret oib
  | None => tmFail "Could not find inductive in mutual inductive?"
  end.

Definition get_oib (mib : mutual_inductive_body) (ind : inductive) : TemplateMonad one_inductive_body :=
  get_nth_oib mib (inductive_ind ind).

Definition get_constructors (oib : one_inductive_body) : list constructor_body :=
  ind_ctors oib.

Definition instance_exists (T : Type) : TemplateMonad unit :=
  inst <- tmInferInstance None T;;
  match inst with
  | my_Some _ _ => ret tt
  | _ => tmFail "Instance already exist"
  end.

Definition qualid_const_kername (q : qualid) : TemplateMonad kername :=
  glob_ref <- tmLocate1 q;;
  match glob_ref with
  | ConstRef kn => ret kn
  | _ => tmFail "Unexpected global_reference after unquoting"
  end.

Definition register_instance (q : qualid) : TemplateMonad unit :=
  tmLocate1 q >>= tmExistingInstance.

Definition get_rect (oib : one_inductive_body) : TemplateMonad kername :=
  let name := (ind_name oib) ^ "_rect" in
  qualid_const_kername name.



Definition make_serializer_case : TemplateMonad term :=
  todo "".
Definition make_serializer_aux : TemplateMonad term :=
  todo "".
Definition make_serializer (eliminator : kername) : TemplateMonad term :=
  todo "".

Definition deser_case_prod_body :=
  (fun (T1 T2 T : Type)
       (rest : (T2 -> T) -> SerializedValue -> option T)
       (serT1 : Serializable T1) =>
  (fun builder sv =>
              do '(a, sv) <- (@deserialize (T1 * SerializedValue) _ sv);
              rest (builder a) sv)).
Definition deser_case_ind_body :=
  (fun (T : Type) =>
  (fun (value : T) (sv : SerializedValue) =>
                match @deserialize unit _ sv with
                | Some _ => Some value
                | None => None
                end)).
              (* do _ <- (@deserialize unit _ sv); *)
              (* Some value)). *)

Fixpoint make_deserializer_case (t : term) (T : term) : TemplateMonad term :=
  match t with
  | tProd _ T1 T2 =>
      rest <- make_deserializer_case T2 T;;
      ret (tApp
        <% @deser_case_prod_body %>
        [T1; T2; T; rest; hole])
  | tRel _ =>
      ret (tApp
        <% @deser_case_ind_body %>
        [t]
      )
  | _ => 
      tmFail "err 1"
  end.

Definition deser_aux_cons_body :=
  (fun (T ctorT : Type)
       (cs : ctorT -> SerializedValue -> option T)
       (rest : nat -> SerializedValue -> option T)
       (ctor : ctorT) =>
  (fun (tag : nat) (sv : SerializedValue) =>
        match tag with
        | 0 => cs ctor sv
        | S tag => rest tag sv
        end)).
Definition deser_aux_nil_body :=
  (fun (T : Type) =>
  (fun (tag : nat) (sv : SerializedValue) => @None T)).

Fixpoint make_deserializer_aux (ctors : list constructor_body) (T : term) (i : nat) : TemplateMonad term :=
  match ctors with
  | ctor :: tl =>
    let ty := ctor.(cstr_type) in
    ind <- get_inductive_ T;;
    let ctor := (tConstruct ind i []) in
    cs <- make_deserializer_case ty T;;
    rest <- make_deserializer_aux tl T (S i);;
    ret (
      tApp
        <% deser_aux_cons_body %>
        [T; ty; cs; rest; ctor]
    )
  | [] =>
    ret (tApp <% deser_aux_nil_body %> [T])
  end.

Definition deser_body :=
  (fun (T : Type) =>
    (fun (deser : nat -> SerializedValue -> option T) =>
      (fun sv =>
        do '(tag, sv) <- @deserialize (nat * SerializedValue) _ sv;
        deser tag sv))).

Definition make_deserializer (ctors : list constructor_body) (T : Type) : TemplateMonad term :=
  tAst <- tmQuote T;;
  deser <- make_deserializer_aux ctors tAst 0;;
  let body :=
    tLambda
      {| binder_name := nNamed "sv"; binder_relevance := Relevant |}
      <% SerializedValue %>
      (tApp
        <% deser_body %>
        [tAst; deser; tRel 0]
      ) in 
  (* body <- tmEval cbv body;; *)
  ret deser.

Unset MetaCoq Strict Unquote Universe Mode.
(* Set MetaCoq Debug. *)

MetaCoq Run (
  let T := Bool in
  ind <- get_inductive T;;
  mib <- get_mib ind;;
  oib <- get_oib mib ind;;
  let ctors := get_constructors oib in
  cs <- match ctors with
  | h :: h2 :: t =>
    tAst <- tmQuote T;;
    let ty := h2.(cstr_type) in
    match ty with
    | tProd _ T1 T2 =>
        rest <- make_deserializer_case T2 tAst;;
        ret (tApp
          <% deser_case_prod_body %>
          [T1; T2; tAst; rest; hole])
    | tRel _ =>
        ret (tApp
          <% @deser_case_ind_body %>
          [tAst]
        )
    | _ => 
        tmFail "err 1"
    end
  | _ => tmFail "t"
  end;;
      (* tmPrint cs *)
    tmMkDefinition "test1" cs
  ).





  let T := Bool in
  ind <- get_inductive T;;
  mib <- get_mib ind;;
  oib <- get_oib mib ind;;
  let ctors := get_constructors oib in
  match ctors with
  | h :: h2 :: t =>
    tAst <- tmQuote T;;
    let ty := h2.(cstr_type) in
    cs <- make_deserializer_case ty tAst;;
    (* cs <- tmEval cbv cs;; *)
    (* cs <- tmEval hnf cs;; *)
    (* tmPrint cs *)
    tmMkDefinition "test1" cs
  | _ => tmFail "t"
  end).


MetaCoq Run (
  let T := Bool in
  ind <- get_inductive T;;
  mib <- get_mib ind;;
  oib <- get_oib mib ind;;
  let ctors := get_constructors oib in
  (* tmPrint ctors). *)
  body <- make_deserializer ctors T;;
  (* tmPrint body). *)
  tmMkDefinition "test1" body
).
Print test1.
Eval cbv in test1.


Program Definition make_serializable (T : Type) : TemplateMonad unit :=
  ind <- get_inductive T;;
  mib <- get_mib ind;;
  oib <- get_oib mib ind;;
  eliminator <- get_rect oib;;
  let ctors := get_constructors oib in

  ser <- make_serializer eliminator;;
  deser <- make_deserializer ctors T;;
  (* @ret _ _ _ tt. *)
  todo "".




Definition make_setters (T : Type) :=
  Tast <- tmQuote T;;
  (* ret Tast. *)
  ind <- match Tast with
      | tInd ind _ => ret ind
      | tApp (tInd ind _) _ => ret ind
      | _ => tmFail "Cannot extract inductive, are you sure you passed a type?"
      end;;
  (* ret ind. *)
  mib <- tmQuoteInductive (inductive_mind ind);;
  oib <- match nth_error (ind_bodies mib) (inductive_ind ind) with
         | Some oib => ret oib
         | None => tmFail "Could not find inductive in mutual inductive?"
         end;;
  (* ctors <- ind_ctors oib;; *)
(*   '(ctor, ar) <- match ind_ctors oib with
                 | [c] => ret (c.(cstr_type), c.(cstr_arity))
                 | _ => tmFail "Type should have exactly one constructor"
                 end;; *)
  ret (ind_ctors oib).

MetaCoq Run (x <- make_setters Bool;; tmPrint x).


Ltac make_serializer_case ty :=
  match ty with
  | ?T1 -> ?T2 =>
    let rest := make_serializer_case T2 in
    constr:(fun (f : SerializedValue -> SerializedValue) (v : T1) =>
              rest (fun (cur : SerializedValue) => f (serialize (v, cur))))
  | SerializedValue =>
    constr:(fun (f : SerializedValue -> SerializedValue) => f (serialize tt))
  end.

Ltac make_serializer_aux term tag :=
  match type of term with
  | ?T1 -> (?T2 -> ?T3) =>
    let cs := make_serializer_case T1 in
    let cs := constr:(cs (fun x => serialize (tag, x))) in
    let term := (eval hnf in (term cs)) in
    make_serializer_aux term (S tag)
  | ?T -> SerializedValue =>
    term
  end.

Ltac make_serializer eliminator :=
  let term := (eval hnf in (eliminator (fun _ => SerializedValue))) in
  let serializer := make_serializer_aux term 0 in
  eval cbn in serializer.

Ltac make_deserializer_case ty :=
  match ty with
  | ?T1 -> ?T2 =>
    let rest := make_deserializer_case T2 in
    constr:(fun builder sv =>
              do '(a, sv) <- (deserialize sv : option (T1 * SerializedValue));
              rest (builder a) sv)
  | ?T => constr:(fun (value : T) (sv : SerializedValue) =>
              do _ <- (deserialize sv : option unit);
              Some value)
  end.

Ltac make_deserializer_aux ctors rty :=
  match ctors with
  | (?ctor, ?tl) =>
    let ty := type of ctor in
    let cs := make_deserializer_case ty in
    let rest := make_deserializer_aux tl rty in
    constr:(
      fun tag sv =>
        match tag with
        | 0 => cs ctor sv
        | S tag => rest tag sv
        end)
  | tt => constr:(fun (tag : nat) (sv : SerializedValue) => @None rty)
  end.

Ltac make_deserializer ctors rty :=
  let deser := make_deserializer_aux ctors rty in
  let deser := constr:(fun sv => do '(tag, sv) <- deserialize sv; deser tag sv) in
  eval cbn in deser.

Ltac get_ty_from_elim_ty ty :=
  match ty with
  | forall (_ : ?T -> Type), _ => T
  end.

Ltac make_serializable eliminator ctors :=
  let ser := make_serializer eliminator in
  let elim_ty := type of eliminator in
  let ty := get_ty_from_elim_ty elim_ty in
  let deser := make_deserializer ctors ty in
  exact
    {| serialize := ser;
      deserialize := deser;
      deserialize_serialize :=
        ltac:(intros []; repeat (cbn in *; try rewrite deserialize_serialize; auto)) |}.

Notation "'Derive' 'Serializable' rect" :=
  ltac:(make_serializable rect tt) (at level 0, rect at level 10, only parsing).

Notation "'Derive' 'Serializable' rect < c0 , .. , cn >" :=
  (let pairs := pair c0 .. (pair cn tt) .. in
  ltac:(
    (* This matches last-to-first so it always finds 'pairs' *)
    match goal with
    | [pairs := ?x |- _] => make_serializable rect x
    end))
    (at level 0, rect at level 10, c0, cn at level 9, only parsing).