(** * Inlining pass on the Template Coq representation  *)

(** Essentially, just an adaptaion of the inlining pass on the erased representation.
 After the pass is applied we generate proofs that the original and the transformed terms are equal in the theory of Coq. The proofs are just by [eq_refl], since the terms are convertible *)

From Coq Require Import List String Bool Basics.

From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CertifyingBeta.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import Certifying.

From MetaCoq.Template Require Import All Kernames.

Import ListNotations.
Import MonadNotation.

Section inlining.
  Context (should_inline : kername -> bool).
  Context (Σ : global_env).

  Definition inline_const (kn : kername) (u : Instance.t) (args : list term) : term :=
    let const := tConst kn u in
    match lookup_env Σ kn with
    | Some (ConstantDecl cst) =>
      match cst_body cst with
      | Some body (* once told me *) =>
        (* Often the first beta will expose an iota (record projection),
               and the projected field is often a function, so we do another beta *)
        let (hd, args) := decompose_app (beta_body body args) in
        beta_body (iota_body hd) args
      | None => tApp const args
      end
    | _ => tApp const args
    end.

  Fixpoint inline_aux (args : list term) (t : term) : term :=
    match t with
    | tApp hd args0 => inline_aux (map (inline_aux []) args0 ++ args) hd
    | tCast t0 _ _ =>
      (* NOTE: removing casts leads to producing more definitions at the proof
         generation phase, even for the cases when there isn't anything to
         inline, because the structure of the term has changed.
         We cannot determine at this point if we should inline something or
         nothing at all, since [should_inline] is a function*)
      inline_aux args t0
    | tConst kn u =>
      if should_inline kn then
        match lookup_env Σ kn with
        | Some (ConstantDecl cst) =>
          match cst_body cst with
          | Some body (* once told me *) =>
            let (hd, args) := decompose_app (beta_body body args) in
          (* NOTE: Often the first beta will expose an iota (record projection),
             and the projected field is often a function, so we do another beta *)
            let res := beta_body (iota_body hd) args in
          (* NOTE: after we beta-reduced the function coming from projection,
             it might intorduce new redexes. This is often the case when using
             option monads. Therefore, we do a pass that find the redexes and
             beta-reduces them further. *)
            betared res
          | None => mkApps (tConst kn u) args
          end
        | _ => mkApps (tConst kn u) args
        end
      else
        mkApps (tConst kn u) args
    | t => mkApps (map_subterms (inline_aux []) t) args
    end.

  Definition inline : term -> term := inline_aux [].

  Definition inline_in_constant_body cst :=
    {| cst_type := inline (cst_type cst);
       cst_universes := cst_universes cst;
       cst_body := option_map inline (cst_body cst) |}.

  Definition inline_oib (oib : one_inductive_body) :=
    {| ind_name := oib.(ind_name);
       ind_type := inline oib.(ind_type);
       ind_kelim := oib.(ind_kelim);
       ind_ctors := map (fun '(c_nm,c_ty,i) => (c_nm, inline c_ty,i)) oib.(ind_ctors);
       ind_projs := map (fun '(p_nm, p_ty) => (p_nm, inline p_ty)) oib.(ind_projs);
       ind_relevance := oib.(ind_relevance) |}.

  Definition inline_context_decl (cd : context_decl) : context_decl :=
    {| decl_name := cd.(decl_name);
       decl_body := option_map inline cd.(decl_body);
       decl_type := cd.(decl_type) |}.

  Definition inline_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (inline_in_constant_body cst)
    | InductiveDecl mib =>
      InductiveDecl
        {| ind_finite := mib.(ind_finite);
           ind_npars := mib.(ind_npars);
           ind_params :=map inline_context_decl mib.(ind_params);
           ind_bodies := map inline_oib mib.(ind_bodies);
           ind_universes := mib.(ind_universes);
           ind_variance := mib.(ind_variance) |}
    end.

End inlining.


Definition inline_in_env (should_inline : kername -> bool) (Σ : global_env) : global_env:=
  let newΣ :=
      fold_right (fun '(kn, decl) Σ => (kn, inline_in_decl should_inline Σ decl) :: Σ) [] Σ in
  filter (fun '(kn, _) => negb (should_inline kn)) newΣ.


Definition inline_global_env_template
           (mpath : modpath)
           (Σ : global_env)
           (should_inline : kername -> bool)
           (seeds : KernameSet.t)
  : TemplateMonad global_env :=
  let suffix := "_after_inlining" in
  Σinlined <- tmEval lazy (inline_in_env should_inline Σ);;
  gen_defs_and_proofs Σ Σinlined mpath suffix seeds;;
  ret Σinlined.

(* Mainly for testing purposes *)
Definition inline_def {A}
           (should_inline : kername -> bool)
           (def : A) : TemplateMonad _ :=
  mpath <- tmCurrentModPath tt;;
  p <- tmQuoteRecTransp def false ;;
  kn <- Common.extract_def_name def ;;
  inline_global_env_template mpath p.1 should_inline (KernameSet.singleton kn).


Definition template_inline (should_inline : kername -> bool): TemplateTransform :=
  fun Σ => Ok (timed "Inlining" (fun _ => inline_in_env should_inline Σ)).

Module Tests.

  (* Inlining into the local *)
  Module Ex1.
    Definition foo : nat -> nat := fun x => x + 1.
    Definition bar : nat -> nat := fun x => foo (x * 2).

    Definition baz : nat -> nat := fun x => foo x + bar x.

    MetaCoq Run (env <- inline_def (fun kn => eq_kername <%% foo %%> kn
                                          ||  eq_kername <%% bar %%> kn)
                                  baz ;;
                 t <- tmEval lazy (map (Basics.compose snd fst) env);;
                 tmPrint t).
  End Ex1.

  (* Inlining into the definition from the standard library *)
  Module Ex2.
    MetaCoq Run (inline_def (fun kn => eq_kername <%% Nat.add %%> kn ) mult).
  End Ex2.

  (* Inlining a function of several arguments  *)
  Module Ex3.

    Definition foo : nat -> nat -> nat -> nat := fun x y z => x + y * z.
    Definition bar : nat -> nat := fun n => foo (n + 1) 1 n.

    Definition baz : nat -> nat := fun z => bar z.
    MetaCoq Run (inline_def (fun kn => eq_kername <%% foo %%> kn ||
                eq_kername <%% bar %%> kn) baz).
  End Ex3.

  (* Records *)
  Module Ex4.

    Set Primitive Projections.
    Record blah :=
      { field1 : nat;
        field2 : nat }.

    Definition set_field1 (b : blah) (n : nat) :=
      {| field1 := n; field2 := b.(field2) |}.

    Definition bar (b : blah ):= set_field1 b 0.

    MetaCoq Run (inline_def (fun kn => eq_kername <%% set_field1 %%> kn) bar).
  End Ex4.

  (* Casts *)
  Module Ex5.
    Definition foo : nat -> nat -> nat := fun x y => x + y.
    Definition bar : nat -> nat := fun x => ((foo (x * 2)) : nat -> nat) x.
    MetaCoq Run (inline_def (fun kn => eq_kername <%% foo %%> kn) bar).
  End Ex5.

  (* Inlining type aliases in inductives *)
  Module Ex6.

    Definition my_prod (A B : Type) : Type := A * B.

    Inductive blah :=
    | blah_ctor : my_prod nat bool -> blah.

    Definition foo (p : my_prod nat bool) : blah := blah_ctor p.

    MetaCoq Run (inline_def (fun kn => eq_kername <%% my_prod %%> kn) foo).
  End Ex6.

End Tests.
