From Equations Require Import Equations.

Class TT (T : Type) := {

}.

Inductive Bool :=
| bTrue : Bool
| bFalse : Bool.



Derive TT for Bool.






From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import AstUtils.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.

Import MCMonadNotation.

Global Unset Asymmetric Patterns.




