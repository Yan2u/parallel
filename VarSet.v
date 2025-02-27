From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import micromega.Lia.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import micromega.Lia.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Logic.FunctionalExtensionality.

Require Import MSets.
Require Import Coq.Program.Equality.
From Parallel Require Import Tactics State Semantics.

(* ======================================= *)

(* sets of variables *)

(* ======================================= *)

Module Var_Decidable <: DecidableType with Definition t := string.
  Definition t := string.
  Definition eq (x y: t) := x = y.
  Definition eqb_t := eqb_string.
  Definition eqb_t_true_iff := eqb_string_true_iff.
  Definition eqb_t_false_iff := eqb_string_false_iff.
  Lemma eq_equiv: Equivalence eq.
  Proof.
    constructor; red; unfold eq; intros; congruence. 
  Qed.
  Definition eq_dec: forall (x y: t), {eq x y} + {~eq x y}.
  Proof.
    intros. unfold t in *. destruct  (eqb_t x y) eqn:BEQ.
  - left; apply eqb_t_true_iff; auto.
  - right; apply eqb_t_false_iff; auto.
  Defined.
End Var_Decidable.

Module SS := MSetWeakList.Make(Var_Decidable).
Module SSP := MSetProperties.Properties SS.
Module SSF := MSetFacts.Facts SS.