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

Import ListNotations.
Require Import MSets.
Require Import Coq.Program.Equality.

Require Import Parallel.Tactics.

(* To support arrays, we make united varable definitions *)

Definition addr : Type := (string * (option nat)).
Definition addr_of_string (s : string) : addr := (s, None).
Coercion addr_of_string : string >-> addr.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition eqb_addr (x y : addr) : bool :=
  match x , y with
  | (s1, None) , (s2, None) => eqb_string s1 s2
  | (s1, Some n1) , (s2, Some n2) => andb (eqb_string s1 s2) (n1 =? n2)
  | _ , _ => false
  end.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
   - rewrite Hs_eq. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs_not_eq. destruct Hs_not_eq. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem eqb_addr_true_iff : forall x y : addr,
    eqb_addr x y = true <-> x = y.
Proof.
  intros [x1 x2] [y1 y2].
  split; intros; unfold eqb_addr in *; 
  destruct x2 eqn: Eeqx2; destruct y2 eqn: Eeqy2; subst;
  try solve_by_invert.
  - apply andb_true_iff in H as [H1 H2]. 
    apply eqb_string_true_iff in H1. subst.
    apply Nat.eqb_eq in H2. subst. reflexivity.
  - apply eqb_string_true_iff in H. subst. reflexivity.
  - inversion H. apply andb_true_iff. split.
    apply eqb_string_true_iff. reflexivity.
    apply Nat.eqb_eq. reflexivity.
  - inversion H. apply eqb_string_true_iff. reflexivity.
Qed.

Theorem eqb_addr_false_iff : forall x y : addr,
    eqb_addr x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_addr_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Definition total_map (A : Type) := addr -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : addr) (v : A) :=
  fun x' => if eqb_addr x x' then v else m x'.

Declare Scope state_scope.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity) : state_scope.

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity) : state_scope.

Bind Scope state_scope with total_map.
Delimit Scope state_scope with state.
Open Scope state.

Lemma t_apply_empty : forall (A : Type) (x : addr) (v : A),
    (_ !-> v) x = v.
Proof.
Admitted.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
Admitted.


Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
Admitted.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
Admitted.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
Admitted.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
Admitted.

Theorem t_eq_update : forall (A : Type) (m : total_map A) x (v1 v2 : A),
  (x !-> v1; m) = (x !-> v2; m) <-> v1 = v2.
Proof.
  split; intros.
  - assert (Heq1 : (x !-> v1; m) x = v1). { rewrite t_update_eq. reflexivity. }
    assert (Heq2 : (x !-> v2; m) x = v2). { rewrite t_update_eq. reflexivity. }
    rewrite H in Heq1. rewrite Heq2 in Heq1. inversion Heq1. reflexivity.
  - rewrite H. reflexivity.
Qed. 

Definition state := total_map nat.