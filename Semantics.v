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
Require Import Parallel.Tactics.
Require Import Parallel.State.

(* ======================================= *)

(* Language Definitions *)

(* ======================================= *)

(* some frequently used vars *)
(* X, Y, Z, W, A, B, C, I, J *)

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition W : string := "W".
Definition A : string := "A".
Definition B : string := "B".
Definition C : string := "C".
Definition I : string := "I".
Definition J : string := "J".

(* var *)

Inductive var : Type :=
  | V_Str : string -> var
  | V_ArrNat : string -> nat -> var      (* array of const offset *)
  | V_ArrVar : string -> string -> var.  (* array of variable offset *)

Declare Scope imp_scope.

Coercion V_Str : string >-> var.
Notation "x '[' n ']_n'" := (V_ArrNat x n) (at level 30) : imp_scope.
Notation "x '[' y ']_s'" := (V_ArrVar x y) (at level 30) : imp_scope.

(* aexp *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | AMod (a1 a2 : aexp).

(* bexp *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BLt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* com with simplest parallel *)

Inductive com : Type :=
  | CSkip
  | CAss (x : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CAwait (b : bexp) (c : com)
  | CCoroutine (c1 c2 : com).

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Bind Scope imp_scope with com.
Delimit Scope imp_scope with imp.

(* Notations *)
Coercion AId : var >-> aexp.
Coercion ANum : nat >-> aexp.
Notation "a '+' b" := (APlus a b) (at level 50, left associativity) : imp_scope.
Notation "a '-' b" := (AMinus a b) (at level 50, left associativity) : imp_scope.
Notation "a '*' b" := (AMult a b) (at level 40, left associativity) : imp_scope.
Notation "a '\' b" := (AMod a b) (at level 40, left associativity) : imp_scope.

(* Notations *)
Definition bexp_of_bool (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bexp_of_bool : bool >-> bexp.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x < y" := (BLt x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.
Notation "'AWAIT' b 'DO' c 'END'" :=
  (CAwait b c) (at level 80, right associativity) : imp_scope.
Notation "'COBEGIN' c1 '//' c2 'COEND'" :=
  (CCoroutine c1 c2) (at level 80, right associativity) : imp_scope.

Definition relation (X : Type) := X -> X -> Prop.
Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

(* small-step semantics for aexp *)

Reserved Notation " t '/' st '--a->' t' "
                  (at level 40, st at level 39).

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_IdStr : forall st i,
      AId (V_Str i) / st --a-> ANum (st i)
  | AS_IdArrNat : forall st i n,
      AId (V_ArrNat i n) / st --a-> ANum (st (i, Some n))
  | AS_IdArrVar : forall st i j,
      AId (V_ArrVar i j) / st --a-> ANum (st (i, Some (st j)))
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st --a-> a1' ->
      (APlus a1 a2) / st --a-> (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st --a-> a2' ->
      (APlus v1 a2) / st --a-> (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st --a-> ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st --a-> a1' ->
      (AMinus a1 a2) / st --a-> (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st --a-> a2' ->
      (AMinus v1 a2) / st --a-> (AMinus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st --a-> (ANum (minus n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st --a-> a1' ->
      (AMult a1 a2) / st --a-> (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st --a-> a2' ->
      (AMult v1 a2) / st --a-> (AMult v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st --a-> (ANum (mult n1 n2))
  | AS_Mod1 : forall st a1 a1' a2,
      a1 / st --a-> a1' ->
      (AMod a1 a2) / st --a-> (AMod a1' a2)
  | AS_Mod2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st --a-> a2' ->
      (AMod v1 a2) / st --a-> (AMod v1 a2')
  | AS_Mod : forall st n1 n2,
      (AMod (ANum n1) (ANum n2)) / st --a-> (ANum (n1 mod n2))

    where " t '/' st '--a->' t' " := (astep st t t') : imp_scope.
  
Notation " t '/' st '--a->*' t' " := (multi (astep st) t t') : imp_scope.
Bind Scope imp_scope with astep.

(* small-step semantics for bexp *)

Reserved Notation " t '/' st '--b->' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st --a-> a1' ->
    (BEq a1 a2) / st --b-> (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st --a-> a2' ->
    (BEq v1 a2) / st --b-> (BEq v1 a2')
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st --b->
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LeEq1 : forall st a1 a1' a2,
    a1 / st --a-> a1' ->
    (BLe a1 a2) / st --b-> (BLe a1' a2)
| BS_LeEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st --a-> a2' ->
    (BLe v1 a2) / st --b-> (BLe v1 a2')
| BS_LeEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st --b->
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st --a-> a1' ->
    (BLt a1 a2) / st --b-> (BLt a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st --a-> a2' ->
    (BLt v1 a2) / st --b-> (BLt v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLt (ANum n1) (ANum n2)) / st --b->
             (if (n1 <? n2) then BTrue else BFalse)
| BS_NotStep : forall st b1 b1',
    b1 / st --b-> b1' ->
    (BNot b1) / st --b-> (BNot b1')
| BS_NotTrue : forall st,
    (BNot BTrue) / st --b-> BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st --b-> BTrue
| BS_AndTrueStep : forall st b2 b2',
    b2 / st --b-> b2' ->
    (BAnd BTrue b2) / st --b-> (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    b1 / st --b-> b1' ->
    (BAnd b1 b2) / st --b-> (BAnd b1' b2)
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st --b-> BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st --b-> BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st --b-> BFalse

where " t '/' st '--b->' t' " := (bstep st t t') : imp_scope.

Notation " t '/' st '--b->*' t' " := (multi (bstep st) t t') : imp_scope.

Bind Scope imp_scope with bexp.

(* small-step semantics for com *)

(* first define big-step semantics for com without AWAIT and COBEGIN *)

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId v => match v with
            | V_Str s => st s
            | V_ArrNat s n => st (s, Some n)
            | V_ArrVar s v => st (s, Some (st v))
            end
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  | AMod a1 a2 => (aeval st a1) mod (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BLt a1 a2   => (aeval st a1) <? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Definition asgn_state (st : state) (v : var) (n : nat) : state :=
  match v with
  | V_Str s => (s !-> n ; st)
  | V_ArrNat s m => ((s, Some m) !-> n ; st)
  | V_ArrVar s x => ((s, Some (st x)) !-> n ; st)
  end.

Open Scope imp_scope.
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_AssStr  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> asgn_state st x n
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Reserved Notation " t '/' st '--c->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st --a-> a' ->
      (i ::= a) / st --c-> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --c-> SKIP / (asgn_state st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --c-> c1' / st' ->
      (c1 ;; c2) / st --c-> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --c-> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st --b-> b' ->
      TEST b  THEN c1 ELSE c2 FI / st
      --c->
      (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      TEST BTrue THEN c1 ELSE c2 FI / st --c-> c1 / st
  | CS_IfFalse : forall st c1 c2,
      TEST BFalse THEN c1 ELSE c2 FI / st --c-> c2 / st
  | CS_While : forall st b c1,
      WHILE b DO c1 END / st
      --c->
      (TEST b THEN c1;; WHILE b DO c1 END ELSE SKIP FI) / st
  | CS_Await : forall st b c st',
      beval st b = true ->              (* <-- big step semantics used here *)
      st =[ c ]=> st' ->                (* <-- big step semantics used here *)
      AWAIT b DO c END / st --c-> SKIP / st'
  | CS_CoroutineL : forall st st' c1 c1' c2,
      c1 / st --c-> c1' / st' ->
      COBEGIN c1 // c2 COEND / st --c-> (COBEGIN c1' // c2 COEND) / st'
  | CS_CoroutineR : forall st st' c1 c2 c2',
      c2 / st --c-> c2' / st' ->
      COBEGIN c1 // c2 COEND / st --c-> (COBEGIN c1 // c2' COEND) / st'
  | CS_CoroutineFinish : forall st,
      COBEGIN SKIP // SKIP COEND / st --c-> SKIP / st

  where " t '/' st '--c->' t' '/' st' " := (cstep (t,st) (t',st')) : imp_scope .

Notation " t '/' st '--c->*' t' '/' st' " := (multi cstep (t,st) (t',st')) (at level 40, st at level 39, t' at level 39) : imp_scope.

Bind Scope imp_scope with cstep.

(* deterministic *)

Lemma astep_deterministic : forall a a1 a2 st,
  a / st --a-> a1 -> a / st --a-> a2 -> a1 = a2.
Proof.
  intros. generalize dependent a2. dependent induction H; intros; subst;
  try (inversion H0; subst; reflexivity);
  match goal with
  | H : ?a1 / ?st --a-> ?a1' |- _ => inversion H; clear H; subst
  end; try reflexivity; try solve_by_invert;
  try (match goal with
  | H : ?a1 / ?st --a-> ?a1' |- _ => apply IHastep in H as H_
  end; rewrite H_; reflexivity);
  try (match goal with
  | H : aval ?v |- _ => inversion H; subst
  end; solve_by_invert).
Qed.

Lemma bstep_deterministic : forall b b1 b2 st,
  b / st --b-> b1 -> b / st --b-> b2 -> b1 = b2.
Proof.
  intros. generalize dependent b2. dependent induction H; intros; subst.
  - inversion H0; subst. assert (Heq: a1' = a1'0). { eapply astep_deterministic. apply H. apply H5. } subst. reflexivity. inversion H4. subst. solve_by_invert. solve_by_invert.
  - inversion H1; subst. inversion H; subst. solve_by_invert. assert (Heq: a2'=a2'0). { eapply astep_deterministic. apply H0. apply H7. } subst. reflexivity. inversion H. subst. solve_by_invert.
  - inversion H0; subst; destruct (n1 =? n2) eqn: Heq; simpl in *; try solve_by_invert; reflexivity.
  - inversion H0; subst. assert (Heq: a1' = a1'0). { eapply astep_deterministic. apply H. apply H5. } subst. reflexivity. inversion H4. subst. solve_by_invert. solve_by_invert.
  - inversion H1; subst; try (inversion H; subst; solve_by_invert).
    assert (Heq: a2'=a2'0). { eapply astep_deterministic. apply H0. apply H7. } subst. reflexivity.
  - inversion H0; subst; destruct (n1 <=? n2) eqn: Heq; simpl in *; try solve_by_invert; reflexivity.
  - inversion H0; subst. assert (Heq: a1' = a1'0). { eapply astep_deterministic. apply H. apply H5. } subst. reflexivity. inversion H4. subst. solve_by_invert. solve_by_invert.
  - inversion H1; subst; try (inversion H; subst; solve_by_invert).
    assert (Heq: a2'=a2'0). { eapply astep_deterministic. apply H0. apply H7. } subst. reflexivity.
  - inversion H0; subst; destruct (n1 <? n2) eqn: Heq; simpl in *; try solve_by_invert; reflexivity.
  - inversion H0; subst; try (apply IHbstep in H3; subst; reflexivity); try inversion H.
  - inversion H0; subst; try solve_by_invert. reflexivity.
  - inversion H0; subst. try solve_by_invert. reflexivity.
  - inversion H0; subst; try solve_by_invert. apply IHbstep in H3. subst. reflexivity.
  - inversion H0; subst; try solve_by_invert. apply IHbstep in H5. subst. reflexivity.
  - inversion H0; subst; try solve_by_invert; try reflexivity.
  - inversion H0; subst; try solve_by_invert; try reflexivity.
  - inversion H0; subst; try solve_by_invert; try reflexivity.
Qed.

(* multistep of aexp/bexp is equivalent to aeval/beval *)

Theorem amultistep_plusL : forall st a a' b,
  a / st --a->* a' ->
  (a + b) / st --a->* (a' + b).
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Plus1. apply H. apply IHmulti.
Qed.

Theorem amultistep_plusR : forall st n b b',
  b / st --a->* b' ->
  (ANum n + b) / st --a->* (ANum n + b').
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Plus2. ector. apply H. apply IHmulti.
Qed.

Theorem amultistep_subL : forall st a a' b,
  a / st --a->* a' ->
  (a - b) / st --a->* (a' - b).
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Minus1. apply H. apply IHmulti.
Qed.

Theorem amultistep_subR : forall st n b b',
  b / st --a->* b' ->
  (ANum n - b) / st --a->* (ANum n - b').
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Minus2. ector. apply H. apply IHmulti.
Qed.

Theorem amultistep_multL : forall st a a' b,
  a / st --a->* a' ->
  (a * b) / st --a->* (a' * b).
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Mult1. apply H. apply IHmulti.
Qed.

Theorem amultistep_multR : forall st n b b',
  b / st --a->* b' ->
  (ANum n * b) / st --a->* (ANum n * b').
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Mult2. ector. apply H. apply IHmulti.
Qed.

Theorem amultistep_modL : forall st a a' b,
  a / st --a->* a' ->
  (a \ b) / st --a->* (a' \ b).
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Mod1. apply H. apply IHmulti.
Qed.

Theorem amultistep_modR : forall st n b b',
  b / st --a->* b' ->
  (ANum n \ b) / st --a->* (ANum n \ b').
Proof.
  intros.
  induction H.
  - apply multi_refl.
  - eapply multi_step. apply AS_Mod2. ector. apply H. apply IHmulti.
Qed.

Theorem aeval_amultistep : forall st a n,
  aeval st a = n -> a / st --a->* ANum n.
Proof.
  intros.
  dependent induction a; intros; subst.
  - apply multi_refl.
  - destruct x as [s | s n | s v] ; subst.
    + eapply multi_step. apply AS_IdStr. apply multi_refl.
    + eapply multi_step. apply AS_IdArrNat. apply multi_refl.
    + eapply multi_step. apply AS_IdArrVar. apply multi_refl.
  - eapply multi_trans.
    apply amultistep_plusL. apply IHa1. reflexivity.
    eapply multi_trans.
    apply amultistep_plusR. apply IHa2. reflexivity.
    eapply multi_step. apply AS_Plus. apply multi_refl.
  - eapply multi_trans.
    apply amultistep_subL. apply IHa1. reflexivity.
    eapply multi_trans.
    apply amultistep_subR. apply IHa2. reflexivity.
    eapply multi_step. apply AS_Minus. apply multi_refl.
  - eapply multi_trans.
    apply amultistep_multL. apply IHa1. reflexivity.
    eapply multi_trans.
    apply amultistep_multR. apply IHa2. reflexivity.
    eapply multi_step. apply AS_Mult. apply multi_refl.
  - eapply multi_trans.
    apply amultistep_modL. apply IHa1. reflexivity.
    eapply multi_trans.
    apply amultistep_modR. apply IHa2. reflexivity.
    eapply multi_step. apply AS_Mod. apply multi_refl.
Qed.

Lemma astep_aeval_equal : forall st a a',
  a / st --a-> a' -> aeval st a = aeval st a'.
Proof.
  intros. dependent induction H;
  try (simpl; lia); try (simpl; rewrite IHastep; reflexivity).
Qed.

Lemma amultistep_aeval_equal : forall st a a',
  a / st --a->* a' -> aeval st a = aeval st a'.
Proof.
  intros. induction H.
  - reflexivity.
  - apply astep_aeval_equal in H. rewrite H.
    apply IHmulti.
Qed.

Theorem amultistep_aeval : forall st a n,
  a / st --a->* ANum n -> aeval st a = n.
Proof.
  intros. apply amultistep_aeval_equal with (a' := ANum n).
  apply H.
Qed.

Theorem amultistep_aeval_iff : forall st a n,
  a / st --a->* ANum n <-> aeval st a = n.
Proof.
  intros. split. apply amultistep_aeval. apply aeval_amultistep.
Qed.

Lemma amultistep_com_ass_L : forall st a n i,
  a / st --a->* (ANum n) -> (i ::= a) / st --c->*  SKIP / (asgn_state st i n).
Proof.
  intros. dependent induction H. simpl.
  - eapply multi_step. apply CS_Ass. apply multi_refl.
  - eapply multi_step. eapply CS_AssStep. apply H.
    assert (H1: n = aeval st x). { symmetry. apply amultistep_aeval. eapply multi_step. apply H. assumption. }
    assert (H2: aeval st x = aeval st y).
    { apply amultistep_aeval_equal. eapply multi_step. apply H. apply multi_refl. }
    rewrite H1. rewrite H2. specialize (IHmulti (aeval st y)).
    apply IHmulti. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma amultistep_com_ass_R : forall st a n i,
  (i ::= a) / st --c->* SKIP / (asgn_state st i n) -> a / st --a->* (ANum n).
Proof.
  intros. destruct i as [i | i m | i j]; subst; unfold asgn_state in *.
  - dependent induction H. inversion H; subst.
    + specialize (IHmulti st a' n i). eapply multi_step. apply H5. eapply IHmulti; try reflexivity.
    + unfold asgn_state in *. inversion H0; try solve_by_invert.
      apply t_eq_update in H3. subst. apply multi_refl.
  - dependent induction H. inversion H; subst.
    + specialize (IHmulti st a' n i m). eapply multi_step. apply H5. eapply IHmulti; try reflexivity.
    + unfold asgn_state in *. inversion H0; try solve_by_invert.
      apply t_eq_update in H3. subst. apply multi_refl.
  - dependent induction H. inversion H; subst.
    + specialize (IHmulti st a' n i j). eapply multi_step. apply H5. eapply IHmulti; try reflexivity.
    + unfold asgn_state in *. inversion H0; try solve_by_invert.
      apply t_eq_update in H3. subst. apply multi_refl.
Qed.

Theorem amultistep_com_ass : forall st a n i,
  a / st --a->* (ANum n) <-> (i ::= a) / st --c->*  SKIP / (asgn_state st i n).
  Proof.
    split.
    - intros H. apply amultistep_com_ass_L. assumption.
    - intros H. apply amultistep_com_ass_R with (i := i). assumption.
  Qed.


Lemma com_ass_result : forall st st' a i,
  (i ::= a) / st --c->* SKIP / st' -> st' = (asgn_state st i (aeval st a)).
Proof.
  intros. dependent induction H. inversion H; subst.
  - specialize (IHmulti st st' a' i).
    apply astep_aeval_equal in H5. rewrite H5.
    eapply IHmulti; try reflexivity.
  - inversion H0; subst; try solve_by_invert. simpl. reflexivity.
Qed.

Lemma bstep_beval_equal : forall st b b',
  b / st --b-> b' -> beval st b = beval st b'.
Proof.
  intros. dependent induction H; subst; simpl; try reflexivity.
  assert (Haeq: aeval st a1 = aeval st a1'). { apply astep_aeval_equal. assumption. }
  rewrite <- Haeq. reflexivity.
  assert (Haeq: aeval st a2 = aeval st a2'). { apply astep_aeval_equal. assumption. }
  rewrite <- Haeq. reflexivity.
  destruct (n1 =? n2) eqn: Heq12; simpl; reflexivity.
  assert (Haeq: aeval st a1 = aeval st a1'). { apply astep_aeval_equal. assumption. }
  rewrite <- Haeq. reflexivity.
  assert (Haeq: aeval st a2 = aeval st a2'). { apply astep_aeval_equal. assumption. }
  rewrite <- Haeq. reflexivity.
  destruct (n1 <=? n2) eqn: Heq12; simpl; reflexivity.
  assert (Haeq: aeval st a1 = aeval st a1'). { apply astep_aeval_equal. assumption. }
  rewrite <- Haeq. reflexivity.
  assert (Haeq: aeval st a2 = aeval st a2'). { apply astep_aeval_equal. assumption. }
  rewrite <- Haeq. reflexivity.
  destruct (n1 <? n2) eqn: Heq12; simpl; reflexivity.
  rewrite IHbstep. reflexivity.
  rewrite IHbstep. reflexivity.
  rewrite IHbstep. reflexivity.
Qed.

Lemma bmultistep_beval_equal : forall st b b',
  b / st --b->* b' -> beval st b = beval st b'.
Proof.
  intros. induction H.
  - reflexivity.
  - apply bstep_beval_equal in H. rewrite H.
    apply IHmulti.
Qed.

Lemma bmultistep_aequal : forall a1 a2 st n1 n2,
  aeval st a1 = n1 -> aeval st a2 = n2 ->
  (a1 = a2) / st --b->* (BEq (ANum n1) (ANum n2)).
Proof.
  intros.
  (* too simple to prove *)
Admitted.

Lemma bmultistep_ale : forall a1 a2 st n1 n2,
  aeval st a1 = n1 -> aeval st a2 = n2 ->
  (a1 <= a2) / st --b->* (BLe (ANum n1) (ANum n2)).
Proof.
  intros.
  (* too simple to prove *)
Admitted.

Lemma bmultistep_alt : forall a1 a2 st n1 n2,
  aeval st a1 = n1 -> aeval st a2 = n2 ->
  (a1 < a2) / st --b->* (BLt (ANum n1) (ANum n2)).
Proof.
  intros.
  (* too simple to prove *)
Admitted.

Lemma bmultistep_bnot : forall b b' st,
  b / st --b->* b' -> (~ b) / st --b->* (~ b').
Proof.
  intros. dependent induction H.
  - apply multi_refl.
  - eapply multi_step. eapply BS_NotStep. apply H.
    assumption.
Qed.

Lemma bmultistep_bandleft : forall b1 b2 b1' st,
  b1 / st --b->* b1' -> (b1 && b2) / st --b->* (b1' && b2).
Proof.
  intros. dependent induction H.
  - apply multi_refl.
  - eapply multi_step. eapply BS_AndStep. apply H. apply IHmulti.
Qed.

Lemma bmultistep_bandright : forall b2 b2' st,
  b2 / st --b->* b2' -> (BTrue && b2) / st --b->* (BTrue && b2').
Proof.
  intros. dependent induction H.
  - apply multi_refl.
  - eapply multi_step. eapply BS_AndTrueStep. apply H. apply IHmulti.
Qed. 

Lemma beval_bmultistep_true : forall st b b',
  beval st b = b' -> b / st --b->* if b' then BTrue else BFalse.
Proof.
  intros. dependent induction b; subst; simpl; try reflexivity; try constructor; try inversion H.
  - assert (H2 : (a1 = a2) / st --b->* (BEq (ANum (aeval st a1)) (ANum (aeval st a2)))). { apply bmultistep_aequal. reflexivity. reflexivity. }
    eapply multi_trans. apply H2. simpl. eapply multi_step. apply BS_Eq. apply multi_refl.
  - assert (H2 : (a1 <= a2) / st --b->* (BLe (ANum (aeval st a1)) (ANum (aeval st a2)))). { apply bmultistep_ale. reflexivity. reflexivity. }
    eapply multi_trans. apply H2. simpl. eapply multi_step. apply BS_LeEq. apply multi_refl.
  - assert (H2 : (a1 < a2) / st --b->* (BLt (ANum (aeval st a1)) (ANum (aeval st a2)))). { apply bmultistep_alt. reflexivity. reflexivity. }
    eapply multi_trans. apply H2. simpl. eapply multi_step. apply BS_LtEq. apply multi_refl.
  - destruct (beval st b) eqn: Heq.
    + specialize (IHb (beval st b)). rewrite Heq in IHb. simpl in *.
      assert (H: (~ b) / st --b->* BNot (BTrue)).
      { apply bmultistep_bnot. apply IHb. reflexivity. }
      eapply multi_trans. apply H. eapply multi_step. apply BS_NotTrue.
      apply multi_refl.
    + specialize (IHb (beval st b)). rewrite Heq in IHb. simpl in *.
      assert (H: (~ b) / st --b->* BNot (BFalse)).
      { apply bmultistep_bnot. apply IHb. reflexivity. }
      eapply multi_trans. apply H. eapply multi_step. apply BS_NotFalse.
      apply multi_refl.
  - destruct (beval st b1) eqn: Heq1; simpl in *.
    + specialize (IHb1 (beval st b1)). rewrite Heq1 in IHb1. simpl in *.
      assert (H: b1 / st --b->* BTrue). { apply IHb1. reflexivity. }
      assert (H1: (b1 && b2) / st --b->* (BTrue && b2)).
      { apply bmultistep_bandleft. apply H. }
      destruct (beval st b2) eqn: Heq2; simpl in *;
      specialize (IHb2 (beval st b2)); rewrite Heq2 in IHb2; simpl in *.
      * eapply multi_trans. apply H1.
        assert (H2: (BTrue && b2) / st --b->* (BTrue && BTrue)).
        { apply bmultistep_bandright. apply IHb2. reflexivity. }
        eapply multi_trans. apply H2. simpl. eapply multi_step. apply BS_AndTrueTrue. apply multi_refl.
      * eapply multi_trans. apply H1.
        assert (H2: (BTrue && b2) / st --b->* (BTrue && BFalse)).
        { apply bmultistep_bandright. apply IHb2. reflexivity. }
        eapply multi_trans. apply H2. simpl. eapply multi_step. apply BS_AndTrueFalse. apply multi_refl.
    + specialize (IHb1 (beval st b1)). rewrite Heq1 in IHb1. simpl in *.
      assert (H: (b1 && b2) / st --b->* (BFalse && b2)).
      { apply bmultistep_bandleft. apply IHb1. reflexivity. }
      eapply multi_trans. apply H. simpl. eapply multi_step. apply BS_AndFalse. apply multi_refl.
Qed.

Theorem bmultistep_beval_iff : forall st b b',
  beval st b = b' <-> b / st --b->* if b' then BTrue else BFalse.
Proof.
  intros. split. apply beval_bmultistep_true. destruct b' eqn: eqb'.
  - apply bmultistep_beval_equal.
  - apply bmultistep_beval_equal.
Qed.

Theorem com_seq_compose : forall c1 c2 st st1 st2,
  c1 / st --c->* SKIP / st1 ->
  c2 / st1 --c->* SKIP / st2 ->
  (c1 ;; c2) / st --c->* SKIP / st2.
Proof.
  intros. dependent induction H.
  - eapply multi_step. apply CS_SeqFinish. apply H0.
  - destruct y as [cy sty]. eapply multi_step. apply CS_SeqStep. apply H.
    specialize (IHmulti cy sty st1). destruct IHmulti; try reflexivity.
    assumption. apply multi_refl. eapply multi_step. apply H2. assumption.
Qed.

Theorem com_seq_split : forall c1 c2 st st1,
  (c1 ;; c2) / st --c->* SKIP / st1 ->
  exists st', c1 / st --c->* SKIP / st' /\ c2 / st' --c->* SKIP / st1.
Proof.
  intros. dependent induction H.
  inversion H; subst.
  - specialize (IHmulti c1' c2 st' st1). destruct IHmulti; try reflexivity.
    exists x. destruct H1 as [H11 H12]. split. eapply multi_step. apply H5. apply H11. apply H12.
  - exists st. split. apply multi_refl. apply H0.
Qed.

Theorem com_if_fwd : forall b b' c1 c2 st,
  b / st --b->* b' ->
  (TEST b THEN c1 ELSE c2 FI) / st --c->* (TEST b' THEN c1 ELSE c2 FI) / st.
Proof.
  intros. dependent induction H.
  - apply multi_refl.
  - eapply multi_step. apply CS_IfStep. apply H. apply IHmulti.
Qed.

Theorem com_if_true : forall c1 c2 st st' b,
  (TEST b THEN c1 ELSE c2 FI) / st --c->* SKIP / st' ->
  beval st b = true ->
  c1 / st --c->* SKIP / st'.
Proof.
  intros. dependent induction H.
  inversion H; subst; simpl; try solve_by_invert.
  specialize (IHmulti c1 c2 st st' b'). destruct IHmulti; try reflexivity.
  apply bstep_beval_equal in H7. rewrite <- H7. assumption. apply multi_refl.
  eapply multi_step. apply H2. apply m. assumption.
Qed.

Theorem com_if_false : forall c1 c2 st st' b,
  (TEST b THEN c1 ELSE c2 FI) / st --c->* SKIP / st'->
  beval st b = false ->
  c2 / st --c->* SKIP / st'.
Proof.
  intros. dependent induction H.
  inversion H; subst; simpl; try solve_by_invert.
  specialize (IHmulti c1 c2 st st' b'). destruct IHmulti; try reflexivity.
  apply bstep_beval_equal in H7. rewrite <- H7. assumption. apply multi_refl.
  eapply multi_step. apply H2. apply m. assumption.
Qed.

Theorem com_await_right : forall c st st',
  st =[ c ]=> st' ->
  c / st --c->* SKIP / st'.
Proof.
  intros. dependent induction H.
  - apply multi_refl.
  - rewrite <- H. apply amultistep_aeval_iff in H as H1.
    apply amultistep_com_ass. rewrite <- H in H1. assumption.
  - eapply com_seq_compose. apply IHceval1. apply IHceval2.
  - apply bmultistep_beval_iff in H. eapply multi_trans.
    apply com_if_fwd. apply H.
    eapply multi_step. apply CS_IfTrue. apply IHceval.
  - apply bmultistep_beval_iff in H. eapply multi_trans.
    apply com_if_fwd. apply H.
    eapply multi_step. apply CS_IfFalse. apply IHceval.
  - eapply multi_step. ector. apply bmultistep_beval_iff in H.
    assert (Hif: (TEST b THEN c;; WHILE b DO c END ELSE SKIP FI) / st --c->* (TEST BFalse THEN c;; WHILE b DO c END ELSE SKIP FI) / st).
    { apply com_if_fwd. apply H. }
    eapply multi_trans. apply Hif. eapply multi_step. apply CS_IfFalse.
    apply multi_refl.
  - eapply multi_step. ector. apply bmultistep_beval_iff in H.
    eapply multi_trans. apply com_if_fwd with (b' := BTrue). assumption.
    eapply multi_step. apply CS_IfTrue. eapply com_seq_compose.
    apply IHceval1. apply IHceval2.
Qed.
  
Lemma cstep_ass_deterministic : forall i a st x1 x2,
  cstep ((i ::= a), st) x1 -> cstep ((i ::= a), st) x2 -> x1 = x2.
Proof.
  intros. generalize dependent x2. dependent induction H; intros; subst.
  - inversion H0; subst. assert (H6 : a'=a'0). { eapply astep_deterministic. apply H. apply H5. } subst. reflexivity. inversion H.
  - inversion H0; subst. inversion H4. reflexivity.
Qed.

Lemma com_ass_deterministic : forall st st1 st2 i a,
  (i ::= a) / st --c->* SKIP / st1 -> (i ::= a) / st --c->* SKIP / st2 -> st1 = st2.
Proof.
  intros. generalize dependent st2. dependent induction H; intros.
  inversion H1; subst.
  inversion H; subst.
  - assert (H9: y0 = (i ::= a', st)). { eapply cstep_ass_deterministic. apply H2. apply H. }
    subst. eapply IHmulti. reflexivity. reflexivity. apply H3.
  - assert (H4: y0 = (SKIP, (asgn_state st i n))). { eapply cstep_ass_deterministic. apply H2. apply H. } subst. 
    inversion H0; subst. inversion H3; subst. reflexivity. inversion H4. inversion H4.
Qed.

Close Scope imp_scope.