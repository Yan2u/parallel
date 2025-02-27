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
Require Import Parallel.Semantics.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80).
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80).

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with ass.

Notation mkAssert P := (P%ass : Assertion).
Notation mkAexp a := (a%ass : Aexp).

Notation "~ P" := (fun st => ~ mkAssert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => mkAssert P st /\ mkAssert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => mkAssert P st \/ mkAssert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => mkAssert P st ->  mkAssert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => mkAssert P st <->  mkAssert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition bassn (b: bexp) : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.

Arguments bassn /.

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (asgn_state st X (aeval st a)).

Notation "P 'sub[' X '|->' a ']' " := (assn_sub X a P)
  (at level 10, X at next level) : assertion_scope.

  (* Hoare triple *)

Open Scope imp_scope.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       c / st --c->* SKIP / st'  ->
       P st  ->
       Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level).

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st) ) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* 2.1 null *)

Theorem hoare_skip : forall P,
  {{P}} SKIP {{P}}.
Proof.
  unfold hoare_triple in *. intros.
  inversion H; subst. assumption. solve_by_invert.
Qed.

(* 2.2 assignment *)

Theorem hoare_asgn : forall Q (X: string) a,
  {{ Q sub[ X |-> a ] }} X ::= a {{ Q }}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  apply com_ass_result in HE.
  unfold assn_sub in HQ. subst. assumption.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros P P' Q c Hhoare Himp st st' Heval HP.
  apply (Hhoare st st'). assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros P Q Q' c Hhoare Himp st st' Heval HP.
  apply Himp. apply (Hhoare st st'). assumption. assumption.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros. eapply hoare_consequence_pre. eapply hoare_consequence_post. apply H. apply H1. apply H0.
Qed.

(* 2.5 composition *)

Theorem hoare_seq : forall P Q R c1 c2,
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1 ;; c2 {{R}}.
Proof.
  unfold hoare_triple. intros P Q R c1 c2 H1 H2 st st' Heval HP.
  apply com_seq_split in Heval. destruct Heval as [st'0 [Hc1 Hc2 ]].
  apply (H2 st'0 st'). assumption. apply (H1 st st'0). assumption. assumption.
Qed.

(* 2.3 alternation *)
Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{P /\ b}} c1 {{Q}} ->
  {{P /\ ~ b}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  unfold hoare_triple in *.
  destruct (beval st b) eqn: Hb.
  - apply com_if_true in HE; try assumption. apply (HTrue st). assumption.
    split; assumption.
  - apply com_if_false in HE; try assumption. apply (HFalse st). assumption.
    split; try assumption. intros contra. simpl in contra. rewrite Hb in contra. inversion contra.
Qed.

(* 2.4 iteration *)
Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} WHILE b DO c END {{P /\ ~ b}}.
Proof.
  Admitted.

(* 3.2 await *)
Theorem hoare_await : forall P Q (b:bexp) c,
  {{P /\ b}} c {{Q}} ->
  {{P}} AWAIT b DO c END {{Q}}.
Proof.
  intros. unfold hoare_triple in *. intros st st' Heval HP.
  inversion Heval. subst. inversion H0. subst.
  inversion H1; try solve_by_invert. subst. specialize (H st st').
  apply H. apply com_await_right in H7. apply H7. split; assumption.
Qed.

Close Scope imp_scope.

(* ======================================= *)

(* Decorated Programs *)

(* ======================================= *)

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : var -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom
           -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCAwait : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPar : Assertion -> dcom -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.


  Declare Scope dcom_scope.
Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'TEST' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity)  : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity)  : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity)  : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity)  : dcom_scope.
Notation "'AWAIT' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCAwait b Pbody d Ppost)
      (at level 80, right associativity)  : dcom_scope.
Notation "'COBEGIN' {{ P1 }} d1 '//' {{ P2 }} d2 'COEND' {{ Q }}"
      := (DCPar P1 d1 P2 d2 Q)
      (at level 80, right associativity)  : dcom_scope. 
Notation "{{ P }} d"
      := (Decorated P d)
      (at level 90)  : dcom_scope.

Delimit Scope dcom_scope with dcom.
Bind Scope dcom_scope with dcom decorated.
Open Scope dcom_scope.

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ;; (extract d2) )
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => TEST b THEN (extract d1) ELSE (extract d2) FI
  | DCWhile b _ d _    => WHILE b DO (extract d) END
  | DCAwait b _ d _      => AWAIT b DO (extract d) END
  | DCPar _ d1 _ d2 _      => COBEGIN extract d1 // extract d2 COEND
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated _ d => extract d
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip Ppost            => Ppost
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCAwait b _ c Ppost       => Ppost
  | DCPar _ d1 _ d2 Ppost       => Ppost
  | DCPre _ d               => post d
  | DCPost _ Q              => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated Ppre d => Ppre
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated Ppre d => post d
  end.

Close Scope dcom_scope.