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
  beval st b = true <-> (bassn b) st.
Proof.
  intros b st. split; intros Hbe; unfold bassn in *; assumption.  
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false <-> ~ ((bassn b) st).
Proof.
  intros b st. split; intros Hbe. intros contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  
  unfold bassn in Hbe. destruct (beval st b) eqn: Hbeval.
  - exfalso. apply Hbe. reflexivity.
  - reflexivity.
Qed.

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

Open Scope imp_scope.
Inductive reduction_in : nat -> (com * state) -> (com * state) -> Prop :=
  | ri_refl : forall c st, reduction_in 0 (c, st) (c, st)
  | ri_step : forall c st c' st' c'' st'' n,
      c / st --c-> c' / st' ->
      reduction_in n (c', st') (c'', st'') ->
      reduction_in (S n) (c, st) (c'', st'').

Lemma reduction_in_trans : forall n1 n2 c1 st1 c2 st2 c3 st3,
  reduction_in n1 (c1, st1) (c2, st2) ->
  reduction_in n2 (c2, st2) (c3, st3) ->
  reduction_in (n1 + n2) (c1, st1) (c3, st3).
Proof.
  intros. dependent induction H; simpl in *.
  - assumption.
  - specialize (IHreduction_in c' st' c2 st2).
    destruct IHreduction_in; try reflexivity; try assumption.
    eapply ri_step. apply H. apply ri_refl.
    eapply ri_step. apply H. eapply ri_step. apply H2. assumption.
Qed.

Lemma reduction_in_multi_cstep_iff : forall c st c' st',
  c / st --c->* c' / st' <->
  exists n, reduction_in n (c, st) (c', st').
Proof.
  split; intros.
  - dependent induction H. exists 0. apply ri_refl.
    destruct y as [cy sty].
    specialize (IHmulti cy sty c' st').
    destruct IHmulti as [n IHmulti]; try reflexivity.
    exists (S n). eapply ri_step. apply H. assumption.
  - destruct H as [n H]. dependent induction H.
    apply multi_refl. eapply multi_step. apply H. apply IHreduction_in.
    reflexivity. reflexivity.
Qed.

Lemma com_if_false_rev : forall b c1 c2 st st',
  TEST b THEN c1 ELSE c2 FI / st --c->* SKIP / st' ->
  beval st b = false ->
  c2 / st --c->* SKIP / st'.
Proof.
  intros. dependent induction H.
  inversion H; subst.
  - specialize (IHmulti b' c1 c2 st st'). destruct IHmulti; try reflexivity.
    apply bstep_beval_equal in H7. rewrite <- H7. assumption.
    apply multi_refl. eapply multi_step. apply H2. apply m.
  - inversion H1.
  - apply H0.
Qed.

Lemma com_if_true_rev : forall b c1 c2 st st',
  TEST b THEN c1 ELSE c2 FI / st --c->* SKIP / st' ->
  beval st b = true ->
  c1 / st --c->* SKIP / st'.
Proof.
  intros. dependent induction H.
  inversion H; subst.
  - specialize (IHmulti b' c1 c2 st st'). destruct IHmulti; try reflexivity.
    apply bstep_beval_equal in H7. rewrite <- H7. assumption.
    apply multi_refl. eapply multi_step. apply H2. apply m.
  - apply H0.
  - inversion H1.
Qed.

Lemma com_while_false_eqst : forall b c st st',
  (WHILE b DO c END) / st --c->* SKIP / st' ->
  beval st b = false ->
  st = st'.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  assert (Hfalse := com_if_false _ _ _ _ _ H2 H0).
  inversion Hfalse; subst; try solve_by_invert. reflexivity.
Qed.

Inductive iter_count : bexp -> com -> nat -> state -> state -> Prop :=
  | ic_end : forall b c st, beval st b = false -> iter_count b c 0 st st
  | ic_step : forall b c st st' st'' n,
      beval st b = true ->
      c / st --c->* SKIP / st' ->
      iter_count b c n st' st'' ->
      iter_count b c (S n) st st''.

Lemma iter_count_split : forall b c n st st',
  iter_count b c (S n) st st' ->
  exists st'', c / st --c->* SKIP / st'' /\ iter_count b c n st'' st'.
Proof.
  intros. inversion H. subst. exists st'0. split; assumption.
Qed.

Definition step_infer {X: Type} (R: relation X) (P: X -> Prop) : Prop :=
  forall a b, P a -> R a b -> P b.

Lemma multi_infer {X: Type} (R: relation X) (P: X -> Prop) :
  step_infer R P ->
  forall a b, P a -> multi R a b -> P b.
Proof.
  unfold step_infer. intros Hstep a b HP Hmulti.
  induction Hmulti; subst; try assumption.
  assert (Hz := IHHmulti (Hstep x y HP H)). assumption.
Qed.

Lemma multi_end {X : Type} (R: relation X):
  forall (x y: X), multi R x y ->
  x = y \/ (x <> y /\ exists z, multi R x z /\ R z y).
Proof.
  intros. dependent induction H.
  - left. reflexivity.
  - destruct IHmulti as [IHmulti | [IHmulti_neq [z0 [IHmulti1 IHmulti2]]]];
    assert (Hexmid := classic (x = z)); destruct Hexmid as [Hexmid | Hexmid];
    try (left; assumption); right; split; try assumption.
    subst. exists x. split; try assumption. apply multi_refl.
    exists z0. split; try assumption. eapply multi_step. apply H. apply IHmulti1. 
Qed. 

Inductive while_succ : (com * state) -> (com * state) -> Prop :=
  | ws_self : forall b c st st', while_succ (WHILE b DO c END, st) (WHILE b DO c END, st')
  | ws_if : forall b b' c st st', 
    b / st' --b->* b' ->
    while_succ (WHILE b DO c END, st) (TEST b' THEN c;; WHILE b DO c END ELSE SKIP FI, st')
  | ws_seq : forall b c c' st st', 
    while_succ (WHILE b DO c END, st) (c' ;; WHILE b DO c END, st')
  | ws_skip : forall b c st st',
    while_succ (WHILE b DO c END, st) (SKIP, st').
  
Lemma com_while_succ : forall b c c' st st',
  (WHILE b DO c END) / st --c->* c' / st' ->
  while_succ (WHILE b DO c END, st) (c', st').
Proof.
  intros. remember (while_succ (WHILE b DO c END, st)) as Hws.
  assert (Hsi : step_infer cstep Hws). {
    unfold step_infer. intros. subst. inversion H0; subst; inversion H1; subst.
    - eapply ws_if. apply multi_refl.
    - eapply ws_if. eapply multi_trans. apply H6. eapply multi_step. apply H8. apply multi_refl.
    - eapply ws_seq.
    - eapply ws_skip.
    - eapply ws_seq.
    - eapply ws_self.
  }
  assert (Hmi := multi_infer cstep Hws Hsi).
  assert (Hst : Hws (WHILE b DO c END, st)). { subst. apply ws_self. }
  eapply Hmi. apply Hst. apply H.
Qed.

Lemma com_while_false : forall b c st st',
  (WHILE b DO c END) / st --c->* SKIP / st' ->
  beval st' b = false.
Proof.
  intros. 
  assert (Hend := multi_end cstep _ _ H).
  destruct Hend as [Hend_eq | [Hend_neq [z [Hend1 Hend2]]]]; try solve_by_invert.
  destruct z as [cz stz].
  assert (Hsucc := com_while_succ _ _ _ _ _ Hend1).
  inversion Hend2; try (subst; inversion Hsucc); subst.
  apply bmultistep_beval_equal in H1. simpl in H1. assumption.
Qed.

Definition is_seq (c : com) : bool :=
  match c with
  | CSeq _ _ => true
  | _ => false
  end.

Inductive first_iter : (com * state) -> (com * state) -> Prop :=
  | fi_while : forall b c st, first_iter (WHILE b DO c END, st) (WHILE b DO c END, st)
  | fi_if : forall b c st b', 
    b / st --b->* b'
    -> first_iter (WHILE b DO c END, st) (TEST b' THEN c;; WHILE b DO c END ELSE SKIP FI, st)
  | fi_seq : forall b c st c' st',
    beval st b = true
    -> c / st --c->* c' / st'
    -> first_iter (WHILE b DO c END, st) ((c' ;; WHILE b DO c END), st').

Definition seq_left (c : com) : com :=
  match c with
  | CSeq c1 _ => c1
  | _ => SKIP
  end.

Inductive pwhile : (com * state) -> (com * state) -> Prop :=
  | pw_firstiter : forall b c st c' st',
    ((WHILE b DO c END) / st --c->* c' / st')
    /\ first_iter (WHILE b DO c END, st) (c', st')
    -> pwhile (WHILE b DO c END, st) (c', st')
  | pw_nseq : forall b c st c' st',
    ((WHILE b DO c END) / st --c->* c' / st')
    /\ is_seq c' = false
    /\ (exists n, iter_count b c n st st')
    -> pwhile (WHILE b DO c END, st) (c', st')
  | pw_seq : forall b c st c' st', 
    ((WHILE b DO c END) / st --c->* c' / st')
    /\ is_seq c' = true
    /\ (exists st'', ( c / st'' --c->* (seq_left c') / st' /\ exists n, iter_count b c n st st'' /\ beval st'' b = true ))
    -> pwhile (WHILE b DO c END, st) (c', st').

Fixpoint com_size (c : com) : nat :=
  match c with
  | SKIP => 1
  | CAss _ _ => 1
  | CSeq c1 c2 => (com_size c1) + (com_size c2)
  | CIf _ c1 c2 => (com_size c1) + (com_size c2)
  | CWhile _ c => (com_size c)
  | CAwait _ c => (com_size c)
  | CCoroutine c1 c2 => (com_size c1) + (com_size c2)
  end.

Lemma com_size_gt_0 : forall c,
  com_size c > 0.
Proof.
  intros. induction c; simpl; lia.
Qed.

Lemma com_seq_not_nested : forall c1 c2,
  ~ (c2 = (c1 ;; c2)).
Proof.
  intros. intros contra.
  assert (Heqsize : com_size c2 = com_size (c1 ;; c2)). {
    rewrite <- contra. reflexivity.
  }
  simpl in Heqsize.
  assert (Hgt := com_size_gt_0 c2).
  assert (Hgt' := com_size_gt_0 c1).
  destruct (com_size c2) eqn: Hsize; simpl in *.
  - inversion Hgt.
  - destruct (com_size c1) eqn: Hsize'; simpl in *.
    + inversion Hgt'.
    + lia.
Qed.

Lemma com_seq_left : forall c1 c1' c2 st st',
  c1 / st --c->* c1' / st' ->
  (c1 ;; c2) / st --c->* (c1' ;; c2) / st'.
Proof.
  intros. dependent induction H. apply multi_refl.
    destruct y as [cy sty]. specialize (IHmulti cy c1' sty st').
    eapply multi_step. apply CS_SeqStep. apply H. apply IHmulti; reflexivity.
Qed.

Lemma com_while_count_rev : forall b c n st st',
  iter_count b c n st st' ->
  WHILE b DO c END / st --c->* SKIP / st'.
Proof.
  intros. dependent induction H.
  - eapply multi_step. ector.
    apply bmultistep_beval_iff in H.
    assert (Hfwd := com_if_fwd _ _ (c;; WHILE b DO c END) SKIP _ H).
    eapply multi_trans. apply Hfwd. eapply multi_step. apply CS_IfFalse.
    apply multi_refl.
  - eapply multi_step. ector.
    apply bmultistep_beval_iff in H.
    assert (Hfwd := com_if_fwd _ _ (c;; WHILE b DO c END) SKIP _ H).
    eapply multi_trans. apply Hfwd. eapply multi_step. apply CS_IfTrue.
    eapply com_seq_compose. apply H0. apply IHiter_count.
Qed.

Lemma com_while_count : forall b c st st',
  WHILE b DO c END / st --c->* SKIP / st'
  -> exists n,  iter_count b c n st st'.
Proof.
  intros. 
Admitted.


(* 2.4 iteration *)
Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} WHILE b DO c END {{P /\ ~ b}}.
Proof.
  unfold hoare_triple. intros P b c Hhoare st st' Heval HP.
  assert (Hcount := com_while_count b c st st' Heval). 
  destruct Hcount as [n Hcount].
  generalize dependent st. generalize dependent st'.
  induction n; intros.
  - inversion Hcount. subst. split; try apply bexp_eval_false; try assumption.
  - destruct (beval st b) eqn: Hb.
    + assert (Hc := iter_count_split _ _ _ _ _ Hcount).
      destruct Hc as [st'' [Hc Hcount']].
      assert (Hwhile := com_while_count_rev b c n st'' st' Hcount').
      simpl in Hhoare.
      assert (Hconj : P st /\ beval st b = true). { split; assumption. }
      assert (HPst'' := Hhoare _ _ Hc  Hconj).
      assert (IHn' := IHn _ _ Hwhile HPst'' Hcount').
      assumption.
    + inversion Heval. subst. inversion H. subst.
      assert (Hfalse := com_if_false_rev _ _ _ _ _ H0 Hb).
      inversion Hfalse; subst; try solve_by_invert.
      apply bexp_eval_false in Hb. split; assumption.
Qed.

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