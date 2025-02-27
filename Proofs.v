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

From Parallel Require Import Tactics State Semantics Hoare VarSet.

Open Scope imp_scope.

(* ======================================= *)

(* Auxiliary Variables *)

(* ======================================= *)

Fixpoint vars_aexp (e : aexp) : SS.t :=
  match e with
  | ANum _ => SS.empty
  | AId X => match X with
            | V_Str x => SS.singleton x
            | V_ArrNat x _ => SS.singleton x
            | V_ArrVar x v => SS.add x (SS.singleton v)
            end
  | APlus a1 a2 => SS.union (vars_aexp a1) (vars_aexp a2)
  | AMinus a1 a2 => SS.union (vars_aexp a1) (vars_aexp a2)
  | AMult a1 a2 => SS.union (vars_aexp a1) (vars_aexp a2)
  | AMod a1 a2 => SS.union (vars_aexp a1) (vars_aexp a2)
  end.

Fixpoint vars_bexp (b : bexp) : SS.t :=
  match b with
  | BTrue => SS.empty
  | BFalse => SS.empty
  | BEq a1 a2 => SS.union (vars_aexp a1) (vars_aexp a2)
  | BLe a1 a2 => SS.union (vars_aexp a1) (vars_aexp a2)
  | BLt a1 a2 => SS.union (vars_aexp a1) (vars_aexp a2)
  | BNot b1 => vars_bexp b1
  | BAnd b1 b2 => SS.union (vars_bexp b1) (vars_bexp b2)
  end.

Fixpoint vars_assigned (c : com) : SS.t :=
  match c with
  | SKIP => SS.empty
  | i ::= a => match i with
              | V_Str s => SS.singleton s
              | V_ArrNat s _ => SS.singleton s
              | V_ArrVar s _ => SS.singleton s
              end
  | c1 ;; c2 => SS.union (vars_assigned c1) (vars_assigned c2)
  | TEST _ THEN c1 ELSE c2 FI => SS.union (vars_assigned c1) (vars_assigned c2)
  | WHILE _ DO c END => vars_assigned c
  | AWAIT _ DO c END => vars_assigned c
  | COBEGIN c1 // c2 COEND => SS.union (vars_assigned c1) (vars_assigned c2)
  end.

Fixpoint vars_ex_assigned (c : com) : SS.t :=
  match c with
  | SKIP => SS.empty
  | i ::= a => match i with
              | V_ArrVar _ v => SS.singleton v
              | _ => SS.empty
              end
  | c1 ;; c2 => SS.union (vars_ex_assigned c1) (vars_ex_assigned c2)
  | TEST b THEN c1 ELSE c2 FI => SS.union (vars_bexp b) (SS.union (vars_ex_assigned c1) (vars_ex_assigned c2))
  | WHILE b DO c END => SS.union (vars_bexp b) (vars_ex_assigned c)
  | AWAIT b DO c END => SS.union (vars_bexp b) (vars_ex_assigned c)
  | COBEGIN c1 // c2 COEND => SS.union (vars_ex_assigned c1) (vars_ex_assigned c2)
  end.

Function aux_vars (prog : com) := SS.diff (vars_assigned prog) (vars_ex_assigned prog).

Example program1 : com :=
  X ::= 1 ;;
  Y ::= 2 ;;
  COBEGIN
    AWAIT X = 1 DO (Z ::= X + 1 ;; X ::= X + 1) END
    //
    AWAIT X = 2 DO (W ::= Z + 1 ;; Y ::= Y + 1) END
  COEND.

Compute SS.elements (aux_vars program1).

Fixpoint del_auxvars_ass (pro : com) (av : SS.t) : com :=
  match pro with
  | SKIP => SKIP
  | i ::= a => let name := match i with
                | V_Str s => s
                | V_ArrNat s _ => s
                | V_ArrVar s _ => s
                end in if SS.mem name av then SKIP else (i ::= a)
  | pc1 ;; pc2 => (del_auxvars_ass pc1 av) ;; (del_auxvars_ass pc2 av)
  | TEST b THEN c1 ELSE c2 FI => TEST b THEN (del_auxvars_ass c1 av) ELSE (del_auxvars_ass c2 av) FI
  | WHILE b DO c END => WHILE b DO (del_auxvars_ass c av) END
  | AWAIT b DO c END => AWAIT b DO (del_auxvars_ass c av) END
  | COBEGIN c1 // c2 COEND => COBEGIN (del_auxvars_ass c1 av) // (del_auxvars_ass c2 av) COEND
  end.

Compute (del_auxvars_ass program1 (aux_vars program1)).

(* aux variables transformation *)

Definition assertion_irrelevant (P : Assertion) (i : addr) : Prop :=
  forall st n, P st <-> P (i !-> n; st).
  

Theorem aux_vars_transformation : forall P c c' Q av,
  av = aux_vars c ->
  c' = del_auxvars_ass c av ->
  (forall x, SS.In x av -> assertion_irrelevant P x) ->
  (forall x, SS.In x av -> assertion_irrelevant Q x) ->
  {{ P }} c' {{Q}} ->
  {{ P }} c {{ Q }}.
Proof.
  Admitted.

Close Scope imp_scope.

Open Scope dcom_scope.
Example dec_4_1 : decorated :=
  {{ X = 0 }}
  COBEGIN
    {{ X = 0 }}
    ->> {{ X = 0 \/ X = 2}}
    AWAIT true DO 
    {{ X = 0 \/ X = 2}}
    X ::= X + 1
    {{ X = 1 \/ X = 3 }}
    END
    {{ X = 1 \/ X = 3 }}
    //
    {{ X = 0 }}
    ->> {{ X = 0 \/ X = 1 }}
    AWAIT true DO
    {{ X = 0 \/ X = 1 }}
    X ::= X + 2
    {{ X = 2 \/ X = 3 }}
    END
    {{ X = 2 \/ X = 3 }}
  COEND
  {{ (X = 1 \/ X = 3) /\ (X = 2 \/ X = 3) }}
  ->> {{ X = 3 }}.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Tactic Notation "verify" := 
    repeat split;
  simpl; unfold assert_implies;
  unfold ap in *; unfold ap2 in *; unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq; [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try lia.

Definition assertion_invariant (P : Assertion) (s : com) (pre_s : Assertion) :=
  {{P /\ pre_s}} s {{P}}.

Fixpoint not_interfere_foreach (pre_s: Assertion) (s: dcom) (t : com) (pre_t : Assertion) :=
  match s with
  | DCSkip _ => assertion_invariant pre_s t pre_t
  | DCSeq d1 d2 => (not_interfere_foreach pre_s d1 t pre_t) /\ (not_interfere_foreach (post d1) d2 t pre_t)
  | DCAsgn _ _ _ => assertion_invariant pre_s t pre_t
  | DCIf _ _ _ _ _ _ => assertion_invariant pre_s t pre_t
  | DCWhile _ _ _ _ => assertion_invariant pre_s t pre_t
  | DCAwait _ _ _ _ => assertion_invariant pre_s t pre_t
  | DCPar P1 d1 P2 d2 _ => (not_interfere_foreach P1 d1 t pre_t) /\ (not_interfere_foreach P2 d2 t pre_t)
  | DCPre ass dpost => not_interfere_foreach ass dpost t pre_t
  | DCPost dpre _ => not_interfere_foreach pre_s dpre t pre_t
  end.

Definition not_interfere (pre_s: Assertion) (s: dcom) (post_s: Assertion) (t : com) (pre_t : Assertion) :=
  (assertion_invariant post_s t pre_t) /\ (not_interfere_foreach pre_s s t pre_t).

Definition not_interfere_dec (s: decorated) (t : com) (pre_t : Assertion) :=
  match s with
  | Decorated pre_s s => not_interfere pre_s s (post s) t pre_t
  end.

Fixpoint interference_free_foreach (t: dcom) (pre_t: Assertion) (s: decorated) :=
  match t with
  | DCSkip _ => True
  | DCSeq d1 d2 => (interference_free_foreach d1 pre_t s) /\ (interference_free_foreach d2 (post d1) s)
  | DCAsgn i a _ => not_interfere_dec s (i ::= a) pre_t
  | DCIf _ P1 d1 P2 d2 _ => (interference_free_foreach d1 P1 s) /\ (interference_free_foreach d2 P2 s)
  | DCWhile _ P d _ => (interference_free_foreach d P s)
  | DCAwait b P d _ => not_interfere_dec s (AWAIT b DO (extract d) END) P
  | DCPar P1 d1 P2 d2 _ => (interference_free_foreach d1 P1 s) /\ (interference_free_foreach d2 P2 s)
  | DCPre ass dpost => interference_free_foreach dpost ass s
  | DCPost dpre _ => interference_free_foreach dpre pre_t s
  end.

(* Definition : dec1 is not interfering with dec2 *)
Definition interference_free (dec1 dec2: decorated) :=
  match dec1 with 
  | Decorated pre1 s1 => interference_free_foreach s1 pre1 dec2
  end.

(* Definition : valid cobegin statements are mutually interference-free *)
Fixpoint valid_concurrent (d : dcom) :=
  match d with
  | DCSkip _ => True
  | DCSeq d1 d2 => (valid_concurrent d1) /\ (valid_concurrent d2)
  | DCAsgn _ _ _ => True
  | DCIf _ _ d1 _ d2 _ => (valid_concurrent d1) /\ (valid_concurrent d2)
  | DCWhile _ _ t _ => valid_concurrent t
  | DCAwait _ _ _ _ => True
  | DCPar P1 d1 P2 d2 _ => (interference_free ({{P1}} d1) ({{P2}} d2)) /\ (interference_free ({{P2}} d2) ({{P1}} d1))
  | DCPre _ dpost => valid_concurrent dpost
  | DCPost dpre _ => valid_concurrent dpre
  end.

Definition valid_concurrent_dec (d : decorated) :=
  match d with
  | Decorated _ d => valid_concurrent d
  end.

(* ======================================= *)

(* Proof of (4.1) *)

(* ======================================= *)

Example dec_4_1_left :=
  {{X=0}}
  ->> {{X=0\/X=2}}
  AWAIT true DO
  {{X=0\/X=2}}
  X::=X+1
  {{X=1\/X=3}}
  END
  {{X=1\/X=3}}.

Example dec_4_1_right :=
  {{X=0}}
  ->> {{X=0\/X=1}}
  AWAIT true DO
  {{X=0\/X=1}}
  X::=X+2
  {{X=2\/X=3}}
  END
  {{X=2\/X=3}}.

Example dec_4_1_inference_free_lr : interference_free dec_4_1_left dec_4_1_right.
Proof.
  simpl; unfold not_interfere; simpl;
  unfold assertion_invariant in *; simpl;
  split.
  - apply hoare_await.
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub. unfold assert_implies. intros.
    destruct H as [[H1 H2] H3].
    assert (HeqX: st X = 2).
    { destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2]; try assumption. rewrite H1. congruence. }
    simpl. rewrite HeqX. right. rewrite t_update_eq. reflexivity.
  - apply hoare_await.
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub. unfold assert_implies. intros.
    destruct H as [[H1 H2] H3].
    assert (HeqX: st X =0).
    { destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2]; try assumption. rewrite H1. congruence. }
    simpl. rewrite HeqX. right. rewrite t_update_eq. reflexivity.
Qed.

Example dec_4_1_inference_free_rl : interference_free dec_4_1_right dec_4_1_left.
Proof.
  simpl. unfold not_interfere. simpl.
  unfold assertion_invariant. simpl. split.
  - apply hoare_await.
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub. unfold assert_implies. intros.
    destruct H as [[H1 H2] H3].
    assert (HeqX: st X = 1).
    { destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2]; try assumption. rewrite H1. congruence. }
    simpl. rewrite HeqX. right. rewrite t_update_eq. reflexivity.
  - apply hoare_await.
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub. unfold assert_implies. intros.
    destruct H as [[H1 H2] H3].
    assert (HeqX: st X =0).
    { destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2]; try assumption. rewrite H1. congruence. }
    simpl. rewrite HeqX. right. rewrite t_update_eq. reflexivity.
Qed.

Example dec_4_1_valid_concurrent : valid_concurrent_dec dec_4_1.
Proof.
  unfold valid_concurrent_dec. unfold valid_concurrent. unfold dec_4_1.
  split.
  - apply dec_4_1_inference_free_lr.
  - apply dec_4_1_inference_free_rl.
Qed.

Close Scope dcom_scope.

Module Proof_4_2.

Definition i := "i"%string.
Definition j := "j"%string.
Definition k := "j"%string.
Definition x := "x"%string.
Definition eventop := "eventop"%string.
Definition oddtop := "oddtop"%string.

Definition ES_ (i : addr) (M : nat) (odt evt : addr) : Assertion :=
  fun st => ( (st evt) <= M + 1) /\ (forall (l: nat), (even l = true /\ 0 < l /\ l < (st i)) -> (st (x, Some l)) <= 0) /\ (even (st i) = true)
  /\ ((st evt) <= M -> st (x, Some (st evt)) > 0).

Definition OS_ (j : addr) (M : nat) (odt evt : addr) : Assertion :=
  fun st => ( (st odt) <= M + 1) /\ (forall (l: nat), (odd l = true /\ 0 < l /\ l < (st j)) -> (st (x, Some l)) <= 0) /\ (odd ( st j) = true) /\ ((st odt) <= M -> st (x, Some (st odt)) > 0).

Definition ES (i : addr) (M : nat) := (ES_ i M oddtop eventop).
Definition OS (j : addr) (M : nat) := (OS_ j M oddtop eventop).

Open Scope imp_scope.
Open Scope dcom_scope.

Definition findpos_M_even (M: nat) : dcom :=
  WHILE (i < oddtop) && (i < eventop) DO
      {{ (ES i M) /\ i < oddtop /\ i < eventop }}
      TEST 0 < x[i]_s THEN
        {{ (ES i M) /\ i < oddtop /\ i < eventop /\ 0 < x[i]_s }}
        ->> {{ (ES i M) /\ i < (M + 1) /\ i < eventop /\ 0 < x[i]_s }}
          eventop ::= i
          {{ (ES i M) }}
      ELSE
        {{ (ES i M) /\ i < oddtop /\ i < eventop /\ x[i]_s <= 0 }}
        i ::= (i + 2)
        {{ (ES i M) }}
      FI
      {{ (ES i M) }}
    END
    {{ (ES i M) /\ (oddtop <= i \/ eventop <= i) }}.

Definition findpos_M_odd (M : nat) : dcom :=
  WHILE (j < oddtop) && (j < eventop) DO
      {{ (OS j M) /\ j < oddtop /\ j < eventop }}
      TEST 0 < x[j]_s THEN
        {{ (OS j M) /\ j < oddtop /\ j < eventop /\ 0 < x[j]_s }}
        ->> {{ (OS j M) /\ j < (M + 1) /\ j < oddtop /\ 0 < x[j]_s }}
          oddtop ::= j
          {{ (OS j M) }}
      ELSE
        {{ (OS j M) /\ j < oddtop /\ j < eventop /\ x[j]_s <= 0 }}
        j ::= (j + 2)
        {{ (OS j M) }}
      FI
      {{ (OS j M) }}
    END
    {{ (OS j M) /\ (oddtop <= j \/ eventop <= j) }}.

Close Scope imp_scope.

Ltac destruct_conj H :=
  match type of H with
  | _ /\ _ => let H1 := fresh H in 
              let H2 := fresh H in 
              destruct H as [H1 H2]; destruct_conj H1; destruct_conj H2
  | _ => idtac
  end.

Ltac destruct_conj_all := 
      match goal with
      | [ H : ?A /\ ?B |- _ ] => destruct_conj H
      | _ => fail "no matches found"
      end.

Theorem findpos_M_interference_free_lr : forall m, 
  interference_free 
    ({{ (ES i m) }} (findpos_M_even m))
    ({{ (OS j m) }} (findpos_M_odd m)).
Proof.
  intros. unfold findpos_M_even. unfold findpos_M_odd.
  simpl. unfold not_interfere. simpl.
  unfold assertion_invariant. simpl. unfold ES. unfold OS. unfold ES_. unfold OS_.
  repeat split; simpl in *; destruct_conj_all;
  try ( 
    apply com_ass_result in H; simpl in *; rewrite H in *;
    repeat (rewrite t_update_neq in *; try discriminate); assumption
  ).
  apply com_ass_result in H; simpl in *; rewrite H in *.
  destruct H3 as [H3 | H3].
  - left. repeat (rewrite t_update_neq in *; try discriminate). assumption.
  - right. rewrite t_update_eq. repeat (rewrite t_update_neq in *; try discriminate).
    apply Nat.lt_le_incl. eapply Nat.lt_le_trans. apply H7. apply H3.
Qed.

Theorem findpos_M_interference_free_rl : forall m, 
  interference_free
    ({{ (OS j m) }} (findpos_M_odd m))
    ({{ (ES i m) }} (findpos_M_even m)).
Proof.
  intros. unfold findpos_M_even. unfold findpos_M_odd.
  simpl. unfold not_interfere. simpl.
  unfold assertion_invariant. simpl. unfold ES. unfold OS. unfold ES_. unfold OS_.
  repeat split; simpl in *; destruct_conj_all;
  try ( 
    apply com_ass_result in H; simpl in *; rewrite H in *;
    repeat (rewrite t_update_neq in *; try discriminate); assumption
  ).
  apply com_ass_result in H; simpl in *; rewrite H in *.
  destruct H3 as [H3 | H3].
  - left. rewrite t_update_eq. repeat (rewrite t_update_neq in *; try discriminate).
    apply Nat.lt_le_incl. eapply Nat.lt_le_trans. apply H7. apply H3.
  - right. repeat (rewrite t_update_neq in *; try discriminate). assumption.
Qed.

Definition findpos_M (M : nat) : decorated :=
  {{ True }}
  i ::= 2 
  {{ i = 2 }} ;;
  j ::= 1 
  {{ i = 2 /\ j = 1 }} ;;
  eventop ::= M + 1 
  {{ i = 2 /\ j = 1 /\ eventop = M + 1 }} ;;
  oddtop ::= M + 1 
  {{ i = 2 /\ j = 1 /\ eventop = M + 1 /\ oddtop = M + 1 }} 
  ->> {{ (ES i M) /\ (OS j M) }} ;;
  COBEGIN
    {{ (ES i M) }}
    (findpos_M_even M)
  //
    {{ (OS j M) }}
    (findpos_M_odd M)
  COEND
  {{ (ES i M) /\ (OS j M) /\ (oddtop <= i \/ eventop <= i) /\ (oddtop <= j \/ eventop <= j) }};;
  TEST oddtop < eventop THEN
    {{ (ES i M) /\ (OS j M) /\ (oddtop <= i \/ eventop <= i) /\ (oddtop <= j \/ eventop <= j) /\ oddtop < eventop }}
    k ::= oddtop
    {{ (ES_ i M k eventop) /\ (OS_ j M k eventop) /\ (k <= i \/ eventop <= i) /\ (k <= j \/ eventop <= j) /\ k < eventop }}
    ->> {{ fun st => (((st k) <= (M + 1))) /\ (forall (l: nat), ((0 < l) /\ (l < (st k))) -> (0 < st (x, Some l))) }}
  ELSE
    {{ (ES i M) /\ (OS j M) /\ (oddtop <= i \/ eventop <= i) /\ (oddtop <= j \/ eventop <= j) /\ eventop <= oddtop }}
    k ::= eventop
    {{ (ES_ i M oddtop k) /\ (OS_ j M oddtop k) /\ (oddtop <= i \/ k <= i) /\ (oddtop <= j \/ k <= j) /\ k < oddtop }}
    ->> {{ fun st => ((st k) <= (M + 1)) /\ (forall (l: nat), (0 < l < (st k)) -> (0 < st (x, Some l))) }}
  FI
  {{ ( fun st => ((st k) <= (M + 1)) /\ (forall (l: nat), 0 < l < (st k) -> 0 < (st (x, Some l))) ) }}.

Theorem findpos_M_valid_concurrent : forall m, valid_concurrent_dec (findpos_M m).
Proof.
  intros. unfold valid_concurrent_dec. unfold valid_concurrent. unfold findpos_M.
  repeat (split; try apply findpos_M_interference_free_lr; try apply findpos_M_interference_free_rl).
Qed.

End Proof_4_2.