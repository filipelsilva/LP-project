(* ################################################################# *)
(** * Additional Properties

      It might be a good idea to read the relevant book chapters/sections before or as you
      develop your solution. The properties below are discussed and some of them proved
      for the original Imp formulation.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp Interpreter RelationalEvaluation.
Set Default Goal Selector "!".


(**
  3.2. TODO: Prove all the properties below that are stated without proof.
             Add a succint comment before each property explaining the property in your own words.
*)

(* ################################################################# *)
(** * Property of the Step-Indexed Interpreter *)

Theorem ceval_step_more: forall i1 i2 st st' res c,
i1 <= i2 ->
ceval_step st c i1 = Some (st', res) ->
ceval_step st c i2 = Some (st', res).
Proof.
  induction i1 as [|i1']; intros i2 st st' res c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2'].
    + inversion Hle.
    + assert (Hle': i1' <= i2') by lia. destruct c.
      ++ (* skip *)
         simpl in Hceval. inversion Hceval.
         reflexivity.
      ++ (* break *)
         simpl in Hceval. inversion Hceval.
         reflexivity.
      ++ (* := *)
         simpl in Hceval. inversion Hceval.
         reflexivity.
      ++ (* ; *)
         simpl in Hceval. simpl.
         destruct (ceval_step st c1 i1') eqn:Heqst1'o.
         +++ (* st1'o = Some *)
             destruct res.
             ++++ (* st1'o = Some (st, SContinue) *)
                  admit.
                  (* apply (IHi1' i2') in Heqst1'o. try assumption. *)
                  (* rewrite Heqst1'o. simpl. simpl in Hceval. *)
                  (* apply (IHi1' i2') in Hceval; try assumption. *)
             ++++ (* st1'o = Some (st, SBreak) *)
                  admit.
                  (* apply (IHi1' i2' st st' SBreak c1) in Heqst1'o. try assumption. *)
                  (* rewrite Heqst1'o. simpl. simpl in Hceval. *)
                  (* apply (IHi1' i2') in Hceval; try assumption. *)
         +++ (* st1'o = None *)
             discriminate Hceval.
      ++ (* if *)
         simpl in Hceval. simpl.
         destruct (beval st b); apply (IHi1' i2') in Hceval;
         assumption.
      ++ (* while *)
         simpl in Hceval. simpl.
         destruct (beval st b); try assumption.
         destruct (ceval_step st c i1') eqn: Heqst1'o.
         +++ (* st1'o = Some *)
             destruct res.
             ++++ (* st1'o = Some (st, SContinue) *)
                  admit.
                  (* apply (IHi1' i2') in Heqst1'o; try assumption. *)
                  (* rewrite -> Heqst1'o. simpl. simpl in Hceval. *)
                  (* apply (IHi1' i2') in Hceval; try assumption. *)
             ++++ (* st1'o = Some (st, SBreak) *)
                  admit.
                  (* apply (IHi1' i2') in Heqst1'o; try assumption. *)
                  (* rewrite -> Heqst1'o. simpl. simpl in Hceval. *)
                  (* apply (IHi1' i2') in Hceval; try assumption. *)
         +++ (* i1'o = None *)
             simpl in Hceval. discriminate Hceval.
(* Qed. *)
Admitted.

(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

Theorem ceval_step__ceval: forall c st st' res,
    (exists i, ceval_step st c i = Some (st', res)) ->
    st =[ c ]=> st' / res.
Proof.
  intros c st st' res H.
  inversion H as [i E].
  clear H.
  generalize dependent res.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

    - (* i = 0 -- contradictory *)
    intros c st st' res H. discriminate H.

  - (* i = S i' *)
    intros c st st' res H.
    destruct c; simpl in H; inversion H; subst; clear H.
      + (* skip *) apply E_Skip.
      + (* break *) apply E_Break.
      + (* := *) apply E_Asgn. reflexivity.
      + (* ; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        ++ (* Evaluation of r1 terminates normally *)
          admit.
          (* apply E_Seq_Continue with s. *)
          (*   apply IHi'. rewrite Heqr1. reflexivity. *)
          (*   apply IHi'. assumption. *)
        ++ (* Otherwise -- contradiction *)
          discriminate H1.
      + (* if *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* while *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr.

  (* - intros. inversion E. *)
  (* - intros. destruct c; simpl in E; inversion E; subst; clear E. *)
  (*   + (1* SKIP *1) apply E_Skip. *)
  (*   + (1* BREAK *1) apply E_Break. *)
  (*   + (1* ASGN *1) apply E_Asgn. reflexivity. *)
  (*   + (1* SEQ *1) remember (ceval_step st c1 i') as step1. destruct step1. *)
  (*     ++ (1* CONTINUE *1) apply E_Seq_Continue with st'; apply IHi'. *)
  (*        (1* +++ rewrite Heqstep1. *1) *)
  (*        +++ admit. *)
  (*        +++ rewrite <- H0. admit. *)
  (*     ++ (1* BREAK *1) inversion H0. *)
  (*   + (1* IF *1) remember (beval st b) as cond. destruct cond. *)
  (*     ++ (1* TRUE *1) apply (E_IfTrue st st' res b c1 c2). *)
  (*        +++ rewrite Heqcond. reflexivity. *)
  (*        +++ apply IHi'. assumption. *)
  (*     ++ (1* FALSE *1) apply (E_IfFalse st st' res b c1 c2). *)
  (*        +++ rewrite Heqcond. reflexivity. *)
  (*        +++ apply IHi'. assumption. *)
  (*   + (1* WHILE *1) remember (beval st b) as cond. destruct cond. *)
  (*     ++ (1* TRUE *1) remember (ceval_step st c i') as step. destruct step. *)
  (*        +++ admit. *)
  (*        (1* +++ (2* CONTINUE *2) apply E_WhileTrue_Continue with st'. *1) *)
  (*            (1* ++++ rewrite Heqcond. reflexivity. *1) *)
  (*            (1* ++++ apply IHi'. inversion Heqstep. admit. *1) *)
  (*            (1* ++++ apply IHi'. inversion Heqstep. admit. *1) *)
  (*        (1* +++ apply (E_WhileTrue_Continue st st st' b c). *1) *)
  (*            (1* ++++ rewrite Heqcond. reflexivity. *1) *)
  (*            (1* ++++ apply IHi'. inversion Heqstep. admit. *1) *)
  (*            (1* ++++ apply IHi'. inversion Heqstep. admit. *1) *)
  (*        +++ (1* BREAK *1) inversion H0. *)
  (*     (1* ++ (2* FALSE *2) apply E_WhileFalse. rewrite Heqcond. rewrite H1. reflexivity. *1) *)
  (*     ++ admit. *)
(* TODO *)
(* Qed. *)
Admitted.

(**
  TODO: For the following proof, you'll need [ceval_step_more] in a
  few places, as well as some basic facts about [<=] and [plus]. *)

Theorem ceval__ceval_step: forall c st st' res,
    st =[ c ]=> st' / res ->
    exists i, ceval_step st c i = Some (st', res).
Proof.
  intros.
  induction H.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.

(* Qed. *)
Admitted.



(* Note that with the above properties, we can say that both semantics are equivalent! *)

Theorem ceval_and_ceval_step_coincide: forall c st st' res,
    st =[ c ]=> st' / res
<-> exists i, ceval_step st c i = Some (st', res).
Proof.
intros c st st'.
split.
 - apply ceval__ceval_step.
 - apply ceval_step__ceval.
Qed.


(* ################################################################# *)
(** * Determinism of Evaluation Again *)

(** Using the fact that the relational and step-indexed definition of
  evaluation are the same, we can give a short proof that the
  evaluation _relation_ is deterministic. *)

(* TODO: Write/explain the following proof in natural language,
         using your own words. *)

(* Explanation:
   This proof says that for any two executions of any program with any initial
   state, if these program and initial state are the same, the final state will
   be the same.

   Proof:
   There has to exist, for each execution, a natural number i such that the
   evaluation of the program over i steps leads to some result.
   We know that for two natural numbers i1 and i2, if i1 is less than or equal
   to i2, the execution of a program over i1 steps will produce the same
   results as an execution of i2 steps over the same program.
   Therefore, we can say that the execution of a program over i1 steps
   will be the same as the execution of i1 + i2 steps over the same program.
   We will have two cases:
   - st1 = st2: to prove this, we can say that for any two numbers, the
   expression can be rewritten such that i1 <= i2, and therefore it is proven.
   - i1 <= i2: the execution of i1 steps will be the same as the execution of
   i2 steps, as said before. Proven.
 *)

Theorem ceval_deterministic' : forall c st st1 st2 res1 res2,
   st =[ c ]=> st1 / res1 ->
   st =[ c ]=> st2 / res2 ->
   st1 = st2.
Proof.
intros c st st1 st2 res1 res2 He1 He2.
apply ceval__ceval_step in He1.
apply ceval__ceval_step in He2.
inversion He1 as [i1 E1].
inversion He2 as [i2 E2].
apply ceval_step_more with (i2 := i1 + i2) in E1.
 - apply ceval_step_more with (i2 := i1 + i2) in E2.
  -- rewrite E1 in E2. inversion E2. reflexivity.
  -- lia.
 - lia.
 Qed.