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
  3.2. Prove all the properties below that are stated without proof.
       Add a succint comment before each property explaining the property in your own words.
*)

(* ################################################################# *)
(** * Property of the Step-Indexed Interpreter *)

(*
   For any two natural numbers (i1, i2), two states (st, st'), result (res) and
   program (c), if i1 is less or equal to i2 and the evaluation of c with
   initial state st over i1 steps has a final state st' and a result res, then
   the evaluation of c with initial state st over i2 steps has the same final
   state and result.
   If a program acheives a certain output under i1 steps, it can acheive the
   same output over i2 >= i1 steps.
 *)
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
    + (* i2 = 0 *)
      inversion Hle.
    + (* i2 = S i2' *)
      assert (Hle': i1' <= i2') by lia. destruct c.
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
             destruct res; destruct p; destruct r.
             ++++ apply (IHi1' i2') in Heqst1'o; try assumption.
                  rewrite Heqst1'o. simpl. simpl in Hceval.
                  apply (IHi1' i2') in Hceval; try assumption.
             ++++ discriminate Hceval.
             ++++ apply (IHi1' i2') in Heqst1'o; try assumption.
                  rewrite Heqst1'o. simpl. simpl in Hceval.
                  apply (IHi1' i2' _ _ SBreak _) in Hceval; try assumption.
             ++++ apply (IHi1' i2') in Heqst1'o; try assumption.
                  rewrite Heqst1'o. simpl. simpl in Hceval.
                  rewrite Hceval. reflexivity.
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
             destruct res; destruct p; destruct r.
             ++++ apply (IHi1' i2') in Heqst1'o; try assumption.
                  rewrite -> Heqst1'o. simpl. simpl in Hceval.
                  apply (IHi1' i2') in Hceval; try assumption.
             ++++ apply (IHi1' i2') in Heqst1'o; try assumption.
                  rewrite -> Heqst1'o. simpl. simpl in Hceval.
                  rewrite Hceval. reflexivity.
             ++++ apply (IHi1' i2') in Heqst1'o; try assumption.
                  rewrite -> Heqst1'o. simpl. simpl in Hceval.
                  apply (IHi1' i2') in Hceval; try assumption.
             ++++ apply (IHi1' i2') in Heqst1'o; try assumption.
                  rewrite -> Heqst1'o. simpl. simpl in Hceval.
                  inversion Hceval.
         +++ (* i1'o = None *)
             inversion Hceval.
Qed.

(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

(*
   For any program c, states st and st' and result res, there exists at least
   one natural number i such that if the evaluation of c with initial state st
   over i steps has final state st' and result res, then we can say that the
   program c applied to the state st outputs the state st' with result res.
   Summarizing, the two alternative definitions of evaluation are equivalent.
 *)
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
           destruct p; destruct r.
           +++ apply E_Seq_Continue with s; apply IHi'; assumption.
           +++ destruct res.
               ++++ inversion H1.
               ++++ apply E_Seq_Break. apply IHi'. rewrite <- H1. assumption.
        ++ (* Otherwise -- contradiction *)
          discriminate H1.
      + (* if *)
        destruct (beval st b) eqn:Heqr.
        ++ (* r = true *)
           apply E_IfTrue; try apply IHi'; assumption.
        ++ (* r = false *)
           apply E_IfFalse; try apply IHi'; assumption.
      + (* while *) destruct (beval st b) eqn:Heqr.
        ++ (* r = true *)
           destruct (ceval_step st c i') eqn:Heqr1.
           +++ (* r1 = Some s *)
               destruct p; destruct r; destruct res.
               ++++ apply (E_WhileTrue_Continue st s st' b c); try apply IHi'; assumption.
               ++++ apply IHi' in H1. inversion H1.
               ++++ apply E_WhileTrue_Break.
                    +++++ assumption.
                    +++++ apply IHi'. inversion H1. rewrite H0 in Heqr1. assumption.
               ++++ inversion H1.
           +++ (* r1 = None *) discriminate H1.
        ++ (* r = false *)
           injection H1 as H2. rewrite <- H2. destruct res.
           +++ apply E_WhileFalse. assumption.
           +++ inversion H.
Qed.

(**
  For the following proof, you'll need [ceval_step_more] in a
  few places, as well as some basic facts about [<=] and [plus]. *)

(*
   For any program c, states st and st' and result res, if the program c
   applied to the state st outputs the state st' with result res, there has to
   exist at least one natural number i such that the evaluation of c with
   initial state st over i steps has final state st' and result res.
   Summarizing, the two alternative definitions of evaluation are equivalent
   (the other way around this time).
 *)
Theorem ceval__ceval_step: forall c st st' res,
    st =[ c ]=> st' / res ->
    exists i, ceval_step st c i = Some (st', res).
Proof.
  intros.
  induction H.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.
  - destruct IHceval. exists (S x). simpl. rewrite H. assumption.
  - destruct IHceval. exists (S x). simpl. rewrite H. assumption.
  - destruct IHceval1. destruct IHceval2. exists (S (x+x0)). simpl.
    assert (ceval_step st c1 (x+x0) = Some (st', SContinue)).
    + apply (ceval_step_more x).
      ++ lia.
      ++ assumption.
    + rewrite H3. destruct res.
      ++ apply (ceval_step_more x0).
         +++ lia.
         +++ assumption.
      ++ apply (ceval_step_more x0).
         +++ lia.
         +++ assumption.
  - destruct IHceval. exists (S x). simpl. rewrite H0. reflexivity.
  - destruct IHceval1. destruct IHceval2. exists (S (x+x0)). simpl.
    rewrite H. assert (ceval_step st c (x+x0) = Some (st', SContinue)).
    + apply (ceval_step_more x).
      ++ lia.
      ++ assumption.
    + rewrite H4. apply (ceval_step_more x0).
      ++ lia.
      ++ assumption.
  - destruct IHceval. exists (S x). simpl. rewrite H.
    assert (ceval_step st c x = Some (st', SBreak)).
    + apply (ceval_step_more x).
      ++ lia.
      ++ assumption.
    + rewrite H1. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.
Qed.

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

(* Write/explain the following proof in natural language,
   using your own words. *)

(*
   Explanation:
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
   We will have two subcases to prove:
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