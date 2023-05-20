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
  intros. induction i1 as [|i1'].
  - inversion H0.
  (* - destruct i2 as [|i2']; inversion H; assert (Hle': i1' <= i2') by lia; destruct c. *)
  (*   + inversion H0. reflexivity. *)
  (*   + inversion H0. reflexivity. *)
  (*   + inversion H0. reflexivity. *)
  (*   + inversion H0. simpl. remember (ceval_step st c1 i1') as step1. destruct step1. *)
  (*     ++ rewrite H3. admit. *)
  (*     ++ inversion H0. admit. *)
  (*   + inversion H0. simpl. *)
  (*     remember (beval st b) as cond. destruct cond; rewrite H2; reflexivity. *)
  (*   + inversion H0. simpl. *)
  (*     remember (beval st b) as cond. destruct cond; try assumption. *)
  (*     ++ admit. *)
  (*     ++ reflexivity. *)
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

  - intros. inversion E.
  - intros. destruct c; simpl in E; inversion E; subst; clear E.
    + (* SKIP *) apply E_Skip.
    + (* BREAK *) apply E_Break.
    + (* ASGN *) apply E_Asgn. reflexivity.
    + (* SEQ *) remember (ceval_step st c1 i') as step1. destruct step1.
      ++ (* CONTINUE *) apply (E_Seq_Continue st st' st' res c1 c2).
         +++ apply IHi'. inversion Heqstep1. rewrite H1. admit.
         +++ apply IHi'. inversion Heqstep1. admit.
      ++ (* BREAK *) inversion H0.
    + (* IF *) remember (beval st b) as cond. destruct cond.
      ++ (* TRUE *) apply (E_IfTrue st st' res b c1 c2).
         +++ rewrite Heqcond. reflexivity.
         +++ apply IHi'. assumption.
      ++ (* FALSE *) apply (E_IfFalse st st' res b c1 c2).
         +++ rewrite Heqcond. reflexivity.
         +++ apply IHi'. assumption.
    + (* WHILE *) remember (beval st b) as cond. destruct cond.
      ++ (* TRUE *) remember (ceval_step st c i') as step. destruct step.
         +++ (* CONTINUE *) apply (E_WhileTrue_Continue st st st' b c).
             (* ++++ rewrite Heqcond. reflexivity. *)
             (* ++++ apply IHi'. inversion Heqstep. admit. *)
             (* ++++ apply IHi'. inversion Heqstep. admit. *)
         (* +++ apply (E_WhileTrue_Continue st st st' b c). *)
             (* ++++ rewrite Heqcond. reflexivity. *)
             (* ++++ apply IHi'. inversion Heqstep. admit. *)
             (* ++++ apply IHi'. inversion Heqstep. admit. *)
         +++ (* BREAK *) inversion H0.
      ++ (* FALSE *) inversion E. apply E_WhileFalse. rewrite Heqcond. rewrite H1. reflexivity.
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
  (* TODO *)
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