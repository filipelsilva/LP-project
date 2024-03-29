(** * Imp: Simple Imperative Programs *)

(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp.
Set Default Goal Selector "!".

(** Next, we need to define the behavior of [break].  Informally,
    whenever [break] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [break]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [break]. In those cases, [break] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X := 0;
       Y := 1;
       while 0 <> Y do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [break] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [break], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [while b do c end], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [break] only terminates the
      innermost loop, [while] signals [SContinue]. *)

(** 3.1. Based on the above description, complete the definition of the
         [ceval] relation.
*)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st) / SContinue
  | E_IfTrue : forall st st' res b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' / res ->
      st =[ if b then c1 else c2 end]=> st' / res
  | E_IfFalse : forall st st' res b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' / res ->
      st =[ if b then c1 else c2 end]=> st' / res
  | E_Seq_Continue : forall st st' st'' res c1 c2,
      st  =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / res ->
      st  =[ c1 ; c2 ]=> st'' / res
  | E_Seq_Break : forall st st' c1 c2,
      st  =[ c1 ]=> st' / SBreak ->
      st  =[ c1 ; c2 ]=> st' / SBreak
  | E_WhileTrue_Continue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / SContinue ->
      st  =[ while b do c end ]=> st'' / SContinue
  | E_WhileTrue_Break : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ while b do c end ]=> st' / SContinue
  | E_WhileFalse : forall st b c,
      beval st b = false ->
      st =[ while b do c end ]=> st / SContinue

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').


(**
  3.2. Prove the following six properties of your definition of [ceval].
       Note that your semantics needs to satisfy these properties: if any of
       these properties becomes unprovable, you should revise your definition of `ceval`.
       Add a succint comment before each property explaining the property in your own words.
*)

(*
   For any program c, states st and st' and result s, if a program <{ break; c
   }> is ran on an initial state st and turns it into the state st', then st is
   the same as st'.
*)
Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  intros. inversion H.
  - inversion H2.
  - inversion H5. reflexivity.
Qed.

(*
   For any binary expression b, program c, states st and st' and result s, if a
   program <{ while b do c end }> is ran, its result will always be SContinue.
*)
Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  intros. inversion H; reflexivity.
Qed.

(*
   For any binary expression b, program c and states st and st', if b evaluates
   to true over the initial state of this while loop and program c finishes
   with SBreak, then the program <{ while b do c end }>'s result will always be
   SContinue.
*)
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros. apply E_WhileTrue_Break; assumption.
Qed.

(*
   For any programs c1 and c2 and states st, st' and st'', if:
   - c1 runs, turns the state st into st', and returns SContinue
   - c2 runs, turns the state st' into st'', and returns SContinue
   Then a program composed by the sequence of both programs, <{ c1; c2 }>,
   upon running, will turn the state st into st'', and return SContinue as well.
*)
Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  intros. apply (E_Seq_Continue st st' st'' SContinue c1 c2); assumption.
Qed.

(*
   For any programs c1 and c2 and states st and st', if c1 runs, turning the
   state st into st', and has return code of SBreak, then <{ c1; c2 }> (the
   sequence of both programs) runs, turning the state st into st', and has
   return code of SBreak as well (c2 is never ran).
*)
Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  intros. apply E_Seq_Break. assumption.
Qed.

(*
   For any binary expression b, program c and states st and st', if the program
   <{ while b do c end }>'s result is SContinue and b evaluates to true over
   the final state of this while loop, then there has to exist a state st''
   such that the execution of program c over this state results in the state
   st' with a result of SBreak.
*)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
  remember (<{ while b do c end }>) as loop.
  induction H; inversion Heqloop; subst.
  - apply IHceval2.
    + reflexivity.
    + assumption.
  - exists st. assumption.
  - rewrite H in H0. inversion H0.
Qed.
