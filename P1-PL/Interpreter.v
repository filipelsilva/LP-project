(** * An Evaluation Function for Imp *)


(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From FirstProject Require Import Imp Maps.

(* Let's import the result datatype from the relational evaluation file *)
From FirstProject Require Import RelationalEvaluation.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some (x, SContinue) => e2
         | Some (x, SBreak) => e1
         | None => None
       end)
   (right associativity, at level 60).

Notation "'LETOPT_WHILE' x <== e1 'IN' e2"
   := (match e1 with
         | Some (x, SContinue) => e2
         | Some (x, SBreak) => Some(x, SContinue)
         | None => None
       end)
   (right associativity, at level 60).

(** 2.1. Implement ceval_step as specified. To improve readability,
         you are strongly encouraged to define auxiliary notation.
         See the notation LETOPT commented above (or in the ImpCEval chapter).
*)

Fixpoint ceval_step (st : state) (c : com) (i : nat): option (state*result) :=
  match i with
  | O => None
  | S i' => match c with
            | <{ break }> => Some(st, SBreak)
            | <{ skip }> => Some(st, SContinue)
            | <{ x := y }> => Some(x !-> aeval st y ; st, SContinue)
            | <{ x ; y }> => LETOPT st' <== ceval_step st x i' IN ceval_step st' y i'
            | <{ if cond then exp1 else exp2 end }> => if (beval st cond) then ceval_step st exp1 i' else ceval_step st exp2 i'
            | <{ while cond do exp end }> => if (beval st cond) then LETOPT_WHILE st' <== ceval_step st exp i' IN ceval_step st' c i' else Some(st, SContinue) end
  end.

(* The following definition is taken from the book and it can be used to
   test the step-indexed interpreter. *)
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some (st, _) => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.

(**
  2.2.  Prove the following three properties.
        Add a succint explanation in your own words of why `equivalence1` and `inequivalence1` are valid.
*)

(*
   This theorem is valid, because after a break (outside of a while, that is)
   no more code is gonna be executed; the program stops.
   Therefore, there exists at least one natural number n such that the
   evaluation of the programs <{ break; c }> (c being any program) and <{
   break; skip }> over a same initial state st, and a number of steps larger or
   equal to n will result in the same final state and result.
*)
Theorem equivalence1: forall st c,
  (exists i0, forall i1, i1>=i0 ->
  ceval_step st <{ break; c }> i1 = ceval_step st <{ break; skip }> i1).
Proof.
  intros. exists 2. intros.
  destruct i1; try lia.
  destruct i1; try lia.
  simpl. reflexivity.
Qed.

(*
   This theorem is valid, because after a break (outside of a while, that is)
   no more code is gonna be executed; the program stops with result code
   SBreak. However, if a program stops without it being caused by a while
   statement, the result code will be SCOntinue.
   Therefore, there exists at least one natural number n such that the
   evaluation of the programs <{ break; c }> (c being any program) and <{ skip
   }> over a same initial state st, and a number of steps larger or equal to n
   will always result in different results (but not different final states, as
   none of these programs does any arithmetic or assignments.
*)
Theorem inequivalence1: forall st c,
  (exists i0, forall i1, i1>=i0 ->
  ceval_step st <{ break; c }> i1 <> ceval_step st <{ skip }> i1).
Proof.
  intros. exists 2. intros.
  destruct i1; try lia.
  destruct i1; try lia.
  simpl. discriminate.
Qed.

Theorem p1_equivalent_p2: forall st,
  (exists i0,
    forall i1, i1>=i0 ->
    ceval_step st p1 i1 = ceval_step st p2 i1
  ).
Proof.
  intros. exists 6. intros.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  simpl. reflexivity.
Qed.
