(*|
########################################
Coq: usage of ``PartialOrder`` typeclass
########################################

:Link: https://stackoverflow.com/q/44610998
|*)

(*|
Question
********

I am trying to define lexicographic ordering on strings over posets,
but I'm not completely sure how to use the ``PartialOrder`` typeclass.
|*)

Require Import List RelationClasses.

Fail Inductive lex_leq {A : Type} `{po : PartialOrder A} :
  list A -> list A -> Prop :=
| lnil: forall l, lex_leq nil l
| lcons:
  forall (hd1 hd2 : A) (tl1 tl2 : list A),
    hd1 <= hd2 -> (* error *)
    (hd1 = hd2 -> lex_leq tl1 tl2) ->
    lex_leq (hd1 :: tl1) (hd2 :: tl2). (* .unfold *)

(*|
Clearly ``<=`` is the wrong notation to use here; I'm wondering how I
can obtain an ordering relation from my ``po`` instance.
|*)

(*|
Answer
******

One can bind the names explicitly to make things more obvious. Before
we can do this we need to tell Coq not to complain about unbound
variables using the ``Generalizable Variables`` command:
|*)

From Coq Require Import List RelationClasses.

Generalizable Variables A eqA R.

Inductive lex_leq `{PartialOrder A eqA R} : list A -> list A -> Prop :=
| lnil: forall l, lex_leq nil l
| lcons:
  forall (hd1 hd2 : A) (tl1 tl2 : list A),
    R hd1 hd2 ->
    (hd1 = hd2 -> lex_leq tl1 tl2) ->
    lex_leq (hd1 :: tl1) (hd2 :: tl2).

(*|
You can find more information in the manual (`here
<https://coq.inria.fr/distrib/current/refman/Reference-Manual004.html#implicit-generalization>`__).
|*)
