(*|
######################################################
Trouble writing my notation for natural numbers in Coq
######################################################

:Link: https://stackoverflow.com/q/11714415
|*)

(*|
Question
********

Why does Coq not accept this?

.. coq:: none
|*)

Definition addition a b := a + b.
Definition multiply a b := a * b.
Definition ten := 10.

(*||*)

Fail Notation "[ d1 , .. , d2 ]" := (addition (multiply ( .. d1 .. ) ten) d2). (* .fails *)

(*|
Answer
******

`Recursive notations
<http://coq.inria.fr/doc/Reference-Manual015.html#RecursiveNotations>`__
need to obey fairly strict rules. The pattern to repeat must appear
twice (that's how Coq knows what is to be repeated): once using ``d2``
around the hole, and once using ``d1`` around a *terminating
expression*. You've only used your pattern once, using ``d2`` around
the hole. You need another iteration, around some ``zero`` (like
``nil`` in the notation for lists).
|*)

Definition zero := 0. (* .none *)
Notation "[ d1 , .. , d2 ]" :=
  (addition (multiply .. (addition (multiply zero ten) d1) .. ten) d2).

(*|
If you don't wish to introduce a zero, you can require at least two
digits inside the brackets (instead of just one as above), and use
that as the terminating expression. This is like the notation for
pairs (in ``Init/Notations.v``, also presented in the manual). You
could complement this with a notation for ``[d0]`` with lower
priority, but as this is just ``d0`` there isn't much point.
|*)

Notation "[ d0 , d1 , .. , d2 ]" :=
  (addition (multiply .. (addition (multiply d0 ten) d1) .. ten) d2).
