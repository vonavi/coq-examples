(*|
Defining integers inductively in Coq (inductive definitions subject to relations)
=================================================================================

:Link: https://stackoverflow.com/questions/66222181/defining-integers-inductively-in-coq-inductive-definitions-subject-to-relations
|*)

(*|
Question
--------

In Coq, one can define the natural numbers inductively as follows:
|*)

Inductive nat :=
| zero : nat
| succ : nat -> nat.

(*|
I would like to know if it's possible to define the **integers**
inductively, in a similar fashion? I can do something like
|*)

Reset nat. (* .none *)
Inductive int :=
| zero : int
| succ : int -> int
| pred : int -> int.

(*|
but then I want to assert in the *definition* of `int` that `succ(pred
x) = x` and `pred(succ x) = x`, and I'm not sure how to do this.
|*)

(*|
Answer
------

What you are literally asking for is called a Quotient Inductive Type
(QIT) and is not currently supported in Coq even though there is a way
to hack around this limitation using private inductive types (see
`these slides <https://coq.inria.fr/files/coq5-slides-bertot.pdf>`_
for instance). It goes without saying that it is far from a
recommended option (at least in Coq, the situation is different in
cubical-agda that do support HITs, a general version of QIT).

In general, Coq does not provide arbitrary quotients. The standard
solutions are either to go to setoids (that is types equipped with an
equivalence relation and showing that all your constructions preserve
these equivalence relation, which is rather heavy) or use specific
aspects of the quotient that you want to do (see `this paper
<https://perso.crans.org/cohen/papers/quotients.pdf>`_). The case of
integers is actually one of the leading example of that paper.
|*)
