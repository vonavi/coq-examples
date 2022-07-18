(*|
################################################
Removing the last element of a sized list in Coq
################################################

:Link: https://stackoverflow.com/q/71536389
|*)

(*|
Question
********

Consider the following type definition of a sized list:
|*)

Inductive listn : nat -> Type -> Type :=
| nil: forall {A : Set}, listn 0 A
| cons: forall {n : nat} {A : Set}, A -> listn n A -> listn (S n) A.

(*|
This is essentially the `Vect
<https://github.com/idris-lang/Idris-dev/blob/master/libs/base/Data/Vect.idr>`__
type in Idris.

I am trying to define the ``init`` function for ``listn``, which
removes the last element.

My attempted implementation was virtually identical to the definition
of ``init`` in Idris. Here it is in Idris:

.. code-block:: idris

    init : Vect (S len) elem -> Vect len elem
    init (x::[])    = []
    init (x::y::ys) = x :: init (y::ys)

Transcribed into Coq:
|*)

Fail Fixpoint init {n : nat} {A : Set} (l : listn (S n) A): listn n A :=
  match l with
  | cons x nil => nil
  | cons x (cons y ys) => cons x (init (cons y ys))
  end. (* .fails *)

(*| ...but this fails with: |*)

Fail Fixpoint init {n : nat} {A : Set} (l : listn (S n) A): listn n A :=
  match l with
  | cons x nil => nil
  | cons x (cons y ys) => cons x (init (cons y ys))
  end. (* .unfold .messages *)

(*|
I take it that Coq isn't able to see that the case necessarily implies
that ``n`` is zero. This is a problem I keep running into – Coq isn't
able to see the relationship between ``n`` and the list itself.

Hence my questions:

- How can ``init`` be implemented in Coq?
- Why does the Idris definition work in Idris but not in Coq? What is
  Idris doing behind the scenes that Coq isn't?
|*)

(*|
Answer
******

By itself, Coq is not very good for writing this kind of code, but you
can use the `Equations plugin
<https://github.com/mattam82/Coq-Equations>`__ to make it simpler.
Nevertheless, let us see how we can do it without external
dependencies:
|*)

Require Import Coq.Vectors.Vector.
(* Vector.t is equivalent to your listn type *)

Arguments nil {A}.
Arguments cons {A} _ {n}.

Fixpoint init {n : nat} {A : Set} (xs : Vector.t A (S n)): Vector.t A n :=
  match xs in Vector.t _ m return Vector.t A (pred m) with
  | nil => nil
  | cons x xs =>
      match xs in Vector.t _ m return Vector.t A m -> Vector.t A m with
      | nil      => fun _  => nil
      | cons _ _ => fun xs => cons x (init xs)
      end xs
  end.

(*|
This definition differs from yours in a few ways. First, we need to
annotate the return type of ``match`` to explain how it depends on the
length of the vector. The ``in Vector.t _ m`` part says that the
return type is *generic* on the length of the vector -- we *cannot*
assume that the length is of the form ``S n``.

Second, we have to enumerate all cases of the data type: ``match`` is
*always* exhaustive in Coq, even if some of the branches are
unreachable due to typing information. Thus, I've included a case for
``nil`` in the first match.

Third, Coq cannot recognize that ``init (cons y ys)`` is a valid
recursive call. We fix this by giving ``cons y ys`` a name, ``xs``,
before destructing it, and using ``init xs`` instead. There is a
subtlelty, however. In ``cons x xs``, the type of ``xs`` is ``Vector.t
A m`` for *some* ``m``, which may or may not be a successor, so we
cannot call ``init`` directly. Instead, we first destruct ``xs``, and
perform the recursive call only on the ``cons`` branch. But because
``match`` is generic on its length argument, Coq does not see a
connection between the length of ``xs`` inside and outside of
``match``. The solution is to perform what Adam Chlipala calls the
*convoy pattern*: we make match return a function rather than a plain
vector, and pass ``xs`` as an argument outside of the match. This way,
the connection between the two lengths is not lost.

I don't know much about Idris, but my guess is that its type-checking
algorithm is more complicated than Coq's, which is why it can tell
that the analogous definition is valid. Coq's rules are quite simple
(and limited), to be honest.
|*)
