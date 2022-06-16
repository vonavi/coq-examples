(*|
###################################
Implementing vector addition in Coq
###################################

:Link: https://stackoverflow.com/q/28487158
|*)

(*|
Question
********

Implementing vector addition in some of the dependently typed
languages (such as Idris) is fairly straightforward. As per the
`example on Wikipedia
<http://en.wikipedia.org/wiki/Idris_%28programming_language%29#Dependent_types>`__:

.. code-block:: idris

    import Data.Vect

    %default total

    pairAdd : Num a => Vect n a -> Vect n a -> Vect n a
    pairAdd Nil       Nil       = Nil
    pairAdd (x :: xs) (y :: ys) = x + y :: pairAdd xs ys

(Note how Idris' totality checker automatically infers that addition
of ``Nil`` and non-``Nil`` vectors is a logical impossibility.)

I am trying to implement the equivalent functionality in Coq, using a
custom vector implementation, albeit very similar to the one provided
in the official `Coq libraries
<https://coq.inria.fr/library/Coq.Vectors.VectorDef.html>`__:
|*)

Set Implicit Arguments.

Inductive vector (X : Type) : nat -> Type :=
| vnul : vector X 0
| vcons {n : nat} (h : X) (v : vector X n) : vector X (S n).
Arguments vnul {X}.

Fail Fixpoint vpadd {n : nat} (v1 v2 : vector nat n) : vector nat n :=
  match v1 with
  | vnul => vnul
  | vcons x1 v1' =>
      match v2 with
      | vnul => False_rect _ _
      | vcons x2 v2' => vcons (x1 + x2) (vpadd v1' v2')
      end
  end. (* .fails .unfold *)

(*|
Note that, I use ``False_rect`` to specify the impossible case,
otherwise the totality check wouldn't pass. However, for some reason
the type checker doesn't manage to unify ``n0`` with ``n1``.

What am I doing wrong?

----

**A:** This development contains a complete example:
http://www.cs.nott.ac.uk/~pszvc/g54dtp/vectors.v
|*)

(*|
Answer
******

It's not possible to implement this function so easily in plain Coq:
you need to rewrite your function using the *convoy pattern*. There
was a `similar question
<https://stackoverflow.com/questions/16952524/structural-recursion-on-a-dependent-parameter>`__
posted a while ago about this. The idea is that you need to make your
``match`` return a function in order to propagate the relation between
the indices:
|*)

Reset Initial. (* .none *)
Set Implicit Arguments.

Inductive vector (X : Type) : nat -> Type :=
| vnul : vector X 0
| vcons {n : nat} (h : X) (v : vector X n) : vector X (S n).
Arguments vnul {X}.

Definition vhd (X : Type) n (v : vector X (S n)) : X :=
  match v with
  | vcons h _ => h
  end.

Definition vtl (X : Type) n (v : vector X (S n)) : vector X n :=
  match v with
  | vcons _ tl => tl
  end.

Fixpoint vpadd {n : nat} (v1 v2 : vector nat n) : vector nat n :=
  match v1 in vector _ n return vector nat n -> vector nat n with
  | vnul         => fun _  => vnul
  | vcons x1 v1' => fun v2 => vcons (x1 + vhd v2) (vpadd v1' (vtl v2))
  end v2.
