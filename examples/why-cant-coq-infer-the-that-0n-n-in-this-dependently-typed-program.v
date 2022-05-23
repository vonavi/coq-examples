(*|
#############################################################################
Why can't Coq infer the that ``0 + n = n`` in this dependently typed program?
#############################################################################

:Link: https://stackoverflow.com/q/35989122
|*)

(*|
Question
********

I'm starting to use Coq and I'd like to define some dependently typed
programs. Consider the following:
|*)

Inductive natlist : nat -> Type :=
| natnil : natlist 0
| natcons : forall k, nat -> natlist k -> natlist (S k).

Fail Fixpoint natappend (n : nat) (l1 : natlist n) (m : nat) (l2 : natlist m) :
  natlist (n + m) :=
  match l1 with
  | natnil => l2
  | natcons _ x rest => natcons (n + m) x (natappend rest l2)
  end. (* .fails *)

(*|
So ``natlist k`` would be a list of ``nat``\ s of length ``k``. The
problem with the definition of concatenation as ``natappend`` is the
following error:
|*)

Fail Fixpoint natappend (n : nat) (l1 : natlist n) (m : nat) (l2 : natlist m) :
  natlist (n + m) :=
  match l1 with
  | natnil => l2
  | natcons _ x rest => natcons (n + m) x (natappend rest l2)
  end. (* .unfold .messages *)

(*|
As you can see it has a problem with the clause:

.. code-block::

    | natnil => l2

because it claims that the type of ``l2`` is ``natlist m`` while the
result type must be ``natlist (n + m) = natlist (0 + m)``.

I know that Coq cannot resolve arbitrary expressions at the type level
to avoid non-terminating computations, but I find strange that even
this simple case isn't handled.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

The problem is that you had a type error in your second branch. Here
is a version that works:
|*)

Fixpoint natappend {n m : nat} (l1 : natlist n) (l2 : natlist m) :
  natlist (n + m) :=
  match l1 with
  | natnil => l2
  | natcons n' x rest => natcons (n' + m) x (natappend rest l2)
  end.

(*|
The crucial difference between this version and the original one is
the parameter passed to ``natcons``: here, it is ``n' + m``, whereas
before it was ``n + m``.

This example illustrates very well a general issue with non-locality
of error messages in Coq, in particular when writing dependently typed
programs. Even though Coq complained about the first branch, the
problem was actually in the second branch. Adding annotations in your
``match`` statement, as suggested by @jbapple, can be useful when
trying to diagnose what is going wrong.
|*)

(*|
Answer (jbapple)
****************

You need ``match ... as ... in ... return ...`` to do more
sophisticated type annotations. See `Adam Chlipala's chapter "Library
MoreDep" in his Book "Certified Programming with Dependent Types"
<http://adam.chlipala.net/cpdt/html/MoreDep.html>`__ or `"Chapter 17:
Extended pattern-matching" in the Coq manual
<https://coq.inria.fr/refman/Reference-Manual020.html>`__. Both have
the ``concat`` example you are working on.

You could also just delay the dependent type bit until the end:
|*)

Reset Initial. (* .none *)
Definition natlist n := { x : list nat & n = length x }.

(*|
Then prove that non-dependently-typed ``concat`` preserves length
sums.

----

**A:**
I much support @jbapple's definition of natlist as a dependent record
instead of the original one, however I'd suggest using
|*)

Reset Initial. (* .none *)
Require Import PeanoNat Bool. (* .none *)
Definition natlist n := { x : list nat & Is_true (n =? length x) }.

(*|
where ``=?`` is the boolean equality on ``nat``, for reasons of proof
irrelevance.

**A:** In general using a ``bool`` makes it easier to prove
injectivity of the first projection, see:
http://stackoverflow.com/questions/35290012/inductive-subset-of-an-inductive-set-in-coq/35300521#35300521

**A:** By the way, I learned about this by reading the ``tuple.v``, a
very good example of a complete sized list library is
http://ssr.msr-inria.inria.fr/~jenkins/current/mathcomp.ssreflect.tuple.html,
I really learned a lot from trying to understand it.
|*)
