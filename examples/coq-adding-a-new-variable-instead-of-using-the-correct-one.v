(*|
##########################################################
Coq adding a new variable instead of using the correct one
##########################################################

:Link: https://stackoverflow.com/q/39459959
|*)

(*|
Question
********

I'm working on my own implementation of vectors in Coq, and I'm
running into a bizarre problem.

Here is my code thus far:
|*)

Set Implicit Arguments.

Inductive Fin : nat -> Type :=
| FZ : forall n, Fin (S n)
| FS : forall n, Fin n -> Fin (S n).

Definition emptyf (A : Type) : Fin 0 -> A.
  intro e. inversion e.
Defined.

Inductive Vec (A : Type) : nat -> Type :=
| Nil  : Vec A 0
| Cons : forall n, A -> Vec A n -> Vec A (S n).

Definition head (A : Type) (n : nat) (v : Vec A (S n)) : A :=
  match v with
  | Cons a _ => a
  end.

Definition tail (A : Type) (n : nat) (v : Vec A (S n)) : Vec A n :=
  match v with
  | Cons _ w => w
  end.

Fail Fixpoint index (A : Type) (n : nat) : Vec A n -> Fin n -> A :=
  match n as n return Vec A n -> Fin n -> A with
  | 0   => fun _ i => emptyf _ i
  | S m => fun v i => match i with
                      | FZ _ => head v
                      | FS j => index (tail v) j
                      end
  end. (* .fails *)

(*|
Everything up to ``tail`` compiles fine, but when I try to compile
``index``, I receive the following error:
|*)

Fail Fixpoint index (A : Type) (n : nat) : Vec A n -> Fin n -> A :=
  match n as n return Vec A n -> Fin n -> A with
  | 0   => fun _ i => emptyf _ i
  | S m => fun v i => match i with
                      | FZ _ => head v
                      | FS j => index (tail v) j
                      end
  end. (* .unfold .messages *)

(*|
Clearly, the culprit is that Coq introduces the new variable ``n0``
instead of assigning ``j`` the type ``Fin m``, even though this is the
only possible type for ``j`` which would result in ``i`` being built
from ``j``. Any idea why this would happen, and how I might be able to
resolve this issue?
|*)

(*|
Answer (eponier)
****************

Note that you do not need to pattern-match against ``n``, but only
against the argument of type ``Fin n``. The resulting definition is
simpler.
|*)

Fixpoint index {A : Type} {n : nat} (i : Fin n) : Vec A n -> A :=
  match i in Fin n0 return Vec A n0 -> A with
  | FZ _ => fun v => head v
  | FS j => fun v => index j (tail v)
  end.

(*| Coq is actually cleaver enough to guess the annotations. |*)

Reset index. (* .none *)
Fixpoint index {A : Type} {n : nat} (i : Fin n) : Vec A n -> A :=
  match i with
  | FZ _ => fun v => head v
  | FS j => fun v => index j (tail v)
  end.

(*|
----

**A (Anton Trunov):** This one feels like magic -- simple argument
swapping solves the problem instantaneously. Nice!

**A:** I did not realize that I switched the arguments. Another
difference with the original function: the decreasing argument is
``i``, not ``n``.

**A (Anton Trunov):** Yes, however if you start with pattern-mathing
on a vector (as in `my answer
<http://stackoverflow.com/a/39469676/2747511>`__), you will have to
use something like the convoy pattern (see `larsr's answer
<http://stackoverflow.com/a/39467904/2747511>`__). So that swap is
actually a big deal.
|*)

(*|
Answer (ejgallego)
******************

I find ``Vec`` and ``Fin`` very hard to use in general, so these days
I use ``'I_n`` and ``n.-tuples T`` from math-comp, which are just
naturals and lists with an irrelevant proof attached. However, if you
want to continue the fun of complex pattern matches, you could try to
define a stronger pattern matching principle:
|*)

Reset index. (* .none *)
Definition fin_case T m (i : Fin m) : T -> (Fin (pred m) -> T) -> T :=
  match i with
  | FZ _ => fun fn fz => fn
  | FS j => fun fn fz => fz j
  end.

(*| Once you have ``fin_case``, you function definition works: |*)

Fixpoint index (A : Type) (n : nat) : Vec A n -> Fin n -> A :=
  match n as n return Vec A n -> Fin n -> A with
  | 0   => fun _ i => emptyf _ i
  | S m => fun v i => fin_case i (head v) (index (tail v))
  end.

(*|
----

**Q:** Thanks for the reply, but It seems to me like this just pushes
the problem onto how to define ``fin_case``. No matter what I try, I
still run into the same problem. Would you mind sharing the definition
you have in mind?

**A:** Updated, a couple of comments:

a) Note that this "pushing the problem onto" is indeed more than that
   and a crucial tool in Coq style dependent programming.
b) There are many other ways to solve these kind of problems, indeed,
   writing a proper match still feels like a bit of an art.
|*)

(*|
Answer (Anton Trunov)
*********************

Just to add to the other answers, a tactic-based solution:
|*)

Reset index. (* .none *)
Fixpoint index (A : Type) (n : nat) (v : Vec A n) (i : Fin n) : A.
  destruct v as [| n h tl].
  - exact (emptyf A i).
  - inversion i as [ | ? i'].
    + exact h.
    + exact (index _ _ tl i').
Defined.

(*|
The ``inversion`` tactic takes care of the "information loss". If you
try to ``Print index.`` the result won't be pretty, but Coq
essentially uses the convoy pattern @larsr has mentioned.

Notice that this approach doesn't use pattern-matching on ``n``. It
pattern-matches on the vector argument instead, that's why it doesn't
need the ``head`` and ``tail`` functions.
|*)

(*|
Answer (larsr)
**************

When you use ``match`` you can lose information. I used the `convoy
pattern <http://adam.chlipala.net/cpdt/html/MoreDep.html>`__ to get
the info back into the context.

.. code-block:: coq

    match i in Fin (S n0) return n0 = m -> A with
      ... => fun H : n0 = m => ...
    end eq_refl

enables Coq to get the info ``n0 = m`` into the context. It is sent
into the match clauses as a function parameter. To use it in the type
check I use ``(match H with ... end)`` so that Coq understands that
``Fin n0 = Fin m``. This is the solution.
|*)

Reset index. (* .none *)
Fixpoint index (A : Type) (n : nat) : Vec A n -> Fin n -> A :=
  match n as n return Vec A n -> Fin n -> A with
  | 0   => fun _ i => emptyf _ i
  | S m => fun v i =>
             match i in Fin (S n') return n' = m -> A with
             | FZ _ => fun _ => head v
             | FS j => fun H => index (tail v) (match H with eq_refl _ => j end)
             end eq_refl
  end.

(*|
When the type checking doesn't understand that two things are equal,
usually the convoy pattern can help you get that info into the
context. I also recommend using ``refine`` to incrementally build up
the term. It let's you see what information there is in the context.

----

**A:** A simple
|*)

Definition cast (m n : nat) (i : Fin m) (H : m = n) : Fin n :=
  eq_rec m Fin i n H.

(*|
might make the code a bit easier to read (``(match H with eq_refl _ =>
j end)`` gets replaced by ``(cast j H)``).

**A:** A comment on the solutions using equality casts, (including the
one with ``inversion``) is that they may not compute/reduce properly
inside Coq, needing additional rewrites.
|*)
