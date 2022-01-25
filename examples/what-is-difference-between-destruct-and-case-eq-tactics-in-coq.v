(*|
#######################################################################
What is difference between ``destruct`` and ``case_eq`` tactics in Coq?
#######################################################################

:Link: https://stackoverflow.com/q/46440349
|*)

(*|
Question
********

I understood ``destruct`` as it breaks an inductive definition into
its constructors. I recently saw ``case_eq`` and I couldn't understand
what it does differently?

.. coq:: none
|*)

Require Import Coq.Structures.OrderedTypeEx.
Require Import FMapAVL.
Module M := FMapAVL.Make(Nat_as_OT).

Definition cc (n : nat) (c : M.t nat) : bool :=
  match M.find n c with
  | None => false
  | _ => true
  end.

Lemma l: forall (n : nat) (k :nat) (m : M.t nat),
    cc n m = true -> cc n (M.add k k m) = true.
Proof.
  intros. unfold cc in H.

(*||*)

  Show. (* .unfold .hyps .goals *)
Abort. (* .none *)

(*|
In the above context, if I do destruct ``M.find n m`` it breaks H into
true and false whereas ``case_eq (M.find n m)`` leaves ``H`` intact
and adds separate proposition ``M.find (elt:=nat) n m = Some v``,
which I can rewrite to get same effect as destruct.

Can someone please explain me the difference between the two tactics
and when which one should be used?

----

**A:** Check this link
https://stackoverflow.com/questions/6823301/how-to-do-cases-with-an-inductive-type-in-coq/6828451#6828451
|*)

(*|
Answer
******

The first basic tactic in the family of ``destruct`` and ``case_eq``
is called ``case``. This tactic modifies only the conclusion. When you
type ``case A`` and ``A`` has a type ``T`` which is inductive, the
system replaces ``A`` in the goal's conclusion by instances of all the
constructors of type ``T``, adding universal quantifications for the
arguments of these constructors, if needed. This creates as many goals
as there are constructors in type ``T``. The formula ``A`` disappears
from the goal and if there is any information about ``A`` in an
hypothesis, the link between this information and all the new
constructors that replace it in the conclusion gets lost. In spite of
this, ``case`` is an important primitive tactic.

Loosing the link between information in the hypotheses and instances
of ``A`` in the conclusion is a big problem in practice, so developers
came up with two solutions: ``case_eq`` and ``destruct``.

Personnally, when writing the Coq'Art book, I proposed that we write a
simple tactic on top of ``case`` that keeps a link between ``A`` and
the various constructor instances in the form of an equality. This is
the tactic now called ``case_eq``. It does the same thing as ``case``
but adds an extra implication in the goal, where the premise of the
implication is an equality of the form ``A = ...`` and where ``...``
is an instance of each constructor.

At about the same time, the tactic ``destruct`` was proposed. Instead
of limiting the effect of replacement in the goal's conclusion,
``destruct`` replaces all instances of ``A`` appearing in the
hypotheses with instances of constructors of type ``T``. In a sense,
this is cleaner because it avoids relying on the extra concept of
equality, but it is still incomplete because the expression ``A`` may
be a compound expression ``f B``, and if ``B`` appears in the
hypothesis but not ``f B`` the link between ``A`` and ``B`` will still
be lost.

Illustration
============
|*)

Definition my_pred (n : nat) := match n with 0 => 0 | S p => p end.

Lemma example n : n <= 1 -> my_pred n <= 0.
Proof.
  case_eq (my_pred n).

(*| Gives the two goals |*)

  Show. (* .unfold .hyps .goals *)

(*|
the extra equality is very useful here.

In `this question <https://stackoverflow.com/q/46434503/1809211>`__ I
suggested that the developer use ``case_eq (a == b)`` when ``(a ==
b)`` has type ``bool`` because this type is inductive and not very
informative (constructors have no argument). But when ``(a == b)`` has
type ``{a = b} + {a <> b}`` (which is the case for the ``string_dec``
function) the constructors have arguments that are proofs of
interesting properties and the extra universal quantification for the
arguments of the constructors are enough to give the relevant
information, in this case ``a = b`` in a first goal and ``a <> b`` in
a second goal.

----

**A:** Note that ``destruct`` has a variant ``destruct H eqn:H0``
which also remembers an equality.

**A:** Also note that there's a simple wrapper ``destruct_with_eqn
H``, which automatically generates a fresh name for the equality.
|*)
