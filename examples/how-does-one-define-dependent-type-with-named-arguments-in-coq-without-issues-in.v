(*|
#################################################################################################################
How does one define dependent type with named arguments in Coq without issues in unification in the constructors?
#################################################################################################################

:Link: https://stackoverflow.com/q/71518005
|*)

(*|
Question
********

I want to defined a lenghted list but I like arguments with names at
the top of the inductive definition. Whenever I try that I get
unification errors with things I hoped worked and was forced to do a
definition that obviously has bugs e.g. allows a list where everything
is length ``0`` but has ``1`` element. How do I fix this?
|*)

Inductive Vector {A : Type} (n : nat) : Type :=
| vnil (* not quite right... *)
| vcons (hd : A) (tail : Vector (n - 1)).

Check vnil 0.
Check vcons 1 true (vnil 0).

Inductive Vector' {A: Type} : nat -> Type :=
| vnil' : Vector' 0
| vcons' : forall n : nat, A -> Vector' n -> Vector' (S n).

Check vnil'.
Check vcons' 0 true (vnil').

Inductive Vector'' {A : Type} (n : nat) : Type :=
| vnil'' : Vector'' n (* seems weird, wants to unify with n, argh! *)
| vcons'' : A -> Vector'' (n - 1) -> Vector'' n.

Check vnil'' 0.
Check vcons'' 1 true (vnil'' 0).
(* Check vcons'' 0 true (vnil'' 0). *)
(* it also worked! nooooo! hope the -1 did the trick but not *)

(*|
Answer
******

Named arguments to the left of ``:`` (they are called parameters) are
implicitly ``forall``'d in each constructor and must appear as the
same variable in the return type of each constructor. Arguments to the
right (they are called indices) are not implicitly ``forall``'d and
may appear as anything. Part of the issue with your definitions is
that ``n`` is already introduced by the time you're writing the type
of each constructor, so you can't quite restrict it to be ``Z`` or ``S
m`` at that point.

The idea is that parameters are supposed to be parameters to the whole
inductive definition. ``Vector A n`` and ``Vector B m`` do not depend
on each other; it would make sense to consider ``Vector A`` and
``Vector B`` to be different inductive definitions, and ``Vector`` as
a family of inductives parameterized by a ``Type``. On the other hand,
``Vector A (S n)`` refers to ``Vector A n``; you cannot construct the
type ``Vector A (S n)`` without first constructing ``Vector A n``, so
they should be considered parts of one inductive construction ``Vector
A : nat -> Type``.

This interpretation is not strictly enforced---you can poke a hole in
it with ``Inductive E (n : nat) : Set := | mk_E : E (S n) -> E
n.``---but the rule about parameters vs. indices in constructor return
types is enforced. It is the *intent of the design* of Coq that the
"most natural" way to define ``Vector`` is
|*)

Reset Initial. (* .none *)
(* making A an implicit argument to Vector seems a bad idea... *)
Inductive Vector (A : Type) : nat -> Type :=
| vnil  : Vector A O
| vcons : forall n, A -> Vector A n -> Vector A (S n).
(* if you want to clean up vnil and vcons afterwards you can issue
   something like *)
Arguments vnil {A}.
Arguments vcons {A n}.
(* it would also work to define Vector with A implicit and then just
   use Arguments on Vector to make A explicit (it would leave n
   explicit in vcons), but that's just weird *)

(*|
If you want to clarify what the ``nat`` is doing, you could just leave
a comment like

.. code-block:: coq

    (* A [Vector A n] is a list of [n] elements of type [A]. *)

or

.. code-block:: coq

    Inductive Vector (A : Type) : (* n *) nat -> Type :=

If you *really* want ``Inductive Vector (A : Type) (n : nat) : Type``,
then you have to resort to something like
|*)

Reset Initial. (* .none *)
Inductive Vector (A : Type) (n : nat) : Type :=
| vnil  (prf : n = O)
| vcons (m : nat) (prf : n = S m) (x : A) (xs : Vector A m).

(*| Which makes everything messy. |*)
