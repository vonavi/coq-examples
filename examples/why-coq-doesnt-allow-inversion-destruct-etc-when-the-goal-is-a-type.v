(*|
####################################################################################
Why Coq doesn't allow ``inversion``, ``destruct``, etc. when the goal is a ``Type``?
####################################################################################

:Link: https://stackoverflow.com/q/27322979
|*)

(*|
Question
********

When ``refine``\ ing a program, I tried to end proof by ``inversion``
on a ``False`` hypothesis when **the goal was a** ``Type``. Here is a
reduced version of the proof I tried to do.
|*)

Lemma strange1 : forall T : Type, 0 > 0 -> T.
  intros T H.
  Fail inversion H. (* .fails *) (* Coq refuses inversion on 'H : 0 > 0' *)

(*| Coq complained |*)

  Fail inversion H. (* .unfold .messages *)
Abort. (* .none *)

(*|
However, since I do nothing with ``T``, it shouldn't matter, ... or?

I got rid of the ``T`` like this, and the proof went through:
|*)

Lemma ex_falso : forall T : Type, False -> T.
  inversion 1.
Qed.

Lemma strange2 : forall T : Type, 0 > 0 -> T.
  intros T H.
  apply ex_falso. (* this changes the goal to 'False' *)
  inversion H.
Qed.

(*|
What is the reason Coq complained? Is it just a deficiency in
``inversion``, ``destruct``, etc.?

----

**A:** An enlightening discussion at the coq-club mailing list:
https://sympa.inria.fr/sympa/arc/coq-club/2014-12/msg00036.html
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

I had never seen this issue before, but it makes sense, although one
could probably argue that it is a bug in ``inversion``.

This problem is due to the fact that ``inversion`` is implemented by
case analysis. In Coq's logic, one cannot *in general* perform case
analysis on a *logical* hypothesis (i.e., something whose type is a
``Prop``) if the result is something of computational nature (i.e., if
the sort of the type of the thing being returned is a ``Type``). One
reason for this is that the designers of Coq wanted to make it
possible to erase proof arguments from programs when extracting them
into code in a sound way: thus, one is only allowed to do case
analysis on a hypothesis to produce something computational if the
thing being destructed cannot alter the result. This includes:

1. Propositions with no constructors, such as ``False``.
2. Propositions with only one constructor, as long as that constructor
   takes no arguments of computational nature. This includes ``True``,
   ``Acc`` (the accessibility predicated used for doing well-founded
   recursion), but excludes the existential quantifier ``ex``.

As you noticed, however, it is possible to circumvent that rule by
converting some proposition you want to use for producing your result
to another one you can do case analysis on directly. Thus, if you have
a contradictory assumption, like in your case, you can first use it to
prove ``False`` (which is allowed, since ``False`` is a ``Prop``), and
*then* eliminating ``False`` to produce your result (which is allowed
by the above rules).

In your example, ``inversion`` is being too conservative by giving up
just because it cannot do case analysis on something of type ``0 < 0``
in that context. It is true that it can't do case analysis on it
directly by the rules of the logic, as explained above; however, one
could think of making a slightly smarter implementation of
``inversion`` that recognizes that we are eliminating a contradictory
hypothesis and adds ``False`` as an intermediate step, just like you
did. Unfortunately, it seems that we need to do this trick by hand to
make it work.
|*)

(*|
Answer (stop-cran)
******************

In addition to Arthur's answer, there is a workaround using
`constructive_definite_description
<https://coq.github.io/doc/master/stdlib/Coq.Logic.Description.html#constructive_definite_description>`__
axiom. Using this axiom in a function would not allow to perform
calculations and extract code from it, but it still could be used in
other proofs:
|*)

Reset Initial. (* .none *)
From Coq Require Import Description.

Definition strange1 : forall T : Type, 0 > 0 -> T.
  intros T H.
  assert (exists! t : T, True) as H0 by inversion H.
  apply constructive_definite_description in H0.
  destruct H0 as [x ?].
  exact x.
Defined.

(*| Or same function without proof editing mode: |*)

Definition strange2 (T : Type) (H : 0 > 0) : T :=
  proj1_sig (constructive_definite_description (fun _ => True) ltac:(inversion H)).

(*|
Also there's a stronger axiom `constructive_indefinite_description
<https://coq.github.io/doc/master/stdlib/Coq.Logic.IndefiniteDescription.html#constructive_indefinite_description>`__
that converts a proposition ``exists x : T, P x`` (without uniqueness)
into a corresponding sigma-type ``{x : T | P x}``.
|*)
