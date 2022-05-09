(*|
##################################################################
General advice about when to use ``Prop`` and when to use ``bool``
##################################################################

:Link: https://stackoverflow.com/q/44638724
|*)

(*|
Question
********

I am formalizing a grammar which is essentially one over boolean
expressions. In Coq, you can get boolean-like things in Prop or more
explicitly in bool.

So for example, I could write:

.. code-block:: coq

    true && true

Or

.. code-block:: coq

    True /\ True

The problem is that in proofs (which is what I really care about) I
can do a case analysis in domain bool, but in Prop this is not
possible (since all members are not enumerable, I suppose). Giving up
this tactic and similar rewriting tactics seems like a huge drawback
even for very simple proofs.

In general, what situations would one choose Prop over bool for
formalizing? I realize this is a broad question, but I feel like this
is not addressed in the Coq manual sufficiently. I am interested in
real world experience people have had going down both routes.
|*)

(*|
Answer
******

There are lots of different opinions on this. My personal take is that
you are often better off not making this choice: it makes sense to
have two versions of a property, one in ``Prop``, the other one in
``bool``.

Why would you want this? As you pointed out, booleans support case
analysis in proofs and functions, which general propositions do not.
However, ``Prop`` is more convenient to use in certain cases. Suppose
you have a type ``T`` with finitely many values. We can write a
procedure
|*)

Variable T : Type. (* .none *)
Variable all : (T -> bool) -> bool.

(*|
that decides whether a boolean property ``P : T -> bool`` holds of all
elements of ``T``. Imagine that we know that ``all P = true``, for
some property ``P``. We might want to use this fact to conclude that
``P x = true`` for some value ``x``. To do this, we need to prove a
lemma about ``all``:
|*)

Lemma allP : forall P : T -> bool,
    all P = true <-> (forall x : T, P x = true).
Admitted. (* .none *)

(*|
This lemma connects two different formulations of the same property: a
boolean one and a propositional one. When reasoning about ``all`` in a
proof, we can invoke ``allP`` to convert freely between the two. We
can also have different conversion lemmas:
|*)

Lemma allPn : forall P,
    all P = false <-> (exists x, P x = false).
Admitted. (* .none *)

(*|
In fact, we are free to choose *any* Coq proposition whatsoever to
relate to a boolean computation (as long, of course, as we can prove
that the two are logically equivalent). For instance, if we would like
to have a custom induction principle associated with a boolean
property, we can look for an equivalent formulation as an inductively
defined proposition.

The `Mathematical Components <http://ssr.msr-inria.inria.fr/>`__
library is a good example of development that follows this style.
Indeed, because it is so pervasive there, the library provides a
special view mechanism for writing conversion lemmas like the one
above and applying them. In plain Coq, we can also use the ``rewrite``
tactic to apply logical equivalences more conveniently.

Of course, there are many situations where it does not make sense to
have two formulations of the same property. Sometimes, you are forced
to use ``Prop``, because the property you care about is undecidable.
Sometimes, you might feel that you wouldn't gain anything by writing
your property in ``Prop``, and may keep it only as a boolean.

In addition to the `Software Foundations
<https://softwarefoundations.cis.upenn.edu/current/Logic.html#lab186>`__
chapter linked above, `this answer
<https://stackoverflow.com/questions/31554453/why-are-logical-connectives-and-booleans-separate-in-coq/31568076#31568076>`__
discusses the difference between ``bool`` and ``Prop`` in more depth.

----

**A:** Indeed some people is wary of what they call "Boolean
blindness", I am a fan of being boolean-blind and recovering my sight
only when needed, in particular in the context of program
verification. It should be noted that the core Math-Comp parts
pertaining boolean reflection will be part of the upcoming Coq 8.7
release, so there is really little reason not to use them if your
proof adapts well to this style.

**A:** Personally, I tend to work with ``Prop`` until a decision of
one of the propositions is necessary, and then use ``sumbool P (~P)``
(which has notation ``{P} + {~P}``). Then if you have some calculation
of ``{P} + {~P}``, eliminating that object gives the true/false
dichotomy, and you also get a direct proof of either ``P`` or ``~P``
(instead of having to apply a reflection lemma).

**A:** That is true, although the ``reflect`` predicate used in
MathComp makes it much simpler to perform case analysis on a boolean
reflecting a proposition ``P`` while obtaining proofs of ``P`` or
``~P`` on each branch: it suffices to destruct the proof of ``reflect
P b``.
|*)
