(*|
###############################
Inductive definition of boolean
###############################

:Link: https://stackoverflow.com/q/54728450
|*)

(*|
Question
********

Trivially, I'm trying to define my own bool type as:
|*)

Inductive mybool : Type :=
| true
| false.

(*| Then I do a ``Print mybool.`` but the output says |*)

Print mybool. (* .unfold .messages *)

(*| How come the type of ``mybool`` is ``Set`` but not ``Type``? |*)

(*|
Answer
******

Coq uses what is called "Universe Minimization" to put inductive types
in the smallest possible universe. Since ``mybool`` doesn't depend on
any other types and doesn't do any universal quantification, it can
safely be put in the (second) lowest level of ``Type``, which is
``Set``. The lowest level is ``Prop``, but inductive types are only
placed in ``Prop`` if they only have one constructor (there are some
exceptions to this), or if it's explicitly annotated.

Note that Coq's universes are cumulative, so ``mybool`` is really in
every level of ``Type``, but it only shows the minimal level.

----

**Q:** I thought ``Set`` is the lowest level of ``Type``, and second
lowest is ``Prop`` (``Prop`` is higher than ``Set``). I thought
``Prop`` is for propositions. In my bool, we have two constructors.
Not sure I understand this part.

**A:** ``Prop`` indeed is for propositions, and can be thought of as
types that have at most one element. That means that ``Prop`` doesn't
contain "large" types that are normally found in ``Set``, like ``nat``
or ``bool``. But on the other hand, everything in ``Prop`` fits in
``Set``, so ``Prop`` is a lower level than ``Set``. You can check this
with something like ``Axiom P: Prop. Check P: Set.`` (which works) vs
``Axiom P: Set. Check P: Prop.`` (which doesn't).
|*)
