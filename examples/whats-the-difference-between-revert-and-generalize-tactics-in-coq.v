(*|
###########################################################################
What's the difference between ``revert`` and ``generalize`` tactics in Coq?
###########################################################################

:Link: https://stackoverflow.com/q/38067228
|*)

(*|
Question
********

From the Coq reference manual (8.5p1), my impression is that
``revert`` is the inverse of ``intro``, but so is ``generalize`` to a
certain extent. For example, ``revert`` and ``generalize dependent``
below seem to be the same.
|*)

Goal forall x y : nat, 1 + x = 2 + y -> 1 + x + 5 = 7 + y.
intros x y. revert x y.
intros x y. generalize dependent y. generalize dependent x.
Abort. (* .none *)

(*|
Is it just that ``generalize`` is more powerful than ``revert``?

Also, the documentation is a bit circular in explaining things about
``generalize``:

    This tactic applies to any goal. It generalizes the conclusion
    with respect to some term.

Is ``generalize`` similar to the abstraction operator in lambda
calculus?
|*)

(*|
Answer
******

Yes, ``generalize`` is more powerful. You've demonstrated it has at
least the same power as ``revert`` by simulating ``revert`` with
``generalize``. Notice that ``generalize`` works on any *terms*,
``revert`` -- only on *identifiers*.

For example, ``revert`` cannot do the example from the manual:

    .. coq::
|*)

    Goal forall x y, 0 <= x + y + y. (* .none *)
      intros x y. (* .none *)
      Show. (* .unfold .messages *)
      generalize (x + y + y).
      Show. (* .unfold .messages *)
    Abort. (* .none *)

(*| As for "circularity" of the definition, the real explanation is
right below the example:

    If the goal is ``G`` and ``t`` is a subterm of type ``T`` in the
    goal, then ``generalize t`` replaces the goal by ``forall x:T,
    G0`` where ``G0`` is obtained from ``G`` by replacing all
    occurrences of ``t`` by ``x``.

Essentially, this says ``generalize`` wraps your goal in ``forall``,
replacing some term with a fresh variable (``x``).

Of course, ``generalize`` should be used with some thought and
caution, since one can get a false statement to prove after using it:
|*)

    Goal forall x y, x > 0 -> 0 < x + y + y.
      intros x y H.
      generalize dependent (x + y + y).
      Show. (* .unfold .messages *)

(*|
----

**Q:** Thanks for the answer, but I still don't understand the why is
this operation called "generalize" in the first place, despite the
given operational semantics. Also, the example Goal you cited seem to
be false to begin with. I don't see how generalize had made anything
worse here.

**A:** It's called ``generalize`` because you substitute a *concrete*
and perhaps complex term having some inner structure with a
*placeholder* without any inner structure of the same type. I.e.
you're *abstracting* away some details and get a more general thing.
And the last example (the goal is true, btw, try ``intros; lia.`` on
it) shows that one cannot throw some concrete details away without any
limits, if one wants to preserve the validity of a formula.
|*)
