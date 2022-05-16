(*|
##########################################################################
How to leverage ``auto``'s searching and hint databases in custom tactics?
##########################################################################

:Link: https://stackoverflow.com/q/41171406
|*)

(*|
Question
********

In my coq development I am learning how to create new tactics tailored
to my problem domain, a la `Prof. Adam Chlipala
<http://adam.chlipala.net/cpdt/html/Match.html>`__. On that page he
describes how to create powerful custom tactics by e.g. combining
``repeat`` with ``match``.

Now, I already have a powerful one-shot tactic in use, `auto
<https://coq.inria.fr/refman/Reference-Manual010.html#sec390>`__. It
strings together chains of steps found from hint databases. I have
invested some effort in curating those hint databases, so I'd like to
continue using it as well.

However this presents a problem. **It isn't clear what the "right" way
is to incorporate** ``auto``\ **'s functionality into customized
tactics.**

For example, since (per its page) ``auto`` always either solves the
goal or does nothing, putting it inside a loop is no more powerful
than calling it once after the loop.

To see why this isn't ideal, consider a hypothetical way to directly
call a single "step" of ``auto``, which succeeds if it could make a
change (as opposed to only when it solved the goal) and fails
otherwise. Such single-steps could be interleaved with custom behavior
in a match repeat loop, allowing us to e.g. ``try contradiction`` or
``try congruence`` at intermediate points within the search tree.

Are there good design patterns for incorporating ``auto``'s
functionality into custom tactics?

Can ``auto``'s behavior be decomposed into "single step" tactics that
we can use?
|*)

(*|
Answer
******

What I would do instead would be to incorporate other tactics within
`auto
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto>`__.
You can do so by using the `Hint Extern num pat => mytactic : mybase
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:cmdv.hint-extern>`__
command where ``num`` is a priority number (0 being the highest
priority), ``pat`` a pattern to filter when the hint should be used
and ``mytactic`` and ``mybase`` are of course the tactic you want to
apply and the base you want to add the hint to (do not use the default
``core``; build up your custom base instead and call it with ``auto
with mybase``; if you do not want to include the lemmas from the
``core`` base in the search, add the fake base ``nocore``: ``auto with
mybase nocore``).

If you start relying on ``auto`` very much, I would switch instead to
the almost equivalent but better behaved `typeclasses eauto with
mybase
<https://coq.inria.fr/refman/addendum/type-classes.html#coq:tacn.typeclasses-eauto>`__.
Contrary to what its name suggests, it is a general purpose tactic
that has nothing to do with type classes (as long as you explicitly
provide the hint base on which it should be working). One of the main
behavior difference to know is that the search depth is unbounded by
default. So beware of possible infinite loops or fix a finite limit
with the variant ``typeclasses eauto num with mybase``.
|*)
