(*|
##################################################
interactive theorem proving with no specified goal
##################################################

:Link: https://stackoverflow.com/questions/49569621/interactive-theorem-proving-with-no-specified-goal
|*)

(*|
Question
********

What's the best approach to do interactive theorem proving in Coq
without specifying a ``Theorem`` definition first? I'd like to state
some initial assumptions and definitions, and then interactively
explore transformations to see if I can prove any interesting theorems
without knowing them ahead of time. I'd like Coq to help me keep track
of the transformed assumptions and check that my rewrites are valid,
like when proving explicit theorems in interactive mode. Does Coq have
support for this use case?
|*)

(*|
Answer
******

One convenient method is to use the ``Variable``/``Hypothesis``
commands (they do the same thing) to add assumptions and introduce
example objects (e.g., ``Variable n:nat.`` introduces a nat you can
now work with). Then to get into theorem proving mode what I do
occasionally is ``Goal False.`` to start proving ``False``, just to
make sure I don't accidentally prove the theorem. You can also
``assert`` and ``admit`` things to get additional assumptions without
restarting the proof.

----

**Q:** ``Variable`` and ``Hypothesis`` are just aliases for ``Axiom``,
right? One of the drawbacks of using that is that they don't show up
above the horizontal line in interactive mode. I can make ``n1 : nat``
appear below the line with ``Variable n : nat. remember n as n1``, but
it also adds ``Heqn1: n1 = n``, which might get annoying when I add
more variables.

**A:** If you first open a section, then the variables and hypotheses
will appear on top of the horizontal line during interactive proofs.

**A:** Yes - more specifically, ``Variable``/``Hypothesis`` are
synonyms for ``Local Axiom`` when not in any section. ``Parameter``
and ``Conjecture`` are actually synonyms for ``Axiom``.
|*)
