(*|
###########################################################################
What's the difference between ``Program Fixpoint`` and ``Function`` in Coq?
###########################################################################

:Link: https://stackoverflow.com/q/44606245
|*)

(*|
Question
********

They seem to serve similar purposes. The one difference I've noticed
so far is that while ``Program Fixpoint`` will accept a compound
measure like ``{measure (length l1 + length l2)}``, ``Function`` seems
to reject this and will only allow ``{measure length l1}``.

Is ``Program Fixpoint`` strictly more powerful than ``Function``, or
are they better suited for different use cases?
|*)

(*|
Answer
******

This may not be a complete list, but it is what I have found so far:

- As you already mentioned, ``Program Fixpoint`` allows the measure to
  look at more than one argument.
- ``Function`` creates a ``foo_equation`` lemma that can be used to
  rewrite calls to ``foo`` with its RHS. Very useful to avoid problems
  like `Coq simpl for Program Fixpoint
  <https://stackoverflow.com/q/36329256/946226>`__.
- In some (simple?) cases, ``Function`` can define a ``foo_ind`` lemma
  to perform induction along the structure of recursive calls of
  ``foo``. Again, very useful to prove things about ``foo`` without
  effectively repeating the termination argument in the proof.
- ``Program Fixpoint`` can be tricked into supporting nested
  recursion, see https://stackoverflow.com/a/46859452/946226. This is
  also why ``Program Fixpoint`` can `define the Ackermann
  <https://stackoverflow.com/questions/10292421/error-in-defining-ackermann-in-coq>`__
  function when ``Function`` cannot.
|*)
