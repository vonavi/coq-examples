(*|
############################################
``Definition`` vs ``Notation`` for constants
############################################

:Link: https://stackoverflow.com/q/35180475
|*)

(*|
Question
********

I'm extending an existing project (Featherweight Java formalization),
and there are a number of constants, such as:
|*)
Parameters var typ : Type. (* .none *)
Notation env := (list (var * typ)).

(*| What would change if I used ``Definition`` instead: |*)

Reset Initial. (* .none *)
Parameters var typ : Type. (* .none *)
Definition env := list (var * typ).

(*|
Why did the author use ``Notation`` here?
|*)

(*|
Answer
******

Whenever you try to apply or rewrite with a lemma, there's a component
in Coq called the *unifier* that tries to find out how to instantiate
your lemma so that it can work with the situation at hand (and
checking that it indeed applies there). The behavior of this unifier
is a bit different depending on whether you use notations or
definitions.

Notations are invisible to Coq's theory: they only affect the parsing
and printing behavior of the system. In particular, the unifier
doesn't need to explicitly unfold a notation when analyzing a term.
Definitions, on the other hand, must be explicitly unfolded by the
unifier. The problem is that the unifier works *heuristically*, and
cannot tell with 100% certainty when some definition must be unfolded
or not. As a consequence, we often find ourselves with a goal that
mentions a definition that the unifier doesn't unfold by itself,
preventing us from applying a lemma or rewriting, and having to
manually add a call to unfold ourselves to get it to work.

Thus, notations can be used as a hack to help the unifier understand
what an abbreviation means without manual unfolding steps.
|*)
