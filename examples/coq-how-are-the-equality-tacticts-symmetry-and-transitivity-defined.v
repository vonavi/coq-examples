(*|
############################################################################
Coq: How are the equality tactics ``symmetry`` and ``transitivity`` defined?
############################################################################

:Link: https://stackoverflow.com/q/71024340
|*)

(*|
Question
********

I'm interested in how the Coq tactics ``symmetry`` and
``transitivity`` actually work. I've read the Coq manual but this only
describes what they do, not how they operate on a proof and change the
proof states. As an example of what I'm looking for, in *Interactive
Theorem Proving and Program Development*, the authors state that "The
reflexivity tactic actually is synonymous with ``apply refl_equal``"
(p. 124). But, the author refers the reader to the reference manual
for ``symmetry`` and ``transitivity``. I haven't found a good
description of things that these two tactics are synonymous with in
the same way.

For clarification, the reason why I ask is that I have defined a path
space ``paths {A : UU} : A -> A -> UU`` notated ``a = b`` (like in
``UniMath``) which acts like an equivalence relation except for that
``a = b`` is not a proposition but a type. For this reason I was
unable to add this relation as an equivalence relation using ``Add
Parametric Relation``. I'm trying to cook up a version of ``symmetry``
and ``transitivity`` with Ltac for this path space relation but I
don't know how to change the proof state; knowing how ``symmetry`` and
``transitivity`` actually work might help.
|*)

(*|
Answer
******

These tactics only apply the lemmas corresponding to symmetry and
transitivity of the relation it finds in the goal. These are found
using the type classes mechanism.

For instance you could declare
|*)

From Coq Require Import RelationClasses.

Variables (A : Type) (R : A -> A -> Prop). (* .none *)
Instance trans : Transitive R.

(*|
which would ask you to prove ``R`` is transitive and then you would be
able to use the tactic ``transitivity`` to prove ``R x y``.
|*)
