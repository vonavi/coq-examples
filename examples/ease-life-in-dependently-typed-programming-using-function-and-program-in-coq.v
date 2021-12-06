(*|
####################################################################################
Ease life in dependently typed programming using ``Function`` and ``Program`` in Coq
####################################################################################

:Link: https://stackoverflow.com/questions/52262322/ease-life-in-dependently-typed-programming-using-function-and-program-in-coq
|*)

(*|
Question
********

I am trying to implement a dependently typed evaluator of STLC in Coq
using ``Program Fixpoint``. Since the language does not have fixed
point operator, I think the evaluator should terminate, though the
termination condition is not structural.

During my development, I find one source of headache is I simply can't
keep track of too many variables at the same time, and pattern
matching is too nested.

If it were about a mere ``Fixpoint``, I can just implement the body
using tactics, but when using ``Program Fixpoint`` or ``Function``, I
just cannot. Is there any trick to build body using tactics in this
case?

I am stuck at very end:
https://gist.github.com/HuStmpHrrr/0d92e646916ae9ec7ced3ff21724ba2d
|*)

(*|
Answer
******

When using ``Program``, you can simply leave underscores for parts of
your term you want to fill in using proof mode. Any underscores that
can be inferred will automatically be filled in and the remaining will
produce obligations. For example, you can write all of ``run`` in
proof mode by writing ``Program Fixpoint run ... {measure ...} := _.``
The measure will show up as an argument to ``run`` in the context.
|*)
