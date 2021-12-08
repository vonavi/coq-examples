(*|
#######################################################
Why does Coq.Init.Logic define the notation ``A -> B``?
#######################################################

:Link: https://stackoverflow.com/questions/52247439/why-does-coq-init-logic-define-the-notation-a-b
|*)

(*|
Question
********

The Coq Standard Library file ``Coq.Init.Logic``, which can be found
`here <https://coq.inria.fr/library/Coq.Init.Logic.html>`__, contains
the statement
|*)

Locate "->". (* .unfold .messages *)

(*|
I don't understand how this is possible, given that the symbol ``->``
already has a built-in meaning. Is ``->`` overwritten by this?

If I type in ``A -> B``, how does Coq know if I mean ``A -> B`` or
``forall (x : A), B``?

Yes, I know the two propositions are logically equivalent, but
shouldn't this be a theorem instead of a notation?

----

As you can tell, I've not had much experience with Coq, but I want to
understand the details.
|*)

(*|
Answer
******

The ``->`` symbol is actually defined by the notation you found in
``Coq.Init.Logic``! While ``forall`` is built-in, ``->`` is defined
using the notation system. The ``Coq.Init.Logic`` module is loaded
automatically into Coq because it's exported by `Coq.Init.Prelude
<https://coq.inria.fr/library/Coq.Init.Prelude.html>`__, which is why
you immediately have access to it.

When you write ``A -> B`` it's interpreted using the notation, which
is ``forall (_:A), B``; this is syntactically similar to ``forall
(x:A), B``, except that the expression ``B`` isn't allowed to depend
on ``x``. There's no ambiguity - this is the only definition for ``A
-> B``, and indeed if you load Coq without the prelude (eg, by passing
the ``-ninety`` flag) ``A -> B`` will not parse.

One aspect of Coq that makes ``->`` seem built-in is that the notation
is *bidirectional* - it applies to both parsing and to printing. This
is why you see ``->`` in your goals and when you use ``Check`` and
``Search``. Here there is real ambiguity; in this case, if a ``forall
(x:A), B`` has a ``B`` that does not depend on ``x``, Coq prefers to
print it using the notation rather than the built-in syntax. If you
turn off printing of notations (``Unset Printing Notation.``) you'll
see ``forall (_:A), B`` everywhere you used to see ``A -> B``. Of
course, if you have a function type with a real dependency, then Coq
needs to use ``forall (x:A), B`` since ``B`` needs to refer to the
variable ``x``.
|*)
