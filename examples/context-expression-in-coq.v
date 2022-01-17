(*|
#############################
``context`` expression in Coq
#############################

:Link: https://stackoverflow.com/q/47361598
|*)

(*|
Question
********

I am trying to understand 'context' **expression** (opposed to
``context`` **pattern**\ ). In the manual it is described as:

    .. code-block:: coq

        context ident [ expr ]

    ident must denote a context variable bound by a context pattern of
    a match expression. This expression evaluates replaces the hole of
    the value of ident by the value of expr.

Could somebody share an example illustrating the usage of this
construct? I guess it must involve ``match`` using ``context`` pattern
and then abovementioned form to use matched context.
|*)

(*|
Answer
******

Here is an example that replaces ``fst (a, _)`` with ``a`` and ``snd
(_, b)`` with ``b``, but doesn't touch ``fst`` and ``snd`` applied to
anything other than pair:
|*)

Ltac unfold_proj_pair :=
  repeat match goal with
         | [ |- context G[fst (?a, _)] ]
           => let G' := context G[a] in change G'
         | [ |- context G[snd (_, ?b)] ]
           => let G' := context G[b] in change G'
         end.

(*|
(Note that ``cbn [fst snd]`` is a simpler way to do this, and that
also works under binders.)
|*)
