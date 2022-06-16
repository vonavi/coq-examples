(*|
################################################################
How to forbid ``simpl`` tactic to unfold arithmetic expressions?
################################################################

:Link: https://stackoverflow.com/q/28432187
|*)

(*|
Question
********

The ``simpl`` tactic unfolds expressions like ``2 + a`` to "match
trees" which doesn't seem simple at all. For example:

.. coq:: none
|*)

Require Import ZArith ssreflect.
Open Scope Z_scope.

(*||*)

Goal forall i : Z, (fun x => x + i) 3 = i + 3.
  simpl. (* .unfold *)

(*|
How to avoid such complications with ``simpl`` tactic?

This particular goal can be solved with ``omega``, but if it is a bit
more sophisticated, ``omega`` fails, and I have to resort to something
like: ``replace (2 + a) with (a + 2). simpl; replace (a + 2) with (2 +
a)``.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

You can control definition unfolding with the ``Transparent`` and
``Opaque`` commands. In your example, you should be able to say
something like
|*)

  Restart. (* .none *)
  Opaque Z.add.
  simpl.
  Transparent Z.add.

(*|
Alternatively, the ``Arguments`` `command
<https://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#hevea_command232>`__
can be used to instruct the ``simpl`` tactic to avoid simplifying
terms in certain contexts. E.g.
|*)

  Restart. (* .none *)
  Arguments Z.add _ _ : simpl nomatch.

(*|
does the trick for me in your case. What this particular variant does
is to avoid simplifying a term when a big, ugly ``match`` would appear
in head position after doing so (what you saw in your example). There
are other variants too, however.

Finally, just for completeness, the `Ssreflect
<http://ssr.msr-inria.inria.fr/>`__ library provides nice
infrastructure for making certain definitions opaque locally. So you
could say something like
|*)

  rewrite (lock Z.add) /= -lock.
Abort. (* .none *)

(*|
meaning "lock ``Z.add``, so that it won't simplify, then simplify the
remaining of the expression (the ``/=`` switch), then unlock the
definition again (``-lock``)".
|*)

(*|
Answer (pielemma)
*****************

You can tweak how the simpl tactic behaves so you get less matches.
|*)

Reset Initial. (* .none *)
Require Import Coq.ZArith.ZArith.

Goal forall i : Z, ((fun x => (x + i)%Z) 3%Z = (i + 3)%Z).
  Arguments Z.add x y : simpl nomatch.
  simpl.

(*|
Read more about it `here
<https://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#hevea_tactic135>`__.

Otherwise you can use `other tactics
<https://coq.inria.fr/distrib/current/refman/tactic-index.html>`__
that allow you to choose how to reduce. ``cbn beta``, for example.
|*)
