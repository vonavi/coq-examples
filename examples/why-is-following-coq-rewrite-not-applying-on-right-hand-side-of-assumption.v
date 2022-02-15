(*|
###########################################################################
Why is following Coq rewrite not applying on right hand side of assumption?
###########################################################################

:Link: https://stackoverflow.com/q/46016461
|*)

(*|
Question
********

I have following Coq env.

.. coq:: none
|*)

Section foo.

  Variables n m : nat.
  Hypothesis IHm : forall n : nat, n + n = m + m -> n = m.
  Hypothesis H : S (n + S n) = S (m + S m).
  Hypothesis ll : forall k : nat, k + S k = S k + k.

(*||*)

  Goal False. (* .unfold .hyps *)

(*|
Doing ``rewrite ll in H``, only changes the LHS ``S (n + S n)`` to ``S
(S n + n)`` but not the RHS ``S (m + S m)``:
|*)

    rewrite ll in H. (* .unfold .hyps *)
Abort. (* .none *)
End foo. (* .none *)

(*|
``ll`` should be applicable on all variables of type ``nat``. What is
wrong here?

----

**A (ejgallego):** ``rewrite H`` will only use one instantiation of
``H``, you need to use the ``!`` quantifier to force more rewrites to
happen. Example:
|*)

Lemma ex n m : n = m -> n + 0 = m + 0.
Proof. now rewrite <- !plus_n_O. Qed.

(*|
Answer
******

Expanding on Emilio's comment, ``rewrite H`` and ``rewrite H in H'``
will first find an instantiation for all (dependently) quantified
variables of ``H``, and then replace all occurrences [#]_ of that
instantiated LHS with the RHS. I believe it finds the topmost/leftmost
instantiation in the syntax tree. So, for example, if you do this:
|*)

Goal forall a b,
    (forall x, x + 0 = x) -> (a + 0) * (a + 0) * (b + 0) = a * a * b.
  intros a b H.
  rewrite H.
Abort. (* .none *)

(*|
the ``rewrite H`` will choose to instantiate ``x`` with ``a``, and the
resulting goal will be ``a * a * (b + 0) = a * a * b``. You can prefix
the lemma with ``!`` (as in ``rewrite !H``) to mean "rewrite
everywhere, picking as many instantiations as you can", or with ``?``
(as in ``rewrite ?H``) to mean ``try rewrite !H``, i.e., you can pick
multiple instantiations, and also don't fail if you can't find any.

.. [#] There's actually a bit more nuance, which is that the
   replacement is done in a single pass with rewrite H and in multiple
   passes with ``rewrite ?H`` and ``rewrite !H``. This only shows up
   when the first replacement(s) expose other replacement locations
   that weren't previously available. This shows up, for example, if
   you rewrite with ``a + 0 = a`` in the goal ``(a + 0) + 0 = a``;
   ``rewrite H`` leaves the goal ``a + 0 = 0``.
|*)
