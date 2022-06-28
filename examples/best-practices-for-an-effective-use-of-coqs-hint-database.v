(*|
##########################################################
Best practices for an effective use of Coq's hint database
##########################################################

:Link: https://stackoverflow.com/q/14247771
|*)

(*|
Question
********

I've been told many times that I should use the hint database and
``auto`` because it's the best thing ever and whatnot. However, the
few times I tried to use that, I have been utterly annoyed by trivial
details. Here is one thing that keeps happening.
|*)

Section Annoying.

Variable T : Type.
Variable P : T -> Prop.

Axiom notP : forall x, ~ P x.
Hint Resolve notP.

Goal forall x : T, P x -> False.
  intros x.
  auto. (* nothing... *)
  replace (P x -> False) with (~ P x) by reflexivity.
  (* fold not. does not work, don't know why either but that is not
     the point here... *)
  auto.
Qed.

End Annoying.

(*|
Therefore, my question is: how do people use the hint database and not
run into such trouble. Are there goods rules of thumbs for an
effective hint database?
|*)

(*|
Answer
******

``auto`` works by applying unmodified theorems to goals. It looks for
what theorems to apply by a syntactic observation of their shape. So
you theorem ``notP`` will only apply to goals of the form

.. coq:: none
|*)

Variable P : Type -> Prop.

Goal forall x, ~ P x.
  intro.

(*||*)

  Show. (* .unfold .goals *)

(*|
A goal of the form ``P x -> False`` is not in this form syntactically.
In fact, the ``auto`` tactic works in the following manner: first use
``intros`` as much as possible, then try to apply theorems. So you
goal is transformed into
|*)

  unfold not. (* .none *) intros. (* .none *)
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
and then it tries to apply theorems that can prove ``False``.
Unfortunately, it tries only to apply theorems for which there is no
guessing of instantiations needed (theorems that can be used with the
tactic ``apply`` and do not require the ``with`` extension). So a
theorem with a statement of the form ``forall a, P a -> False`` would
never be used by ``auto``, because ``apply`` would complain that it
does know how to instantiate ``a``.

So, good candidate proofs for ``auto`` are proofs that you can do by
only using ``intros`` and ``apply``, with no instance of ``unfold`` or
``apply ... with`` and no manual application of theorems to arguments,
and where at each step, the rightmost formula (at the end of arrows)
of the theorem uses the predicate as the predicate appearing in the
goal's conclusion.

Your annoying example works because the goal at some point the main
formula is ``~ P x``, so the main symbol is ``not``, and ``auto`` has
the lemma ``notP`` in its table for this main symbol.

Here is an example that works well:
|*)

Variable my_le : nat -> nat -> Prop.

Hypotheses my_le_n : forall x, my_le x x.

Hypothesis my_le_S : forall x y, my_le x y -> my_le x (S y).

Hint Resolve my_le_n my_le_S.

Lemma toto : my_le 10 14.
Proof.
  auto.
Qed.

(*|
After the ``Hint`` command, ``auto`` has the two lemmas ``my_le_n``
and ``my_le_S`` in its table, to be used when the goals main symbol is
``my_le``. When looking at ``my_le 10 14``, it tries these two lemmas
in turn. The first fails, but the second one apply and produces a new
goal ``my_le 10 13``, this can be repeated several times until
``auto`` manages to apply ``my_le_n``. So ``auto`` explores a tree of
possibilities where the branching comes from the fact that there may
be several theorems applicable for a given goal. Also, the length of
the branches is limited to 5, so that ``my_le 10 15`` will not be
solved by ``auto``. You can change the length of branches by giving a
numeric argument to ``auto``. So ``auto 20`` will solve ``my_le 10
15`` and other similar instances.
|*)
