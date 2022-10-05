(*|
###########################################
Unable to find an instance for the variable
###########################################

:Link: https://stackoverflow.com/q/8874951
|*)

(*|
Question
********

Context: I'm working on exercises in `Software Foundations
<http://www.cis.upenn.edu/~bcpierce/sf/>`__.

.. coq:: none
|*)

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S m) => evenb m
  end.

(*||*)

Theorem neg_move : forall x y : bool,
    x = negb y -> negb x = y.
Proof. Admitted.

Theorem evenb_n__oddb_Sn : forall n : nat,
    evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - Fail rewrite -> neg_move. (* .fails *)

(*| Before the last line, my subgoal is this: |*)

    Show. (* .unfold .goals *)

(*| And I want to transform it into this: |*)

    symmetry. (* .none *) apply neg_move. (* .none *) symmetry. (* .none *)
    Show. (* .unfold .goals *)
    Undo 3. (* .none *)

(*|
When I try to step through ``rewrite -> neg_move``, however, it
produces this error:
|*)

    Fail rewrite -> neg_move. (* .unfold .messages *)

(*|
I'm sure this is really simple, but what am I doing wrong? (Please
don't give anything away for solving ``evenb_n__oddb_Sn``, unless I'm
doing it completely wrong).
|*)

(*|
Answer
******

As danportin mentioned, Coq is telling you that it does not know how
to instantiate ``y``. Indeed, when you do ``rewrite -> neg_move``, you
ask it to replace some ``negb x`` by a ``y``. Now, what ``y`` is Coq
supposed to use here? It cannot figure it out.

One option is to instantiate ``y`` explicitly upon rewriting:

.. code-block:: coq

    rewrite -> neg_move with (y:=some_term).

This will perform the rewrite and ask you to prove the premises, here
it will add a subgoal of the form ``x = negb some_term``.

Another option is to specialize ``neg_move`` upon rewriting:

.. code-block:: coq

    rewrite -> (neg_move _ _ H)

Here ``H`` must be a term of type ``some_x = negb some_y``. I put two
wildcards for the ``x`` and the ``y`` parameters of ``neg_move`` since
Coq is able to infer them from ``H`` as being ``some_x`` and
``some_y`` respectively. Coq will then try to rewrite an occurence of
``negb some_x`` in your goal with ``some_y``. But you first need to
get this ``H`` term in your hypotheses, which might be some additional
burden...

(Note that the first option I gave you should be equivalent to
``rewrite -> (neg_move _ some_term)``)

Another option is ``erewrite -> negb_move``, which will add
uninstantiated variables that will look like ``?x`` and ``?y``, and
try to do the rewrite. You will then have to prove the premise, which
will look like ``(evenb (S (S n'))) = negb ?y``, and hopefully in the
process of solving this subgoal, Coq will find out what ``?y`` should
have been from the start (there are some restrictions though, and some
problems may arise is Coq solves the goal without figuring out what
``?y`` must be).

----

However, for your particular problem, it is quite easier:
|*)

    Show. (* .unfold .goals *)
    symmetry.
    Show. (* .unfold .goals *)
    apply neg_move.
    Show. (* .unfold .goals *)

(*|
And that's what you wanted (backwards, do another ``symmetry.`` if you
care).
|*)
