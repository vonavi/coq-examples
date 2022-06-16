(*|
####################################
How to match a ``match`` expression?
####################################

:Link: https://stackoverflow.com/q/28454977
|*)

(*|
Question
********

I am trying to write a rule for hypotheses, formulated with a help of
``match`` construction:
|*)

Goal forall x : nat,
    (match x with | 0 => 0 | 1 => 5 | _ => 10 end = 5 -> x = 1)%nat.
intros. (* .unfold *)

(*|
How can I match such hypotheses? The following straight forward method
fails:

.. code-block:: coq

    match goal with
    | [H : match ?e with | ?a => ?x | ?b => ?y | ?c => ?z end = ?b] => idtac
    end.

    > Syntax error: 'end' expected after [branches] (in [match_constr]).
|*)

(*|
Answer
******

Pattern-matching on ``match`` statements is somewhat weird.

The first thing you should know is that, inside Coq, there's no such
thing as a ``match`` on several variables or with deep matching:
everything is translated in terms of simpler ``match`` statements.
Thus, the term you wrote is actually syntax sugar for the following
term:

.. code-block:: coq

    match x with
    | 0 => 0
    | S x' =>
        match x' with
        | 0 => 5
        | S x'' => 10
        end
    end

which is what Coq is hinting at when it prints your proof state. The
problem is that this syntax sugar doesn't work on Ltac patterns: thus,
when writing an Ltac pattern that mentions a ``match``, you should
always try to match it as if it were a one-level ``match``.

The second problem is that you can't bind the *pattern* part of a
``match``: something like

.. code-block:: coq

    match goal with
    | H : match ?x => _ | ?y => _ end = 5 |- _ => (* ... *)
    end.

doesn't really make sense in Ltac.

You have two choices for solving your problem, then:

1. Write down the ``match`` you expect with the exact list of
   constructors of your type on the pattern part, e.g.

   .. code-block:: coq

       match goal with
       | H : match x with 0 => _ | S _  => _ end = 5 |- _ => (* ... *)
       end.

2. Use the special ``match (* ... *) with _ => _ end`` syntax, which
   matches *any* ``match`` whatsoever:

   .. code-block:: coq

       match goal with
       | H : match x with _ => _ end = 5 |- _ => (* ... *)
       end

Often, as in your case, one still wants to consider *all* branches of
``match``, including deep ones. This idiom often comes in handy in
that case:
|*)

repeat match goal with
       | H : match ?x with _ => _ end = _ |- _ =>
           destruct x; try solve [inversion H]
       end.
