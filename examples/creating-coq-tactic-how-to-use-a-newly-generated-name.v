(*|
#######################################################
Creating Coq tactic: how to use a newly generated name?
#######################################################

:Link: https://stackoverflow.com/q/71443387
|*)

(*|
Question
********

I want to create a Coq tactic that looks something like the following.
I assert a proposition named ``H``, I prove that proposition, and then
I use ``simpl`` within that proposition. The tactic would look
something like this:
|*)

Tactic Notation "foo" :=
  assert (True) as H; try apply I;
  simpl in H.

(*|
However, instead of using the name ``H`` for this hypothesis, I want
Coq to generate a new name for me. The problem is, how can I then use
``simpl`` in this hypothesis?

.. code-block:: coq

    Tactic Notation "foo" :=
      assert (True) as ?; try apply I;
      simpl in (* what? *).

Is there a way that I can generate a hypothesis name, and then refer
back to it within the same tactic?
|*)

(*|
Answer
******

You can use the ``fresh`` tactic for this. Here is an example:
|*)

Tactic Notation "foo" :=
  let H := fresh "H" in
  assert True as H; try apply I; simpl in H.

Goal False.
foo. (* H : True *)
foo. (* H, H0 : True *)
Abort.
