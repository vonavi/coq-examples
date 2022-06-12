(*|
#########################################
Using local notation inside a Coq theorem
#########################################

:Link: https://stackoverflow.com/q/30270240
|*)

(*|
Question
********

Suppose I want to prove a theorem about an object that is verbose to
spell out, say ``ABCDEFGHIJKLMNOPQRSTUVWXYZ``, such that the
unabbreviated theorem is

.. code-block:: coq

    Theorem verbose :
      prop_1 ABCDEFGHIJKLMNOPQRSTUVWXYZ
      -> prop_2 ABCDEFGHIJKLMNOPQRSTUVWXYZ
      -> prop_3 ABCDEFGHIJKLMNOPQRSTUVWXYZ
      -> prop_4 ABCDEFGHIJKLMNOPQRSTUVWXYZ
      -> prop_5 ABCDEFGHIJKLMNOPQRSTUVWXYZ.

Is there a way to use local notation inside a theorem, so I can
compress it to something like the following?

.. code-block:: coq

    Theorem succinct :
      prop_1 X -> prop_2 X -> prop_3 X -> prop_4 X -> prop_5 X
    where "X" := ABCDEFGHIJKLMNOPQRSTUVWXYZ.

I'd use regular notations if I'm using the verbose term repeatedly,
but for one-off cases it'd be nice if there were something like
``where`` for theorems, so I can reuse good names.
|*)

(*|
Answer (Andrew Swann)
*********************

You can use ``Section``\ s and ``Let`` for local definitions.

.. code-block:: coq

    Section thm.

    Let X := ABCDEFGHIJKLMNOPQRSTUVWXYZ.

    Theorem succinct : prop_1 X -> prop_2 X.

    ....

    End thm.
|*)

(*|
Answer (larsr)
**************

You can use ``Definition myobj := ABCDEFGHIJKLMNOPQRSTUVWXYZ.`` to
define a name for the object. Later, you can use ``unfold myobj.`` to
expand the name to its value.

To introduce it into a local proof environment, use ``remember``.
|*)

Require Import ZArith. (* .none *)
Open Scope Z_scope. (* .none *)
Theorem foo :
  forall x y z : Z, x + y - z = x + (y - z).
Proof.
  intros.
  remember (x + y) as bar.

(*| Now the environment is |*)

  Show. (* .unfold .messages *)

(*|
----

**Q:** Maybe the question didn't make it clear, but what I'm looking
for is a notation local to a theorem, so that simple variable names
like ``X`` can be reused without overloading. Your suggestion would
indeed be the best way if the object was used repeatedly across
multiple theorems.

**A:** Inside a proof you can do ``remember (foo + bar + ABDE) as Q.``
|*)
