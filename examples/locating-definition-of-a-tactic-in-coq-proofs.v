(*|
#############################################
Locating definition of a tactic in Coq proofs
#############################################

:Link: https://stackoverflow.com/q/13623319
|*)

(*|
Question
********

In studying Coq proofs of other authors, I often encounter a tactic,
lets say ``inv eq Heq`` or ``intro_b``. I want to understand such
tactics.

How can I find if it is a Coq tactic or a tactic notation defined
somewhere in my current project?

Second, is there a way to find its definition?

I used ``SearchAbout``, ``Search``, ``Locate`` and ``Print`` but could
not find answers to the above questions.
|*)

(*|
Answer (Ptival)
***************

You should be able to use

.. code-block:: coq

    Print Ltac <tacticname>.

to print the code of a user-defined tactic (according to the
`documentation
<http://coq.inria.fr/distrib/V8.4/refman/Reference-Manual012.html#@command252>`__).

----

To find where it is defined... I guess you're going to need grep
unfortunately, ``Locate`` does not work for tactics names it seems.

----

**A:** ``Locate Ltac`` is the tactic version of ``Locate``
|*)

(*|
Answer (Clément)
****************

As mentioned before, ``Print Ltac ...`` prints the code of a
user-defined tactic.

To locate a user-defined tactic (i.e. to know where its defined), use
``Locate Ltac ...``. It gives you the fully qualified name. Then use
``Locate Library`` to find the corresponding file.
|*)
