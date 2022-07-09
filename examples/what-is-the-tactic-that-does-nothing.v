(*|
#####################################
What is the tactic that does nothing?
#####################################

:Link: https://stackoverflow.com/q/69859665
|*)

(*|
Question
********

Sometimes it is useful to have a tactic which does nothing. I've tried
to search "empty tactic" or "null tactic" but these do not give me the
answer.
|*)

(*|
Answer
******

The tactic you are looking for is ``idtac``, short for "identity
tactic"

.. code::

    Tactic idtac (ident ​| string​ | natural)*

\

    Leaves the proof unchanged and prints the given tokens. Strings
    and naturals are printed literally. If ident is an Ltac variable,
    its contents are printed; if not, it is an error. `source
    <https://coq.inria.fr/refman/proof-engine/ltac.html#coq:tacn.idtac>`__

You can give ``idtac`` arguments, which are useful for debugging.
|*)
