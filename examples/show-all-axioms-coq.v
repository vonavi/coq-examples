(*|
###################
Show all axioms Coq
###################

:Link: https://stackoverflow.com/q/37562911
|*)

(*|
Question
********

I want to see all axioms which were used by my proof. What are the
easiest ways to obtain such information? Which commands or scripts or
tools I shall use? I am interested in either all axioms or all used
axioms.
|*)

(*|
Answer
******

You should use the

.. code-block:: coq

    Print Assumptions foobar.

vernacular command, described `here
<https://coq.inria.fr/refman/Reference-Manual008.html#hevea_command99>`__
|*)
