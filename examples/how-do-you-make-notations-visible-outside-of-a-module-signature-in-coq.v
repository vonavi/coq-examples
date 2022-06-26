(*|
#######################################################################
How do you make notations visible outside of a module signature in Coq?
#######################################################################

:Link: https://stackoverflow.com/q/15720888
|*)

(*|
Question
********

I've defined a module signature in Coq that defines several notations.
When I try to use these notations outside of the signature however,
Coq fails. A simplified version of my code is given below. Any help
would be appreciated.
|*)

Module Type Field_Axioms.

Delimit Scope Field_scope with F.
Open Scope Field_scope.

Parameter Element : Set.

Parameter addition : Element -> Element -> Element.

Infix " + " := addition : Field_scope. (* ASSIGNS THE "+" OPERATOR TO SCOPE. *)

End Field_Axioms.

Module Type Ordered_Field_Axioms.

  Declare Module Field : Field_Axioms.

  Print Scope Field_scope. (* SHOWS THAT THE SCOPE IS EMPTY. *) (* .unfold *)

End Ordered_Field_Axioms.

(*|
Answer
******

You can replace:

.. code-block:: coq

    Declare Module Field : Field_Axioms.

with:

.. code-block:: coq

    Declare Module Import Field : Field_Axioms.
|*)
