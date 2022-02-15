(*|
###########################################
Returning a record from a definition in Coq
###########################################

:Link: https://stackoverflow.com/q/45650879
|*)

(*|
Question
********

Suppose I've got a ``record`` that contains two ``nat``\ s.
|*)

Record toy := {
    num1 : nat;
    num2 : nat
  }.

(*|
I want to build a definition that given two ``nat``\ s returns a
``record`` containing those two ``nat``\ s.

.. code-block:: coq

    Definition args_to_toy_record (n1 : nat) (n2 : nat) : toy :=
      (* { num1 = n1; num2 = n2} ?? *)

Unfortunately, the official documentation only seems to cover the
simpler cases when the return type is a ``bool`` or a ``nat``. Is such
a thing possible in coq? If yes, what is the best method to achieve
it?
|*)

(*|
Answer
******

You had it almost right. You just need slightly different syntax:
|*)

Reset Initial. (* .none *)
Record toy := {
    num1 : nat;
    num2 : nat
  }.

Definition args_to_toy_record (n1 : nat) (n2 : nat) : toy :=
  {| num1 := n1; num2 := n2 |}.

(*|
Alternatively, you can use regular constructor syntax. Every record
``toto`` in Coq is declared as an inductive (sometimes, coinductive)
type with a single constructor ``Build_toto``, whose arguments are
exactly the fields of the record:
|*)

Reset args_to_toy_record. (* .none *)
Definition args_to_toy_record (n1 : nat) (n2 : nat) : toy :=
  Build_toy n1 n2.

(*|
You can also name the record constructor explicitly, like this:
|*)

Reset Initial. (* .none *)
Record toy := Toy {
                 num1 : nat;
                 num2 : nat
               }.

Definition args_to_toy_record (n1 : nat) (n2 : nat) : toy :=
  Toy n1 n2.
