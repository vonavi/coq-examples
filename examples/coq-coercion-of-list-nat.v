(*|
##############################
Coq - Coercion of ``list nat``
##############################

:Link: https://stackoverflow.com/q/70726083
|*)

(*|
Question
********

I would like to do a coercion from the type ``list nat`` to the type
``list bool``. I would think that this could be done in the following
way:

.. code-block:: coq

    From Coq Require Import Lists.List.

    Definition nat_to_bool (n : nat) : bool :=
      match n with
      | 0 => true
      | _ => false
      end.

    Definition list_nat_to_list_bool (l : list nat) : list bool :=
      map (fun n => (nat_to_bool n)) l.

    Coercion list_nat_to_list_bool : list nat >-> list bool.

However, this doesn't work. It seems like there is a fundamental issue
with using coercion on something of the form ``list nat``. Why does
this not work?
|*)

(*|
Answer
******

The `documentation
<https://coq.inria.fr/refman/addendum/implicit-coercions.html#classes>`__
states that a class name must be a defined name. Neither ``list nat``
nor ``list bool`` are defined names - they are both applications. You
must give the types between you want to define coercions a name as in:
|*)

From Coq Require Import Lists.List.

Definition nat_to_bool (n : nat) : bool :=
  match n with
  | 0 => true
  | _ => false
  end.

Definition list_nat := list nat.
Definition list_bool := list bool.

Definition list_nat_to_list_bool (l : list_nat) : list_bool :=
  map (fun n => (nat_to_bool n)) l.

Coercion list_nat_to_list_bool : list_nat >-> list_bool.

(*|
Please note that the coercion function must use these names - you
can't write ``list nat`` instead of ``list_nat``. Also the
applications of the coercion must use the defined names as in:
|*)

Definition test : list_bool := (1 :: nil) : list_nat.

(*|
I *guess* this is so because coercions might be done at the syntactic
level where type unifications would be difficult.

----

**Q:** So, if I have a function ``f`` whose inputs are of type ``list
bool``, and I want to use coercion to pass objects of type ``list
nat`` to it, I'd have to edit ``f`` so that its input type is
``list_bool`` instead? There isn't a way around this?

**A:** I am not an expert for coercions, but as far as I know and
understand the documentation, that's how it is, yes.
|*)
