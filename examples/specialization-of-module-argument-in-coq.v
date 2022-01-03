(*|
########################################
Specialization of module argument in Coq
########################################

:Link: https://stackoverflow.com/q/54703204
|*)

(*|
Question
********

I have a module and I need to specialize one of its argument. I want
to use natural numbers instead of arbitrary
``UsualDecidableTypeFull``. How can I obtain such behaviour in Coq?

I defined some module:
|*)

Require Import Coq.Structures.Equalities. (* .none *)
Module PRO2PRE_mod
       (SetVars FuncSymb PredSymb PropSymb: UsualDecidableTypeFull).
  (* ... *)
End PRO2PRE_mod.

(*| Then I specialized the last of the arguments ``PropSymb``. |*)

Require Import Arith.PeanoNat.
Module m2 : UsualDecidableTypeFull.
  Definition t := nat.
  Definition eq := @eq nat.
  Definition eq_refl := @eq_refl nat.
  Definition eq_sym := @eq_sym nat.
  Definition eq_trans := @eq_trans nat.
  Definition eq_equiv : Equivalence eq := Nat.eq_equiv.
  Definition eq_dec := Nat.eq_dec.
  Definition eqb := Nat.eqb.
  Definition eqb_eq := Nat.eqb_eq.
End m2.

(*| This module needs specialization of ``PropVars``: |*)

Module SWAP_mod
       (SetVars FuncSymb PredSymb : UsualDecidableTypeFull).

  Module PRE := PRO2PRE_mod SetVars FuncSymb PredSymb m2.
  Import PRE.

  Theorem test : m2.t.
    Fail exact 0. (* .fails *) (* ERROR HERE! *)
  Abort.

End SWAP_mod.

(*|
How to use theorems about natural numbers inside the last module? (I
think I don't understand something about using modules... Maybe we
need somehow to coerce the type ``m2.t`` to the type ``nat``?)
|*)

(*|
Answer
******

Indeed, the use of ``: UsualDecidableTypeFull`` in the definition of
``m2`` hides completely the implementation details of ``m2``. From the
outside, ``m2.t`` is an unknown type.

Sometimes, this is exactly what you want. For example, you may want to
abstract away a type defined in a module so that the users cannot
manipulate values of this type without using the functions that you
gave to them in the module. You can thus ensure that they will not
break some invariants.

However, in your case, you need to remember that ``m2.t`` is actually
``nat``, you have at least these two options:

- Make the interface transparent with ``Module m2 <:
  UsualDecidableTypeFull``. When using this, Coq just verifies that
  the definition of the module complies with the signature, but does
  not hide the content of the module.
- If you still want to hide part of the module, you can also use

  .. coq::
|*)

Reset m2. (* .none *)
Module m2 : UsualDecidableTypeFull with Definition t := nat.

(*|
  In this case, from the outside, ``m2.t`` is known to be ``nat``, but
  the other fields of ``m`` are masked. For instance, the body of
  ``m2.eqb`` is hidden.
|*)
