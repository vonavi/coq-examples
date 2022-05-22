(*|
##################################
Merge duplicate cases in match Coq
##################################

:Link: https://stackoverflow.com/q/37514976
|*)

(*|
Question
********

I have come by this problem many times: I have a proof state in Coq
that includes matches on both sides of an equality that are the same.

Is there a standard way to rewrite multiple matches into one?

Eg.

.. code-block:: coq

    match expression_evaling_to_Z with
    | Zarith.Z0 => something
    | Zarith.Pos _ => something_else
    | Zarith.Neg _ => something_else
    end = yet_another_thing.

And if I destruct on ``expression_evaling_to_Z`` I get two identical
goals. I would like to find a way to get only one of the goals.
|*)

(*|
Answer (ejgallego)
******************

A standard solution is to define "a view" of your datatype using a
type family that will introduce the proper conditions and cases when
destructed. For your particular case, you could do:
|*)

Require Import Coq.ZArith.ZArith.

Inductive zero_view_spec : Z -> Type :=
| Z_zero  :                      zero_view_spec Z0
| Z_zeroN : forall z, z <> Z0 -> zero_view_spec z.

Lemma zero_viewP z : zero_view_spec z.
Proof. now destruct z; [constructor|constructor 2|constructor 2]. Qed.

Lemma U z : match z with
            | Z0              => 0
            | Zpos _ | Zneg _ => 1
            end = 0.
Proof.
destruct (zero_viewP z).
Abort.

(*|
This is a common idiom in some libraries like math-comp, which
provides special support for instantiating the ``z`` argument of the
type family.
|*)

(*|
Answer (Anton Trunov)
*********************

You can write the ``match`` expression more succinctly:

.. code-block:: coq

    match expression_evaling_to_Z with
    | Z0 => something
    | Zpos _ | Zneg _ => something_else
    end = yet_another_thing.

But that will give you 3 subgoals when using ``destruct``.

In this particular case we may use the fact that you actually need to
distinguish the zero and non-zero cases, and it looks like a job for
the ``Z.abs_nat : Z -> nat`` function.

.. code-block:: coq

    Require Import Coq.ZArith.BinIntDef.

    match Z.abs_nat (expression_evaling_to_Z) with
    | O => something
    | S _ => something_else
    end = yet_another_thing.

This will get you only two subcases, but you need to destruct on
``Z.abs_nat (expression_evaling_to_Z)`` or introduce a new variable.
If you choose the 1st variant, then you'll probably need ``destruct
(...) eqn:Heq.`` to put the equation into context.

Basically this approach is about finding a new datatype (or defining
one) and a suitable function to map from the old type to the new one.
|*)

(*|
Answer (larsr)
**************

If you don't mind typing you can use ``replace`` to replace the RHS
with the LHS of your goal, which makes it trivial to solve, and then
you just have to prove once that the rewrite is indeed ok.
|*)

Open Scope Z.

Lemma L a b :
  match a + b with
  | Z0     => a + b
  | Zpos _ => b + a
  | Zneg _ => b + a
  end = a + b.
Proof.
  (* 1. replace the RHS with something trivially true *)
  replace (b + a) with (a + b).
  - (* 2. solve the branches in one fell swoop *)
    destruct (a + b); auto.
  - (* 3. solve only once what is required for the two brances *)
    apply Z.add_comm.
Qed.

(*|
Perhaps you can use some Ltac-fu or other lemma to not have to type in
the RHS manually too.
|*)
