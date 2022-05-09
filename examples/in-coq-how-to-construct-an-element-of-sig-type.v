(*|
#################################################
In Coq, How to construct an element of 'sig' type
#################################################

:Link: https://stackoverflow.com/q/44967359
|*)

(*|
Question
********

With a simple inductive definition of a type ``A``:
|*)

Require Import EqNat. (* .none *)
Inductive A : Set := mkA : nat -> A.

(* get ID of A *)
Definition getId (a : A) : nat := match a with mkA n => n end.

(*| And a subtype definition: |*)

(* filter that test ID of *A* is 0 *)
Definition filter (a : A) : bool :=
  if beq_nat (getId a) 0 then true else false.

(* cast bool to Prop *)
Definition IstrueB (b : bool) : Prop := if b then True else False.

(* subtype of *A* that only interests those who pass the filter *)
Definition subsetA : Set := {a : A | IstrueB (filter a) }.

(*|
I try this code to cast element of ``A`` to ``subsetA`` when
``filter`` passes, but failed to convenience Coq that it is a valid
construction for an element of 'sig' type:
|*)

Fail Definition cast (a : A) : option subsetA :=
  match filter a with
  | true => Some (exist _ a (IstrueB (filter a)))
  | false => None
  end. (* .unfold *)

(*|
So, Coq expects an actual proof of type ``IstrueB (filter a)``, but
what I provide there is type ``Prop``.

Could you shed some lights on how to provide such type? thank you.
|*)

(*|
Answer
******

First of all, there is the standard `is_true
<https://coq.inria.fr/library/Coq.Init.Datatypes.html#is_true>`__
wrapper. You can use it explicitly like so:
|*)

Reset subsetA. (* .none *)
Definition subsetA : Set := {a : A | is_true (filter a) }.

(*| or implicitly using the coercion mechanism: |*)

Reset subsetA. (* .none *)
Coercion is_true : bool >-> Sortclass.
Definition subsetA : Set := { a : A | filter a }.

(*|
Next, non-dependent pattern-mathching on ``filter a`` doesn't
propagate ``filter a = true`` into the ``true`` branch. You have at
least three options:

1. Use tactics to build your ``cast`` function:

  .. coq::
|*)

Definition cast (a : A) : option subsetA.
  destruct (filter a) eqn:prf.
  - exact (Some (exist _ a prf)).
  - exact None.
Defined.

(*|
2. Use dependent pattern-matching explicitly (search for "convoy
   pattern" on Stackoverflow or in `CDPT
   <http://adam.chlipala.net/cpdt/>`__):

   .. coq::
|*)

Definition cast' (a : A) : option subsetA :=
  match filter a as fa
        return (filter a = fa -> option subsetA)
  with
  | true => fun prf => Some (exist _ a prf)
  | false => fun _ => None
  end eq_refl.

(*|
3. Use the Program facilities:

   .. coq::
|*)

Require Import Coq.Program.Program.

Program Definition cast'' (a : A) : option subsetA :=
  match filter a with
  | true => Some (exist _ a _)
  | false => None
  end.

(*|
----

**A:** There is also ``Is_true`` in ``Bool``.
|*)
