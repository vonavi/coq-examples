(*|
################################################
Coq: a single notation for multiple constructors
################################################

:Link: https://stackoverflow.com/q/38060151
|*)

(*|
Question
********

Is it possible to define a single notation for multiple constructors
in Coq? If the constructors differ by their argument types, they might
be inferrable from them. A minimal (non-)working example:
|*)

Inductive A : Set :=
  a | b | c : C -> A | d : D -> A
  with C : Set := c1 | c2
  with D : Set := d1 | d2.

Notation "' x" := (_ x) (at level 19).
Check 'c1. (* .unfold *)

(*|
In this case, constructor inference doesn't work. Maybe there's
another way to specify a constructor as a variable?
|*)

(*|
Answer (Daniel Schepler)
************************

You can create a typeclass with the constructors as instances and let
the instance resolution mechanism infer the constructor to call for
you:

.. coq:: none
|*)

Reset Initial.

Inductive A : Set :=
  a | b | c : C -> A | d : D -> A
  with C : Set := c1 | c2
  with D : Set := d1 | d2.

(*||*)

Class A_const (X : Type) : Type :=
  a_const : X -> A.
Instance A_const_c : A_const C := c.
Instance A_const_d : A_const D := d.

Check a_const c1.
Check a_const d2.

(*|
By the way, with Coq 8.5, if you really want a notation ``' x`` to
result in the exact constructor applied to ``x``, rather than e.g.
``@a_const C A_const_c c1``, then you can use ltac-terms to accomplish
that:
|*)

Notation "' x" := ltac:(match constr:(a_const x) with
                        | @a_const _ ?f _ =>
                            let unfolded := (eval unfold f in f) in
                            exact (unfolded x)
                        end) (at level 0).
Check 'c1. (* .unfold *)
Check 'd2. (* .unfold *)

(*|
----

**A:** Indeed; depending on the particular application using a
``Canonical Structure`` could work very well here too.
|*)

(*|
Answer (Daniel Schepler)
************************

In fact, the idea of using an ltac-term leads to an entirely different
solution from the other one I posted:

.. coq:: none
|*)

Reset Initial.

Inductive A : Set :=
  a | b | c : C -> A | d : D -> A
  with C : Set := c1 | c2
  with D : Set := d1 | d2.

(*||*)

Notation "' x" := ltac:(let T := (type of x) in
                        let T' := (eval hnf in T) in
                        match T' with
                        | C => exact (c x)
                        | D => exact (d x)
                        end) (at level 0).
Check 'c1. (* .unfold *)
Check 'd2. (* .unfold *)

(*|
(Here the ``eval hnf`` part lets it work even if the type of the
argument isn't syntactically equal to ``C`` or ``D``, but it does
reduce to one of them.)
|*)
