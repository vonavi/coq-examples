(*|
########################################################
How can I write a function of the following form in Coq?
########################################################

:Link: https://stackoverflow.com/q/47947777
|*)

(*|
Question
********

.. code-block:: coq

    f x = f (g subtermOfX)

Is recursion only allowed if the arg to the function is a direct
subterm of the arg passed so that Coq can see that it actually
terminates?
|*)

(*|
Answer
******

It's possible to write such function ``f`` if function ``g`` preserves
the property of being a subterm.

Some of the standard functions have this property, e.g. ``pred``,
``sub``:
|*)

From Coq Require Import Arith List.
Import ListNotations.

Fixpoint foo (x : nat) : nat :=
  match x with
  | O => 42
  | S x' => foo (pred x')       (* foo (x' - 1) works too *)
  end.

(*|
On the other hand some (standard) functions do not have this property,
but can be rewritten to remedy this deficiency. E.g. the standard
``tl`` function does not preserve the subterm property, so the
following fails:
|*)

Fail Fixpoint bar (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs' => bar (tl xs')
  end. (* .fails *)

(*| but if we redefine the tail function like so |*)

Fixpoint new_tl {A : Type} (xs : list A) :=
  match xs with
  | [] => xs                    (* `tl` returns `[]` here *)
  | _ :: xs' => xs'
  end.

(*| we can recover the desired property: |*)

Fixpoint bar (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs' => bar (new_tl xs')
  end.

(*|
The only difference between ``tl`` and ``new_tl`` is that in the case
of empty input list ``tl`` returns ``[]``, but ``new_tl`` returns the
original list.
|*)
