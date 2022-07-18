(*|
###############################################################################
How does one build the list of only true elements in Coq using dependent types?
###############################################################################

:Link: https://stackoverflow.com/q/71518511
|*)

(*|
Question
********

I was going through the Coq book `from the maths perspective
<https://math-comp.github.io/mcb/>`__. I was trying to define a
dependently typed function that returned a length list with ``n``
trues depending on the number trues we want. Coq complains that things
don't have the right type but when I see it if it were to unfold my
definitions when doing the type comparison it should have worked but
it doesn't. Why?

Code:
|*)

Module playing_with_types2.
  Inductive Vector {A : Type} : nat -> Type :=
  | vnil : Vector 0
  | vcons: forall n : nat, A -> Vector n -> Vector (S n).

  Definition t {A : Type} (n : nat) : Type :=
    match n with
    | 0 => @Vector A 0
    | S n' => @Vector A (S n')
    end.
  Check t. (* nat -> Type *)
  Check @t. (* Type -> nat -> Type *)

  (* meant to mimic Definition g : forall n: nat, t n. *)
  Fail Fixpoint g (n : nat) : t n :=
    match n with
    | 0 => vnil
    | S n' => vcons n' true (g n')
    end. (* .fails *)

(*| Coq's error: |*)
  Fail Fixpoint g (n : nat) : t n :=
    match n with
    | 0 => vnil
    | S n' => vcons n' true (g n')
    end. (* .unfold .messages *)

(*|
i.e. ``t ?n@{n1:=0}`` is ``Vector 0``... no?
|*)

(*|
Answer
******

In this case, it looks like Coq does not manage to infer the return
type of the ``match`` expression, so the best thing to do is to give
it explicitly:
|*)

  Fail Fixpoint g (n : nat) : t n :=
    match n return t n with
    | 0 => vnil
    | S n' => vcons n' true (g n')
    end. (* .fails *)

(*|
Note the added ``return`` clause.

Then the real error message appears:
|*)

  Fail Fixpoint g (n : nat) : t n :=
    match n return t n with
    | 0 => vnil
    | S n' => vcons n' true (g n')
    end. (* .unfold .messages *)

(*|
And this time it is true that in general ``t n'`` is not the same as
``Vector n'`` because ``t n'`` is stuck (it does not know yet whether
``n'`` is ``0`` or some ``S n''``).
|*)
