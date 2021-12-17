(*|
############################################
Dependent type as a function argument in Coq
############################################

:Link: https://stackoverflow.com/questions/58848680/dependent-type-as-a-function-argument-in-coq
|*)

(*|
Question
********

I am very new to Coq. I am trying to experiment with Coq's dependent
types. What I want to do, is to simply feed an even number to a
function. For example, in pseudo-code:

.. code::

    def next_even(n: {n: Integer | n is even}) :=
    {
      add n 2
    }

Then I want to utilize the function with different arguments, such as
(in pseudo-code):

.. code-block:: C

    next_even(1)    // Coq should show an error
    next_even(4)    // Coq should compute 6

So, in Coq, I want to do the following:

.. code-block:: coq

    Compute (next_even 1).
    Compute (next_even 4).

How can I construct it?
|*)

(*|
Answer
******

Here is a direct translation of your function in Coq:
|*)

From Coq Require Import Arith.

Definition add_two_even (n : {n : nat | Nat.even n = true}) : nat :=
  proj1_sig n + 1.

(*|
Note that you need the ``proj1_sig`` function to extract ``n`` from
the subset type ``{n : nat | Nat.even n = true}``. To use
``add_two_even``, you also need to go the other way around: go from a
number to an element of ``{n | Nat.even n = true}``. In Coq, this
requires manual proof. For concrete values of ``n``, this is easy:
|*)

(* The next command fails with a type checking error *)
Fail Compute add_two_even (exist _ 1 eq_refl). (* .fails *)
(* The next command succeeds *)
Compute add_two_even (exist _ 4 eq_refl).

(*|
The ``exist`` constructor wraps a value ``x`` with a proof of ``P x``,
producing an element of the subset type ``{x | P x}``. The ``eq_refl``
term is a proof of ``x = x`` for any value of ``x``. When ``n`` is a
concrete number, Coq can evaluate ``Nat.even n`` and find if
``eq_refl`` is a valid proof of ``Nat.even n = true``. When ``n`` is
``1``, ``Nat.even n = false``, and the check fails, leading to the
first error message. When ``n`` is ``4``, the check succeeds.

Things get more complicated when ``n`` is not a constant, but an
arbitrary expression. A proof that ``Nat.even n = true`` can require
detailed reasoning that must be guided by the user. For instance, we
know that ``Nat.even (n + n) = true`` for any value of ``n``, but Coq
does not. Thus, to call ``add_two_even`` on something of the form ``n
+ n``, we need to show a lemma.
|*)

Lemma add_n_n_even n : Nat.even (n + n) = true.
Proof.
  induction n as [|n IH]; trivial.
  now simpl; rewrite <- plus_n_Sm, IH.
Qed.

Definition foo (n : nat) :=
  add_two_even (exist _ (n + n) (add_n_n_even n)).

(*|
There are some tools for facilitating this style of programming, such
as the `equations plugin
<https://github.com/mattam82/Coq-Equations>`__, but the general wisdom
in the Coq community is that you should avoid subset types for
functions like ``add_two_even``, where the constraints do not
substantially simplify the properties about the function.

You can find many examples of good uses of subset types in the
`Mathematical Components <https://github.com/math-comp/math-comp>`__
libraries. For example, the libraries use subset types to define a
type ``n.-tuple T`` of lists of length ``n``, and a type ``'I_n`` of
integers bounded by ``n``. This allows us to define a total accessor
function ``tnth (t : n.-tuple T) (i : 'I_n) : T`` that extracts the
``i``\ th element of the list ``t``. If we define this accessor for
arbitrary lists and integers, we need to pass a default value to the
function to return when the index is out of bounds, or change the
function's signature so that it returns a value of type ``option T``
instead, indicating that the function can fail to return a value. This
change makes properties of the accessor function harder to state. For
example, consider the ``eq_from_tnth`` lemma, which says that two
lists are equal if all their elements are equal:

.. code-block:: coq

    eq_from_tnth:
      forall (n : nat) (T : Type) (t1 t2 : n.-tuple T),
        (forall i : 'I_n, tnth t1 i = tnth t2 i) -> t1 = t2

The statement of this lemma for arbitrary lists becomes more
complicated, because we need an extra assumption saying that the two
lists are of the same size. (Here, ``x0`` is the default value.)

.. code-block:: coq

    eq_from_nth:
      forall (T : Type) (x0 : T) (s1 s2 : list T),
      size s1 = size s2 ->
      (forall i : nat, i < size s1 -> nth x0 s1 i = nth x0 s2 i) -> s1 = s2
|*)
