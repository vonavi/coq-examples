(*|
###############################
How to optimize a search in Coq
###############################

:Link: https://stackoverflow.com/q/19747308
|*)

(*|
Question
********

I have a simple search function for a property that I am interested
in, and a proof that the function is correct. I want to evaluate the
function, and use the correctness proof to get the theorem for the
original property. Unfortunately, evaluation in Coq is very slow. As a
trivial example, consider looking for square roots:
|*)

(* Coq 8.4
   A simple example to demonstrate searching.
   Timings are rough and approximate. *)

Require Import Peano_dec.

Definition SearchSqrtLoop :=
  fix f i n := if eq_nat_dec (i * i) n
               then i
               else match i with
                    | 0 => 0 (* ~ Square n \/ n = 0 *)
                    | S j => f j n
                    end.

Definition SearchSqrt n := SearchSqrtLoop n n.

(* Compute SearchSqrt 484.
   takes about 30 seconds. *)

Theorem sqrt_484a : SearchSqrt 484 = 22.
  apply eq_refl. (* 100 seconds *)
Qed. (* 50 seconds *)

Theorem sqrt_484b : SearchSqrt 484 = 22.
  vm_compute. (* 30 seconds *)
  apply eq_refl.
Qed. (* 30 seconds *)

Theorem sqrt_484c (a : nat) : SearchSqrt 484 = 22.
  apply eq_refl. (* 100 seconds *)
Qed. (* 50 seconds *)

Theorem sqrt_484d (a : nat) : SearchSqrt 484 = 22.
  vm_compute. (* 60 seconds *)
  apply eq_refl.
Qed. (* 60 seconds *)

(*|
Now try the corresponding function in Python:

.. code-block:: python

    def SearchSqrt(n):
      for i in range(n, -1, -1):
        if i * i == n:
          return i
      return 0

or slightly more literally

.. code-block:: python

    def SearchSqrtLoop(i, n):
      if i * i == n:
        return i
      if i == 0:
        return 0
      return SearchSqrtLoop(i - 1, n)

    def SearchSqrt(n):
      return SearchSqrtLoop(n, n)

The function is nearly instant in Python, but takes minutes in Coq,
depending on exactly how you try to call it. Also curious is that
putting an extra variable in makes ``vm_compute`` take twice as long.

I understand that everything is done symbolically in Coq, and thus
slow, but it would be very useful if I could directly evaluate simple
functions. Is there a way to do it? Just using native integers instead
of linked lists would probably help a lot.
|*)

(*|
Answer (user1861759)
********************

You'll get a speedup if you use binary arithmetic instead of unary
arithmetic. Take a look at ``NArith`` and ``ZArith``.

http://coq.inria.fr/library/

You'll also get a speedup if you run your code on OCaml, Haskell, or
Scheme instead.

http://coq.inria.fr/refman/Reference-Manual025.html
|*)

(*|
Answer (Anton Trunov)
*********************

There is a much more efficient function for finding square roots in
the standard library (`sqrt
<https://coq.inria.fr/library/Coq.Init.Nat.html#sqrt>`__):

    The following square root function is linear (and tail-recursive).
    With Peano representation, we can't do better. For faster
    algorithm, see ``Psqrt``/``Zsqrt``/``Nsqrt``...

.. coq::
|*)

Require Import Coq.Init.Nat.

Theorem sqrt_484a_v2 : sqrt 484 = 22.
  Time apply eq_refl.
  Time Qed.

(*|
As ``Time`` tells us it works much faster (around 200 times faster
than ``sqrt_484a``).

The reason for this performance difference lies in the fact that
``SearchSqrt`` squares its first argument on each iteration, which is
an expensive operation.

``sqrt``'s implementation, on the other hand, is based on the `Odd
Number Theorem <http://mathworld.wolfram.com/OddNumberTheorem.html>`__
(``1 + 3 + 5 + ...`` is a square number). One just needs to count the
number of increasing intervals that can be fitted into the input
argument ``n`` and that would be the `integer square root
<https://en.wikipedia.org/wiki/Integer_square_root>`__ of ``n``. E.g.
``22 = (1 + 3 + 5 + 7) + 6``, which means there are 4 intervals (of
lengths ``1``, ``3``, ``5``, and ``7``) in 22, so ``sqrt 22 = 4`` (and
we are not interested in the residual value 6).
|*)
