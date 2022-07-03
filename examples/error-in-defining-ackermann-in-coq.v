(*|
##################################
Error in defining Ackermann in Coq
##################################

:Link: https://stackoverflow.com/q/10292421
|*)

(*|
Question
********

I am trying to define the Ackermann-Peters function in Coq, and I'm
getting an error message that I don't understand. As you can see, I'm
packaging the arguments ``a, b`` of Ackermann in a pair ``ab``; I
provide an ordering defining an ordering function for the arguments.
Then I use the ``Function`` form to define Ackermann itself, providing
it with the ordering function for the ``ab`` argument.
|*)

Require Import Recdef.

Definition ack_ordering (ab1 ab2 : nat * nat) :=
  match ab1, ab2 with
  | (a1, b1), (a2, b2) => a1 > a2 \/ (a1 = a2 /\ b1 > b2)
  end.

Fail Function ack (ab : nat * nat) {wf ack_ordering ab} : nat :=
  match ab with
  | (0, b) => b + 1
  | (a, 0) => ack (a - 1, 1)
  | (a, b) => ack (a - 1, ack (a, b - 1))
  end. (* .fails .unfold *)

(*|
I'm not sure what bothers Coq, but searching the internet, I found a
suggestion there may be a problem with using a recursive function
defined with an ordering or a measure, where the recursive call occurs
within a match. However, using the projections ``fst`` and ``snd`` and
an ``if-then-else`` generated a different error message. Can someone
please suggest how to define Ackermann in Coq?
|*)

(*|
Answer (Anton Trunov)
*********************

It seems like ``Function`` can't solve this problem. However, its
cousin ``Program Fixpoint`` can.

Let's define some lemmas treating well-foundedness first:
|*)

Reset Initial. (* .none *)
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Arith.

Definition lexicographic_ordering (ab1 ab2 : nat * nat) : Prop :=
  match ab1, ab2 with
  | (a1, b1), (a2, b2) => a1 < a2 \/ (a1 = a2 /\ b1 < b2)
  end.

(* this is defined in stdlib, but unfortunately it is opaque *)
Lemma lt_wf_ind : forall n (P : nat -> Prop),
    (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof. intro p. intros. elim (lt_wf p). auto with arith. Defined.

(* this is defined in stdlib, but unfortunately it is opaque too *)
Lemma lt_wf_double_ind : forall P : nat -> nat -> Prop,
    (forall n m,
        (forall p (q : nat), p < n -> P p q) ->
        (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p. pattern p. apply lt_wf_ind.
  intros n H q. pattern q. apply lt_wf_ind. auto.
Defined.

Lemma lexicographic_ordering_wf : well_founded lexicographic_ordering.
Proof.
  intros (a, b). pattern a, b. apply lt_wf_double_ind.
  intros m n H1 H2.
  constructor. intros (m', n') [G | [-> G]].
  - now apply H1.
  - now apply H2.
Defined.

(*| Now we can define the Ackermann-Péter function: |*)

Program Fixpoint ack (ab : nat * nat) {wf lexicographic_ordering ab} : nat :=
  match ab with
  | (0, b) => b + 1
  | (S a, 0) => ack (a, 1)
  | (S a, S b) => ack (a, ack (S a, b))
  end.
Next Obligation.
  inversion Heq_ab. subst. left. auto. Defined.
Next Obligation.
  apply lexicographic_ordering_wf. Defined.

(*|
Some simple tests demonstrating that we can compute with ``ack``:
|*)

Example test1 : ack (1, 2) = 4 := eq_refl.
Example test2 : ack (3, 4) = 125 := eq_refl. (* this may take several seconds *)

(*|
----

Using the `Equations <http://mattam82.github.io/Coq-Equations/>`__
plugin by M. Sozeau and C. Mangin it is possible to define the
function this way:

.. code-block:: coq

    From Equations Require Import Equations Subterm.

    Equations ack (p : nat * nat) : nat :=
      ack p by rec p (lexprod _ _ lt lt) :=
      ack (pair 0 n) := n + 1;
      ack (pair (S m) 0) := ack (m, 1);
      ack (pair (S m) (S n)) := ack (m, ack (S m, n)).

Unfortunately, it's not possible to use the ``( , )`` notation for
pairs due to `issue #81
<https://github.com/mattam82/Coq-Equations/issues/81>`__. The code is
taken from Equation's test suite: `ack.v
<https://github.com/mattam82/Coq-Equations/blob/71b3b266563b18b47a8bd2677e65e94f08674283/test-suite/ack.v>`__.
|*)

(*|
Answer (wires)
**************

You get this error because you are referencing the ``ack`` function
while you are defining it. Self reference is only allowed in
``Fixpoint``\ s (ie. recursive functions) but the problem is, as you
probably know, that the Ackermann function is not a primitive
recursive function.

See `Coq'Art section 4.3.2.2
<http://books.google.nl/books?id=m5w5PRj5Nj4C&pg=PA95>`__ for some
more information on this.

So one alternative way to define it is by inlining a second recursive
function that is structurally recursive for the second argument; so
something like
|*)

Reset Initial. (* .none *)
Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
             match m with
             | O => ack p 1
             | S q => ack p (ackn q)
             end
           in ackn m
  end.

(*|
----

**Q:** I wasn't using ``Fixpoint``, but ``Function``. This is supposed
to work with total functions that have a decreasing argument, and I
should be able to do so using either a measure or a comparison,
followed by a theorem that arguments in recursive calls either have a
smaller measure or are less than the original arguments, as per the
comparator. I know Ackermann is 2nd-order PR, but obviously the PR
status of the function didn't prevent you from encoding it in some
way. What I'm wondering about is what is wrong with the encoding I
gave, which seems to follow the description in the manual.
|*)
