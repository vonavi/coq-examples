(*|
#####################################################
How to replace a term with some property of the term?
#####################################################

:Link: https://stackoverflow.com/q/69949496
|*)

(*|
Question
********

I apologize if this example is contrived, I am attempting to prove a
similar Lemma with a more complex function than ``list_even``. I wish
to prove some property about a translation of a list.
|*)

Require Import Coq.Lists.List.
Import ListNotations.

Definition list_even (c : list nat) := map Nat.even c.

Lemma list_even_split : forall (c : list nat),
    c = nil \/
      exists c1 c2 b,
        c = c1 ++ c2
        /\ list_even c1 = b :: nil
        /\ list_even c = b :: list_even c2.

(*| The proof I came up with is as follows. |*)

Proof.
  induction c.
  - left. reflexivity.
  - right. exists [a], c.
    (* I am stuck here. *)
    assert (e := Nat.even a).

(*|
If I were to prove this by hand, my argument goes as follows.

Let ``c = [a] :: c2``, so ``c1 = [a]``. By ``Nat.Even_or_Odd``, ``a``
is even or it is odd. If ``a`` is even, then ``b = true`` and so

.. code-block:: coq

    c = [a] ++ c2 /\
        list_even [a] = [true] /\
        list_even c = true :: list_even c2

If ``a`` is odd, then ``b = false`` and so

.. code-block:: coq

    c = [a] ++ c2 /\
        list_even [a] = [false] /\
        list_even c = false :: list_even c2

which hold by simplification and reflexivity.

However, I do not know how to translate the proof state of
|*)

    Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
into one which proceeds with the evenness of ``a``.

I also do not believe I need induction for this.
|*)

(*|
Answer
******

Even-ness isn't actually important to this goal, as it is just a fact
about mapping. Either ``c`` is the empty list, or ``c`` is of the form
``c = x :: xs = [x] ++ xs`` so ``map Nat.even c = Nat.even x ++ map
Nat.even xs``. As such, you could have a proof like
|*)

Lemma list_even_split : forall (c : list nat),
    c = nil \/
      exists c1 c2 b,
        c = c1 ++ c2
        /\ list_even c1 = b :: nil
        /\ list_even c = b :: list_even c2.
Proof.
  intros c.
  destruct c as [|x xs];
    [ left; auto
    | right; exists (x :: nil); do 2 eexists; repeat split; eauto ].
Qed.

(*|
However, in other cases where one needs evenness of a variable you can
record it via

.. code-block:: coq

    destruct (Nat.even x) eqn : NAT_IS_EVEN
|*)
