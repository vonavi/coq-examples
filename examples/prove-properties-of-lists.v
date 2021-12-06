(*|
#########################
Prove properties of lists
#########################

:Link: https://stackoverflow.com/questions/52410544/prove-properties-of-lists
|*)

(*|
Question
********

My aim is to prove that certain properties of generated lists hold.
For instance, a generator function produces a list of ``1``'s, the
length of the list is given as an argument; I'd like to prove that the
length of the list is what the argument specifies. This is what I have
so far:
|*)

Require Import List.

Fixpoint list_gen lng acc :=
  match lng with
  | 0 => acc
  | S lng_1 => list_gen lng_1 (1 :: acc)
  end.

Lemma lm0 : length (list_gen 0 nil) = 0.
  intuition.
Qed.

Lemma lm1 : forall lng : nat, length (list_gen lng nil) = lng.
  induction lng.
  - apply lm0.
  - (* .unfold *)
Abort. (* .none *)

(*|
Now after applying ``lm0`` the induction step is left. I was hoping
that the proof of this step would be deduced from the code of
``list_gen`` but it's most likely a mistaken concept. How can this
subgoal be proved?

----

**A (Daniel Schepler):** I would guess probably you need to generalize
what you're proving to handle cases where the ``acc`` argument is not
``nil``:

.. code-block:: coq

    forall (lng : nat) (acc : list nat),
      length (list_gen lng acc) = lng + length acc.

(And then simpl should be very helpful in proving the inductive
step...)
|*)

(*|
Answer
******

I would go with Daniel's approach, however a bit more general one is
to write out a spec of ``list_gen``, e.g. using *non-tail-recursive*
``repeat`` function:
|*)

Require Import List Arith.
Import ListNotations.

Lemma list_gen_spec : forall lng acc,
    list_gen lng acc = repeat 1 lng ++ acc.
Abort. (* .none *)

(*|
where I had to add a bunch of lemmas about ``repeat``'s interaction
with some standard list functions.
|*)

Lemma repeat_singleton {A} (x : A) :
  [x] = repeat x 1.
Admitted.

Lemma repeat_app {A} (x : A) n m :
  repeat x n ++ repeat x m = repeat x (n + m).
Admitted.

Lemma app_cons {A} (x : A) xs :
  x :: xs = [x] ++ xs.
Admitted.           (* this is a convenience lemma for the next one *)

Lemma app_cons_middle {A} (y : A) xs ys :
  xs ++ y :: ys = (xs ++ [y]) ++ ys.
Admitted.

(*|
I'll leave the proofs of these lemmas as an exercise.

After proving the spec, your lemma could be proved with a few
rewrites.
|*)

Lemma list_gen_spec : forall lng acc,
    list_gen lng acc = repeat 1 lng ++ acc.
Proof.
  induction lng as [| lng IH]; intros xs; simpl; trivial.
  rewrite IH.
  now rewrite app_cons_middle, repeat_singleton, repeat_app, Nat.add_comm.
Qed.

Lemma lm1 lng : length (list_gen lng nil) = lng.
Proof.
  now rewrite list_gen_spec, app_nil_r, repeat_length.
Qed.
