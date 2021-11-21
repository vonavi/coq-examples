(*|
Lemma about list and rev(list)
==============================

:Link: https://stackoverflow.com/questions/56860962/lemma-about-list-and-revlist
|*)

(*|
Question
--------

Trying to prove the following lemma I got stuck. Usully theorems about
lists are proven using induction, but I don't know where to move next.
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Lemma reverse_append : forall (T : Type) (h : T) (t : list T),
    h :: t = rev t ++ [h] -> t = rev t.
Proof.
  intros. induction t.
  - simpl. reflexivity.
  - simpl. simpl in H. (* .unfold *)
Admitted. (* .none *)

(*|
Answer
------

Main answer
~~~~~~~~~~~

Before you start proving your theorem, you should try to *thoroughly*
understand what your theorem says. Your theorem is simply wrong.

Counterexample: `2 :: [1;2] = rev [1;2] ++ [2]`, but `[1;2]` is not a
palindrome.

Full proof:
|*)

Require Import List.
Import ListNotations.

Lemma reverse_append_false :
  ~(forall (T : Type) (h : T) (t : list T),
       h :: t = rev t ++ [h] -> t = rev t).
Proof.
  intros H. specialize (H nat 2 [1;2] eq_refl). inversion H.
Qed.

(*|
Minor issues
~~~~~~~~~~~~

    Usually theorems about lists are proven using induction

This is a pretty naive statement, though technically correct. There
are so many ways to do induction on a value, and choosing the
induction that works best is a crucial skill. To name a few:

- Induction on the list
- Induction on the length of the list

  - arises quite frequently when dealing with `rev` and other
    functions that preserve length
  - `Example <https://stackoverflow.com/a/18760596/4595904>`_

- If simple induction doesn't work, consider a custom induction scheme

  - `nat_ind2 <https://stackoverflow.com/a/56356131/4595904>`_
|*)
