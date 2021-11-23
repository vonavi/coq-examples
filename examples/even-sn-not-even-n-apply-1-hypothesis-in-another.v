(*|
``even_Sn_not_even_n`` - apply 1 hypothesis in another
======================================================

:Link: https://stackoverflow.com/questions/56354064/even-sn-not-even-n-apply-1-hypothesis-in-another
|*)

(*|
Question
--------

Unfortunately I got stuck again:
|*)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

Lemma even_Sn_not_even_n : forall n,
    even (S n) <-> not (even n).
Proof.
  intros n. split.
  - intros H. unfold not. intros H1. induction H1 as [|n' E' IHn].
    + inversion H.
    + inversion_clear H. apply IHn in H0. apply H0.
  - intros H. induction n as [|n' IHn].
    + exfalso. apply H. apply ev_0.
    + apply ev_SS. (* .unfold *)
Abort. (* .none *)

(*|
As far I could prove it in words:

``(n' + 1)`` is not even according to ``H``. Therefore according to
``IHn``, it is not true that ``n'`` is not even (double negation):

.. code-block:: coq

    IHn : ~ ~ even n'

Unfolding double negation, we conclude that ``n'`` is even.

But how to write it in coq?
|*)

(*|
Answer
------

The usual way to strip double negation is to introduce the "excluded
middle" axiom, which is defined under the name ``classic`` in
`Coq.Logic.Classical_Prop
<https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Classical_Prop.html>`_,
and apply the lemma ``NNPP``.

However, in this particular case, you can use the technique called
**reflection** by showing that the Prop is consistent with a boolean
function (you might remember the ``evenb`` function introduced earlier
in the book).

.. coq:: none
|*)

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(*|
(Assuming you're at the beginning of IndProp) You'll soon see the
following definition later in that chapter:
|*)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(*| You can prove the statement |*)

Lemma even_reflect : forall n : nat, reflect (even n) (evenb n).
Abort. (* .none *)

(*|
and then use it to move between a Prop and a boolean (which contain
the same information i.e. the (non-)evenness of ``n``) at the same
time. This also means that you can do classical reasoning on that
particular property without using the ``classic`` axiom.

I suggest to complete the exercises under Reflection section in
IndProp, and then try the following exercises. (\ **Edit:** I uploaded
the full answer `here
<https://github.com/Bubbler-4/coq-misc-works/blob/gitpod-vnc/StackOverflow/even_reflect.v>`_.)
|*)

(* Since ``evenb`` has a nontrivial recursion structure, you need the
   following lemma: *)
Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) -> forall n : nat, P n.
Proof.
  fix IH 5. intros. destruct n as [| [| ]]; auto.
  apply H1. apply IH; auto.
Qed.

(* This is covered in an earlier chapter *)
Lemma negb_involutive : forall x : bool, negb (negb x) = x.
Proof. intros []; auto. Qed.

(* This one too. *)
Lemma evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  induction n.
  - auto.
  - rewrite IHn. simpl. destruct (evenb n); auto.
Qed.

(* Exercises. *)
Lemma evenb_even : forall n : nat, evenb n = true -> even n.
Proof. induction n using nat_ind2.
(* Fill in here *) Admitted.

Lemma evenb_odd : forall n : nat, evenb n = false -> ~ (even n).
Proof. induction n using nat_ind2.
(* Fill in here *) Admitted.

Lemma even_reflect : forall n : nat, reflect (even n) (evenb n).
Proof. (* Fill in here. Hint: You don't need induction. *) Admitted.

Lemma even_iff_evenb : forall n, even n <-> evenb n = true.
Proof. (* Fill in here. Hint: use ``reflect_iff`` from IndProp. *) Admitted.

Theorem reflect_iff_false : forall P b, reflect P b -> (~ P <-> b = false).
Proof. (* Fill in here. *) Admitted.

Lemma n_even_iff_evenb : forall n, ~ (even n) <-> evenb n = false.
Proof. (* Fill in here. *) Admitted.

Lemma even_Sn_not_even_n : forall n,
    even (S n) <-> not (even n).
Proof. (* Fill in here.
          Hint: Now you can convert all the (non-)evenness properties
          to booleans, and then work with boolean logic! *) Admitted.
