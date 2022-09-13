(*|
#######################
Coq induction on modulo
#######################

:Link: https://stackoverflow.com/q/29189073
|*)

(*|
Question
********

I'm new with Coq and I really have difficulty in applying the
induction. As long as I can use theorems from the library, or tactics
such as ``lia``, all this is "not a problem". But as soon as these do
not work, I'm always stuck.

To be precise, now I try to prove
|*)

Require Import ZArith. (* .none *)
Lemma mod_diff : forall n m : nat, n >= m /\ m <> 0 -> (n - m) mod m = n mod m.

(*| the case ``n = 0`` I already have. |*)

Proof.
  intros. destruct H as [H1 H2]. induction n.
  - now rewrite Nat.mod_0_l, Nat.mod_0_l.

(* | But how to make the induction step? |*)

  - Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Answer (Atsby)
**************

Induction is not necessary for the proof, there are sufficient lemmas
in the Coq library that can be used. To find these lemmas, I used
``SearchAbout modulo`` and ``SearchAbout plus``.

Then, I did:
|*)

Require Import Lia. (* .none *)
Lemma mod_add_back : forall n m : nat, m <> 0 -> (n + m) mod m = n mod m.
Proof.
  intros. rewrite Nat.add_mod, Nat.mod_same.
  - now rewrite plus_0_r, Nat.mod_mod.
  - assumption.
  - assumption.
Qed.

Lemma mod_diff : forall n m : nat, n >= m /\ m <> 0 -> (n - m) mod m = n mod m.
Proof.
  intros. intuition. rewrite <- mod_add_back.
  - assert (n - m + m = n) by lia.
    rewrite H. reflexivity.
  - intuition.
Qed.

(*|
Notice the use of ``assert ... by lia`` to prove an instance of a
rewriting that doesn't seem to be available as a built-in lemma. It's
a bit tricky because with nats it does not work in general, but only
if ``n >= m``. (\ **EDIT**: actually the built-in lemma
``Nat.sub_add`` would've worked).

So the idea in the proof is to first prove a lemma that allows you to
"add back" ``m``, as this seems like a good idea to have a separate
lemma. However, I suppose it could also have been done as a single
proof.

Indeed, induction on ``n`` does not advance the proof at all, because
there is no way to show the preconditions of the inductive hypothesis
(cannot derive ``n >= m`` from ``S n >= m``). While induction is an
important building block it is not always the right tool.
|*)

(*|
Answer (larsr)
**************

As @Atsby said, there is already useful lemmas in the library, so you
can for instance do
|*)

Reset Initial. (* .none *)
Require Import ZArith.
Require Import Lia.

Lemma mod_diff : forall n m : nat, n >= m /\ m <> 0 -> (n - m) mod m = n mod m.
Proof.
  intros n m [H1 H2].
  rewrite <- (Nat.mod_add _ 1); try rewrite mult_1_l, Nat.sub_add; auto.
Qed.

(*|
Regarding your question about how to do it with induction, my general
advice is to get an induction hypothesis that is as general as
possible, i.e. don't introduce the quantified variables before you do
``induction``. And also, try to get an induction hypothesis that is
also useful for "the next" value. I would therefore try to prove
another formula ``(n + k * m) mod m = n mod m`` and do induction on
``k``, because then only algebraic rewriting is necessary to prove the
``k + 1`` case from ``k``. However, in this case, that 'other formula'
was already in the library, called ``Nat.sub_add``.
|*)

(*|
Answer (Partial)
****************

You should use a different induction principle.

The ``mod`` function obeys the following relation.
|*)

Reset Initial. (* .none *)
Inductive mod_rel : nat -> nat -> nat -> Prop :=
| mod_rel_1 : forall n1 n2, n2 = 0 -> mod_rel n1 n2 0
| mod_rel_2 : forall n1 n2, n2 > 0 -> n1 < n2 -> mod_rel n1 n2 n1
| mod_rel_3 : forall n1 n2 n3,
    n2 > 0 -> n1 >= n2 -> mod_rel (n1 - n2) n2 n3 -> mod_rel n1 n2 n3.

(*|
In standard math it's usually assumed modulo by zero is undefined. The
truth is all theorems involving modulo have the precondition that the
second argument not be zero, so it doesn't really matter whether
modulo by zero is defined or not.

The following is the domain of the ``mod`` function.
|*)

Inductive mod_dom : nat -> nat -> Prop :=
| mod_dom_1 : forall n1 n2, n2 = 0 -> mod_dom n1 n2
| mod_dom_2 : forall n1 n2, n2 > 0 -> n1 < n2 -> mod_dom n1 n2
| mod_dom_3 : forall n1 n2,
    n2 > 0 -> n1 >= n2 -> mod_dom (n1 - n2) n2 -> mod_dom n1 n2.

(*|
In Coq there are only total functions, so any pair of natural numbers
is in the domain of ``mod``. This is provable by well-founded
induction and case analysis.
|*)

Conjecture wf_ind : forall P1,
    (forall n1, (forall n2, n2 < n1 -> P1 n2) -> P1 n1) -> forall n1, P1 n1.
Conjecture O_gt : forall n1, n1 = 0 \/ n1 > 0.
Conjecture lt_ge : forall n1 n2, n1 < n2 \/ n1 >= n2.

Conjecture mod_total : forall n1 n2, mod_dom n1 n2.

(*| The induction principle associated with ``mod``'s domain is |*)

Check mod_dom_ind : forall P1 : nat -> nat -> Prop,
    (forall n1 n2, n2 = 0 -> P1 n1 n2) ->
    (forall n1 n2, n2 > 0 -> n1 < n2 -> P1 n1 n2) ->
    (forall n1 n2, n2 > 0 -> n1 >= n2 ->
                   mod_dom (n1 - n2) n2 -> P1 (n1 - n2) n2 -> P1 n1 n2) ->
    forall n1 n2, mod_dom n1 n2 -> P1 n1 n2.

(*| But since ``mod`` is total, it's possible to simplify this to |*)

Conjecture mod_ind : forall P1 : nat -> nat -> Prop,
    (forall n1 n2, n2 = 0 -> P1 n1 n2) ->
    (forall n1 n2, n2 > 0 -> n1 < n2 -> P1 n1 n2) ->
    (forall n1 n2, n2 > 0 -> n1 >= n2 -> P1 (n1 - n2) n2 -> P1 n1 n2) ->
    forall n1 n2, P1 n1 n2.

(*|
This induction principle applies to any pair of natural numbers. It's
better suited to proving facts about ``mod`` because follows the
structure of the definition of ``mod``. ``mod`` can't be defined
directly using structural recursion, so structural induction will only
get you so far when proving things about ``mod``.

Not every proof should be tackled with induction though. You need to
ask yourself why you believe something to be true and translate that
to a rigorous proof. If you're not sure why it's true, you need to
learn or discover why it is or isn't.

But division and modulo can be defined indirectly by structural
recursion. In the following function, ``n3`` and ``n4`` serve as an
intermediate quotient and remainder. You define it by decrementing the
dividend and incrementing the remainder until the remainder reaches
the divisor, at which point you increment the quotient and reset the
remainder and continue. When the dividend reaches zero, you have the
true quotient and remainder (assuming you didn't divide by zero).
|*)

Conjecture ltb : nat -> nat -> bool.

Fixpoint div_mod (n1 n2 n3 n4 : nat) : nat * nat :=
  match n1 with
  | 0 => (n3, n4)
  | S n1 => if ltb (S n4) n2
            then div_mod n1 n2 n3 (S n4)
            else div_mod n1 n2 (S n3) 0
  end.

Definition div (n1 n2 : nat) : nat := fst (div_mod n1 n2 0 0).

Definition mod (n1 n2 : nat) : nat := snd (div_mod n1 n2 0 0).

(*|
You still don't use structural induction to prove things about ``div``
and ``mod``. You use it to prove things about ``div_mod``. These
functions correspond to the following (structurally inductive)
theorem.
|*)

Theorem augmented_division_algorithm : forall n1 n2 n3 n4,
    n4 < n2 -> exists n5 n6, n1 + n3 * n2 + n4 = n5 * n2 + n6 /\ n6 < n2.
Proof.
  induction n1.
  - firstorder. exists n3. exists n4. firstorder.
  - firstorder. destruct (lt_ge (S n4) n2).
    + specialize (IHn1 n2 n3 (S n4) H0). firstorder.
      exists x. exists x0. firstorder.
      admit. (* H1 implies the conclusion. *)
    + Conjecture C2 : forall n1 n2, n1 < n2 -> 0 < n2.
      pose proof (C2 _ _ H). specialize (IHn1 n2 (S n3) 0).
      firstorder. exists x. exists x0. firstorder.
      Conjecture C3 : forall n1 n2, n1 < n2 -> S n1 >= n2 -> S n1 = n2.
      pose proof (C3 _ _ H H0). subst. cbn in *.
      admit. (* H2 implies the conclusion. *)
Admitted.

(*|
The usual division algorithm can be derived by setting ``n3`` and
``n4`` to zero.
|*)

Conjecture division_algorithm : forall n1 n2, 0 < n2 -> exists n5 n6,
      n1 = n5 * n2 + n6 /\ n6 < n2.

(*| Disclaimer: conjectures and simply-typed functions. |*)
