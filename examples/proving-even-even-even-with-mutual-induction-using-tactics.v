(*|
##################################################################
Proving ``even + even = even`` with mutual induction using tactics
##################################################################

:Link: https://stackoverflow.com/q/43560581
|*)

(*|
Question
********

I was trying out mutual induction in Coq, the first type I defined was
|*)

Inductive IsEven : nat -> Prop :=
| EvenO : IsEven O
| EvenS n : IsOdd n -> IsEven (S n)
with IsOdd : nat -> Prop :=
| OddS n : IsEven n -> IsOdd (S n).

(*|
I now wanted to prove that the sum of even numbers is even. I was able
to do this using a ``Fixpoint`` and pattern matching:
|*)

Fixpoint even_plus_even (n m : nat) (evenn : IsEven n) (evenm : IsEven m) :
  IsEven (n + m) :=
  match evenn with
  | EvenO => evenm
  | EvenS n' oddn' => EvenS (n' + m) (odd_plus_even n' m oddn' evenm)
  end
with odd_plus_even (n m : nat) (oddn : IsOdd n) (evenm : IsEven m) :
  IsOdd (n + m) :=
  match oddn with
  | OddS n' evenn' => OddS (n' + m) (even_plus_even n' m evenn' evenm)
  end.

(*|
This defines both ``even_plus_even`` and ``odd_plus_even``. I would
now like to prove this using tactics in a more terse way (preferably
without using many predefined lemmas to keep the code as
self-contained as possible) but I haven't gotten very far.

Specifically, is it possible to prove both ``even_plus_even`` and
``odd_plus_even`` using only one Lemma like we can with the
``Fixpoint``?

**Edit:** Thank you very much for your answers, the ``Lemma ... with
...`` syntax was exactly what I was looking for. In fact
|*)

Lemma even_plus_even2 (n m : nat) (evenn : IsEven n) (evenm : IsEven m) :
  IsEven (n + m)
with odd_plus_even2 (n m : nat) (oddn : IsOdd n) (evenm : IsEven m) :
  IsOdd  (n + m).
Proof.
  induction evenn; simpl.
  - assumption.
  - constructor. auto.
  - induction oddn; simpl. constructor. auto.
Defined.

(*|
generates exactly the same proof term as the ``Fixpoint`` in my
originial question.
|*)

(*|
Answer (Vinz)
*************

There is support for mutual induction in Coq. I know of two ways, but
I only recall how to use one:

1. Combined Schemes

   Here is how it works:
|*)

Scheme IsEven_ind2 := Induction for IsEven Sort Prop
    with IsOdd_ind2 := Induction for IsOdd Sort Prop.

Combined Scheme IsEvenOdd_ind from IsEven_ind2, IsOdd_ind2.

Lemma foo : (forall (n : nat) (evenn : IsEven n), forall m (evenm : IsEven m),
                IsEven (n + m)) /\
              (forall (n : nat) (oddn : IsOdd n), forall m (evenm : IsEven m),
                  IsOdd (n + m)).
Proof.
  apply IsEvenOdd_ind.
  - now intros m hm.
  - intros h hn hi m hm. rewrite plus_Sn_m. apply EvenS. now apply hi.
  - intros h hn hi m hm. rewrite plus_Sn_m. apply OddS. now apply hi.
Qed.

(*|
1. ``Lemma with``

   On this one I just don't know how to finish it but that's a syntax
   issue iirc:
|*)

Reset foo. (* .none *)
Lemma foo : forall (n m : nat) (evenn : IsEven n) (evenm : IsEven m),
    IsEven (n + m)
with bar : forall (n m : nat) (oddn : IsOdd n) (evenm : IsEven m),
    IsOdd (n + m).
Proof.
  - intros n m hn. revert m.
    induction hn as [| p hp]; intros m hm; simpl in *.
    + exact hm.
    + now apply EvenS; apply bar.
  - intros n m hn hm. revert n hn.
    induction hm as [| p hp]; intros n hn; simpl in *.
    + now apply bar; [exact hn | apply EvenO].
    + apply bar; [exact hn |]. now apply EvenS.
Fail Qed. (* .fails .unfold *)
Abort. (* .none *)

(*|
**Edit:** Here is a valid syntax for the ``Lemma with`` solution.
|*)

Lemma foo (n : nat) (evenn : IsEven n) :
  forall (m : nat) (evenm : IsEven m), IsEven (n + m)
with bar (n : nat) (oddn : IsOdd n) :
  forall (m : nat) (evenm : IsEven m), IsOdd (n + m).
Proof.
  - induction evenn as [| p hp]; intros m hm; simpl in *.
    + exact hm.
    + now apply EvenS; apply bar.
  - induction oddn as [p hp]. intros n hn. simpl in *.
    apply OddS. now apply foo.
Qed.

(*|
Answer (larsr)
**************

You can for instance prove both lemmas at the same time by "anding"
them together into one lemma, and then extract the left or right part
of the clause using ``proj1`` and ``proj2``.
|*)

Reset even_plus_even. (* .none *)
Lemma even_or_odd_plus_even: forall (n m : nat),
    (forall (evenn : IsEven n) (evenm : IsEven m), IsEven (n + m)) /\
      (forall (oddn : IsOdd n) (evenm : IsEven m), IsOdd (n + m)).
Proof.
  induction n; split; intros.
  - auto.
  - inversion oddn.
  - destruct (IHn m) as [He Ho]. inversion evenn.
    constructor. auto.
  - destruct (IHn m) as [He Ho]. inversion oddn.
    constructor. auto.
Qed.

Definition even_plus_even n m := proj1 (even_or_odd_plus_even n m).
Definition odd_plus_even n m := proj2 (even_or_odd_plus_even n m).

(*| gives you |*)

Check even_plus_even. (* .unfold .messages *)
Check odd_plus_even. (* .unfold .messages *)

(*|
Notice that the two clauses share share the ``n`` and ``m``, which you
need if the clauses can't be proved separately because they need to
depend on each other. (In this particular case they don't, though. You
*could* prove the statements separately, as Anton showed.)

EDIT: just saw Vinz solution. I didn't know Lemma had the ``with``
syntax (thanks for showing!), but that makes sense and is I think a
neater way to do this mutually dependent definition.
|*)

Reset even_plus_even. (* .none *)
Lemma even_plus_even : forall n m, IsEven n -> IsEven m -> IsEven (n + m)
with odd_plus_even: forall n m, IsOdd n -> IsEven m -> IsOdd (n + m).
Proof.
  - induction 1; simpl; auto using EvenS.
  - induction 1; simpl; auto using OddS.
Qed.

(*|
----

**A:** Actually, both ``Lemma`` and ``Fixpoint`` are just aliases for
``Theorem``, see `here
<https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#hevea_command20>`__,
which means that you can also define ``Fixpoint`` definitions with
proof tactics, without giving the explicit proof term upfront. By the
way, the ``refine`` tactic is useful if you want to give parts of the
proof term explicitly, while leaving holes to fill in by tactics.
|*)
