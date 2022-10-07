(*|
###################################################
Induction on predicates with product type arguments
###################################################

:Link: https://stackoverflow.com/q/34877565
|*)

(*|
Question
********

If I have a predicate like this:
|*)

Inductive foo : nat -> nat -> Prop :=
| Foo : forall n, foo n n.

(*| then I can trivially use induction to prove some dummy lemmas: |*)

Lemma foo_refl : forall n n',
    foo n n' -> n = n'.
Proof.
  intros. induction H. reflexivity.
Qed.

(*| However, for a predicate with product type arguments: |*)

Inductive bar : (nat * nat) -> (nat * nat) -> Prop :=
| Bar : forall n m, bar (n, m) (n, m).

(*|
a similar proof for nearly identical lemma gets stuck because all
assumptions about variables disappear:
|*)

Lemma bar_refl : forall n n' m m',
    bar (n, m) (n', m') -> n = n'.
Proof.
  intros. induction H. (* :( *)
Abort. (* .none *)

(*|
Why is this happening? If I replace ``induction`` with ``inversion``,
then it behaves as expected.

The lemma is still provable with ``induction`` but requires some
workarounds:
|*)

Lemma bar_refl : forall n n' m m',
    bar (n, m) (n', m') -> n = n'.
Proof.
  intros.
  remember (n, m) as nm.
  remember (n', m') as n'm'.
  induction H.
  inversion Heqnm. inversion Heqn'm'. repeat subst.
  reflexivity.
Qed.

(*|
Unfortunately, this way proofs gets completely cluttered and are
impossible to follow for more complicated predicates.

One obvious solution would be to declare ``bar`` like this:
|*)

Inductive bar' : nat -> nat -> nat -> nat -> Prop :=
| Bar' : forall n m, bar' n m n m.

(*|
This solves all the problems. Yet, for my purposes, I find the
previous ("tupled") approach somewhat more elegant. Is there a way to
keep the predicate as it is and still be able to do manageable
inductive proofs? Where does the problem even come from?
|*)

(*|
Answer (Vinz)
*************

The issue is that induction can only works with variables, not
constructed terms. This is why you should first prove something like
|*)

Reset bar_refl. (* .none *)
Lemma bar_refl : forall p q, bar p q -> fst p = fst q.

(*| which is trivially proved by |*)
  now induction 1.
Qed.

(*|
to prove your lemma.

If you don't want the intermediate lemma to have a name, your solution
is the correct one: you need to help Coq with ``remember`` to
generalize your goal, and then you'll be able to prove it.

I don't remember exactly where this restriction comes from, but I
recall something about making some unification problem undecidable.
|*)

(*|
Answer (larsr)
**************

Often in these situation one can do induction on one of the sub-terms.

In your case your lemma can be proved by induction on ``n``, with
|*)

Reset bar_refl. (* .none *)
Lemma bar_refl : forall n n' m m', bar (n, m) (n', m') -> n = n'.
Proof. induction n; intros; inversion H; auto. Qed.

(*|
Answer (Anton Trunov)
*********************

    ... all assumptions about variables disappear... Why is this
    happening? If I replace ``induction`` with ``inversion``, then it
    behaves as expected.

The reason that happens is described perfectly in this blog post:
`Dependent Case Analysis in Coq without Axioms
<https://homes.cs.washington.edu/~jrw12/dep-destruct.html>`__ by James
Wilcox. Let me quote the most relevant part for this case:

    When Coq performs a case analysis, it first abstracts over all
    indices. You may have seen this manifest as a loss of information
    when using ``destruct`` on predicates (try destructing ``even 3``
    for example: it just deletes the hypothesis!), or when doing
    induction on a predicate with concrete indices (try proving
    ``forall n, even (2*n + 1) -> False`` by induction on the
    hypothesis (not the ``nat``) -- you'll be stuck!). Coq essentially
    forgets the concrete values of the indices. When trying to induct
    on such a hypothesis, one solution is to replace each concrete
    index with a new variable together with a constraint that forces
    the variable to be equal to the correct concrete value.
    ``destruct`` does something similar: when given a term of some
    inductive type with concrete index values, it first replaces the
    concrete values with new variables. It doesn't add the equality
    constraints (but ``inversion`` does). The error here is about
    abstracting out the indices. You can't just go replacing concrete
    values with arbitrary variables and hope that things still type
    check. It's just a heuristic.

To give a concrete example, when using ``destruct H.`` one basically
does pattern-matching like so:
|*)

Reset bar_refl. (* .none *)
Lemma bar_refl : forall n n' m m',
  bar (n, m) (n', m') -> n = n'.
Proof.
  intros n n' m m' H.
  refine (match H with
          | Bar a b => _
          end).

(*| with the following proof state: |*)

  Show. (* .unfold .messages *)

(*|
To get almost the exact proof state we should've erased ``H`` from the
context, using the ``clear H.`` command: ``refine (...); clear H.``.
This rather primitive pattern-matching doesn't allow us to prove our
goal. Coq abstracted away ``(n, m)`` and ``(n', m')`` replacing them
with some pairs ``p`` and ``p'``, such that ``p = (a, b)`` and ``p' =
(a, b)``. Unfortunately, our goal has the form ``n = n'`` and there is
neither ``(n, m)`` nor ``(n', m')`` in it -- that's why Coq didn't
change the goal with ``a = a``.

But there is a way to tell Coq to do that. I don't know how to do
*exactly* that using tactics, so I'll show a proof term. It's is going
to look somewhat similar to @Vinz's solution, but notice that I didn't
change the statement of the lemma:
|*)

  Undo. (* to undo the previous pattern-matching *)
  refine (match H in (bar p p') return fst p = fst p' with
          | Bar a b => _
          end).

(*|
This time we added more annotations for Coq to understand the
connections between the components of ``H``'s type and the goal -- we
explicitly named the ``p`` and ``p'`` pairs and because we told Coq to
treat our goal as ``fst p = fst p'`` it will replace ``p`` and ``p'``
in the goal with ``(a, b)``. Our proof state looks like this now:
|*)

  Show. (* .unfold .messages *)
  reflexivity. (* .none *)
Qed. (* .none *)

(*|
and simple ``reflexivity`` is able to finish the proof.

I think now it should be clear why ``destruct`` works fine in the
following lemma (don't look at the answer below, try to figure it out
first):
|*)

Lemma bar_refl_all : forall n n' m m',
    bar (n, m) (n', m') -> (n, m) = (n', m').
Proof.
  intros. destruct H. reflexivity.
Qed.

(*|
Answer: because the goal contains the same pairs that are present in
the hypothesis's type, so Coq replaces them all with appropriate
variables and that will prevent the information loss.
|*)

(*|
Answer (Dominique Larchey-Wendling)
***********************************

Another way...
|*)

Reset bar_refl. (* .none *)
Lemma bar_refl n n' m m' : bar (n, m) (n', m') -> n = n'.
Proof.
  change (n = n') with (fst (n, m) = fst (n', m')).
  generalize (n, m) (n', m').
  intros ? ? [ ]. reflexivity.
Qed.
