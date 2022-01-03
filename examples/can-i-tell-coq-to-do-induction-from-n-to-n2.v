(*|
#######################################################
Can I tell Coq to do induction from ``n`` to ``n + 2``?
#######################################################

:Link: https://stackoverflow.com/q/53998991
|*)

(*|
Question
********

I'm trying to see if it's possible to prove ``evenb n = true <->
exists k, n = double k`` from
https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html
without involving odd numbers at all. I tried something like the
following:

.. coq:: none
|*)

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(*||*)

Theorem evenb_double_k : forall n,
    evenb n = true -> exists k, n = double k.
Proof.
  intros n H. induction n as [|n' IHn'].
  - exists 0. reflexivity.
  - (* stuck *)
(*|
But apparently induction works one natural number at a time, and
``exists k : nat, S n' = double k`` is clearly not provable.
|*)

    Show 1. (* .unfold .messages *)
Abort. (* .none *)

(*| Is there a way to have induction go from ``n`` to ``n + 2``? |*)

(*|
Answer (Li-yao Xia)
*******************

There is a tactic called ``fix``. I will try to explain what is
happening at a high level, because I think it is a cool hack, but be
warned that ``fix`` is a double-edged sword, generally ill advised to
use: it depends on really low-level details of Coq, that make proofs
quite fragile, and when they break, the error messages are difficult
to understand.

``fix foo i``, where ``foo`` is a fresh variable, and ``i`` is an
integer, is a tactic which applies to a goal with at least ``i``
arguments (for example, ``forall n, evenb n = true -> ...`` has two:
``n`` and a proof of ``evenb n = true``), and **assumes the goal that
you are trying to prove**, naming that new hypothesis ``foo``. (Yes,
you read that right.)
|*)

Theorem evenb_double_k : forall n,
    evenb n = true -> exists k, n = double k.
Proof.
  fix self 1. (* .unfold *)

(*|
Of course, there is a catch: **that hypothesis must be applied to a
proper subterm of n** (which is the *first* argument of the goal,
that's what the number parameter of ``fix self 1`` means, we say that
the first argument is the *decreasing argument*\ ). What is a proper
subterm of ``n``? It is a value that you can get only by destructing
``n``, at least once.

Note that Coq won't immediately complain if you still decide to apply
the hypothesis ``self`` directly (``n`` is not a proper subterm of
itself). Coq only checks the "subterm" requirement on ``Qed``. *EDIT:*
You can also use the command ``Guarded`` at any time to check this.
|*)

  apply self. (* seems fine, all goals done. *)
Fail Qed. (* .fails *) (* ERROR! *)
Abort. (* .none *)

(*|
You can approximatively imagine ``fix`` as a form of strong induction,
where the induction hypothesis (``self``) is given for all terms
smaller than the current one, not only immediate predecessors. However
this "subterm" relation does not actually appear in the statement of
``self``. (This peculiarity is what makes ``fix`` a low-level,
dangerous tactic.)

After a ``fix`` you generally want to ``destruct`` the decreasing
argument. This is where ``fix`` allows your proof to follow the
structure of ``evenb``. Below, we destruct again immediately in the
``S`` case. So we get three cases: ``n = O``, ``n = S O``, ``n = S (S
n')`` for some ``n' : nat``.

The first case is easy, the second one is vacuous, and the third one
is where you need the "induction hypothesis" ``self`` at ``n'``.
|*)

Theorem evenb_double_k : forall n,
    evenb n = true -> exists k, n = double k. (* .none *)
Proof.
  fix self 1. intros n. destruct n as [| [| n']].
  - exists 0. reflexivity.
  - discriminate.
  - simpl. intro H. apply self in H.
    destruct H as [k Hk]. exists (S k).
    rewrite Hk. reflexivity.
Qed.

(*|
Some of the reasoning there is fairly generic, and it can be pulled
out into a custom *induction principle for even nats*, which is
concretely another ``Theorem``.
|*)

Theorem even_ind :
  forall (P : nat -> Prop),
    P O ->
    (forall n, evenb n = true -> P n -> P (S (S n))) ->
    forall n, evenb n = true -> P n.

(*|
Compare it to the standard induction principle for ``nat``, which is
in fact also a theorem, named ``nat_ind``. This is what the
``induction`` tactic uses under the hood.
|*)

  About nat_ind. (* .unfold .no-messages *)

(*|
The induction step in ``nat_ind`` goes from ``n`` to ``S n``, whereas
the induction step for ``even_ind`` goes from ``n`` to ``S (S n)``,
and has an extra hypothesis saying that our numbers are even.

The proof of ``even_ind`` follows a similar structure to
``evenb_double_k``, although it is more abstract because it
generalizes over all predicates ``P`` on ``nat``.
|*)

Proof.
  intros P HO HSS. fix self 1.
  intros n. destruct n as [| [| n']].
  - intro. apply HO.
  - discriminate.
  - intros H. apply HSS.
    + apply H.
    + apply self. apply H.
Qed.

(*|
Another approach here is to not use ``fix`` at all (since it should be
avoided), but keep ``induction`` as a primitive to prove the
alternative ``even_ind`` principle. That is fine for ``nat``, but for
some complex inductive types, the default induction principle is too
weak and a handwritten ``fix`` is the only way.

Finally, going back to ``evenb_double_k``, we can use the new
induction principle with ``apply even_ind``, as opposed to ``fix`` or
``induction``. We now get only the two meaningful cases, ``O`` and ``S
(S n')`` where ``n'`` is even.
|*)

Theorem evenb_double_k' : forall n,
    evenb n = true -> exists k, n = double k.
Proof.
  apply even_ind.
  - exists 0. reflexivity.
  - intros n H [k Hk]. exists (S k).
    rewrite Hk. reflexivity.
Qed.

(*|
----

Definitions used in this answer:
|*)

Reset Initial.  (* .none *)
Fixpoint evenb n :=
  match n with
  | S (S n') => evenb n'
  | S O => false
  | O => true
  end.

Fixpoint double k :=
  match k with
  | O => O
  | S k' => S (S (double k'))
  end.

(*|
Answer (Anton Trunov)
*********************

Yes, absolutely! Let's use the induction principle from `this answer
<https://stackoverflow.com/a/40595110/2747511>`__.
|*)

From Coq Require Import Arith.

Lemma pair_induction (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 Hstep n.
  enough (P n /\ P (S n)) by easy.
  induction n; intuition.
Qed.

(*|
Now we can use the new principle like so (I switched the non-standard
functions with their stdlib counterparts so that everything compiles):
|*)

Theorem evenb_double_k : forall n,
    Nat.even n = true -> exists k, n = Nat.double k.
Proof.
  intros n Ev.
  induction n as [| |n IHn _] using pair_induction.
  (* the rest of the proof has been removed to not spoil the fun *)
Abort. (* .none *)
