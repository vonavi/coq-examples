(*|
#################################################
How can I automate counting within proofs in Coq?
#################################################

:Link: https://stackoverflow.com/q/42662141
|*)

(*|
Question
********

I have a function ``count`` that counts how many times a given
predicate is provable when applied to elements of a list. It is
defined as follows:
|*)

Parameter T : Type.

Parameter dec : forall (p : T -> Prop) (w : T), {p w} + {~ p w}.

Fixpoint count (p : T -> Prop) (l : list T) := match l with
  | nil => 0
  | cons head tail => if dec p head then 1 + count p tail else count p tail
end.

(*| I then use this function to state lemmas like the following: |*)

Parameter a b c : T.
Parameter q : T -> Prop.

Axiom Aa : q a.
Axiom Ab : q b.
Axiom Ac : ~ q c.

Lemma example : count q (cons a (cons b (cons c nil))) = 2.

(*| My proofs of such lemmas tend to be quite tedious: |*)

Proof.
  unfold count.
  assert (q a); [apply Aa | auto].
  assert (q b); [apply Ab | auto].
  assert (~ q c); [apply Ac | auto].
  destruct (dec q a); [auto | contradiction].
  destruct (dec q b); [auto | contradiction].
  destruct (dec q c); [contradiction | auto].
Qed.

(*|
What can I do to automate such tedious proofs that involve computation
with my ``count`` function?
|*)

(*|
Answer (Zimm i48)
*****************

This is typically the kind of cases where you are better off proving
things by reflection. See how things go smoothly (of course I modified
a bit your example to avoid all these axioms):
|*)

Reset Initial. (* .none *)
Require Import List.
Import ListNotations.

Fixpoint count {T : Type} (p : T -> bool) (l : list T) :=
  match l with
  | [] => 0
  | h :: t => if p h then S (count p t) else (count p t)
  end.

Inductive T := a | b | c.

Definition q x :=
  match x with
  | a => true
  | b => true
  | c => false
  end.

Lemma example : count q [a; b; c] = 2.
Proof.
  reflexivity.
Qed.

(*|
I realize that your definition of ``count`` was taking a propositional
predicate on type ``T`` (but with the assumption that all predicates
on type ``T`` are decidable) and instead I propose to define ``count``
to take a boolean predicate. But you may realize that having a
decidable propositional predicate or having a boolean predicate is
actually equivalent.

E.g. from your axioms, I can define a function which transform any
propositional predicate into a boolean one:
|*)

Reset Initial. (* .none *)
Parameter T : Type.

Parameter dec : forall (p : T -> Prop) (w : T), {p w} + {~ p w}.

Definition prop_to_bool_predicate (p : T -> Prop) (x : T) : bool :=
  if dec p x then true else false.

(*|
Of course, because there are axioms involved in your example, it won't
actually be possible to compute with the boolean predicate. But I'm
assuming that you put all these axioms for the purpose of the example
and that your actual application doesn't have them.

Answer to your comment
======================

As I told you, as soon as you have defined some function in terms of
an axiom (or of a `Parameter
<https://coq.inria.fr/refman/language/gallina-specification-language.html#coq:cmdv.parameter>`__
since this is the same thing), there is no way you can compute with it
anymore.

However, here is a solution where the decidability of propositional
predicate ``p`` is a lemma instead. I ended the proof of the lemma
with `Defined
<https://coq.inria.fr/refman/language/gallina-specification-language.html#coq:cmdv.defined>`__
instead of `Qed
<https://coq.inria.fr/refman/language/gallina-specification-language.html#coq:cmd.qed>`__
to allow computing with it (otherwise, it wouldn't be any better than
an axiom). As you can see I also redefined the ``count`` function to
take a predicate and a proof of its decidability. The proof by
reflection still works in that case. There is no ``bool`` but it is
strictly equivalent.
|*)

Reset Initial. (* .none *)
Require Import List.
Import ListNotations.

Fixpoint count {T : Type} (p : T -> Prop)
         (dec : forall (w: T), {p w} + {~ p w}) (l : list T) :=
  match l with
  | [] => 0
  | h :: t => if dec h then S (count p dec t) else count p dec t
  end.

Inductive T := a | b | c.

Definition p x := match x with | a => True | b => True | c => False end.

Lemma dec_p : forall (w : T), {p w} + {~ p w}.
Proof.
  intros []; simpl; auto.
Defined.

Lemma example2: count p dec_p [a; b; c] = 2.
Proof. reflexivity. Qed.

(*|
Answer (Anton Trunov)
*********************

Let's create our custom hint database and add your axioms there:

.. coq:: none
|*)

Reset Initial.

Parameter T : Type.

Parameter dec : forall (p : T -> Prop) (w : T), {p w} + {~ p w}.

Fixpoint count (p : T -> Prop) (l : list T) := match l with
  | nil => 0
  | cons head tail => if dec p head then 1 + count p tail else count p tail
end.

Parameter a b c : T.
Parameter q : T -> Prop.

Axiom Aa : q a.
Axiom Ab : q b.
Axiom Ac : ~ q c.

(*||*)

Hint Resolve Aa : axiom_db.
Hint Resolve Ab : axiom_db.
Hint Resolve Ac : axiom_db.

(*|
Now, the ``firstorder`` tactic can make use of the hint database:
|*)

Lemma example : count q (cons a (cons b (cons c nil))) = 2.
Proof.
  unfold count.
  destruct (dec q a), (dec q b), (dec q c); firstorder with axiom_db.
Qed.

(*|
----

We can automate our solution using the following piece of Ltac:
|*)

Ltac solve_the_probem :=
  match goal with
    |- context [if dec ?q ?x then _ else _] =>
      destruct (dec q x);
      firstorder with axioms_db;
      solve_the_probem
  end.

(*|
Then, ``unfold count; solve_the_probem.`` will be able to prove the
lemma.
|*)
