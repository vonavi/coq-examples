(*|
#############################################
Prove that the only zero-length vector is nil
#############################################

:Link: https://stackoverflow.com/q/47945424
|*)

(*|
Question
********

I have a type defined as
|*)

Inductive bits : nat -> Set :=
| bitsNil : bits 0
| bitsCons : forall {l}, bool -> bits l -> bits (S l).

(*| and I'm trying to prove: |*)

Lemma emptyIsAlwaysNil : forall {a: bits 0}, a = bitsNil.

(*|
After ``intros``, I've tried ``constructor 1``, ``case a``,
``intuition``, to no avail. ``case a`` seems like the closest, but it
gets an error:
|*)
  intros. (* .none *) Fail case a. (* .unfold .messages *)
Abort. (* .none *)

(*|
It sounds like it can't determine whether a bit-vector of an arbitrary
length is equal to one of zero-length, because they're different at
the type level. Is that correct?
|*)

(*|
Answer (Tej Chajed)
*******************

Yes, you're basically correct: specifically, what isn't type checking
is Coq's attempt to construct a ``match`` on ``a:bits 0`` (which is
what ``case`` does): the ``bitsCons`` case has an ill-typed
conclusion.

Here's an axiom-free proof. The key idea is to manually generalize the
statement to any ``n = 0`` (I couldn't figure out how to do this with
tactics; they all trip up on the dependency). The equality proof then
makes the conclusion type check regardless of what ``n`` is, and we
can dismiss the ``bitsCons`` case because we'll have ``n = S n'``. In
the more difficult ``bitsNil`` case, we make use of
``eq_rect_eq_dec``, which is a consequence of Axiom K but is provable
when the type index (``nat``, in this case) has decidable equality.
See the `Coq standard library documentation
<https://coq.inria.fr/library/Coq.Logic.Eqdep_dec.html>`__ for some
other things you can do without axioms with decidable equality.
|*)

Reset Initial. (* .none *)
Require PeanoNat.
Require Import Eqdep_dec.
Import EqNotations.

Inductive bits : nat -> Set :=
| bitsNil : bits 0
| bitsCons : forall {l}, bool -> bits l -> bits (S l).

Lemma emptyIsAlwaysNil_general :
  forall n (H: n = 0) {a: bits n}, rew [bits] H in a = bitsNil.
Proof.
  intros. induction a; simpl.
  - (* bitsNil *)
    rewrite <- eq_rect_eq_dec. auto.
    apply PeanoNat.Nat.eq_dec.
  - (* bitsCons - derive a contradiction *)
    exfalso; discriminate H.
Qed.

Lemma emptyIsAlwaysNil : forall {a: bits 0}, a = bitsNil.
Proof.
  intros.
  change a with (rew [bits] eq_refl in a).
  apply emptyIsAlwaysNil_general.
Qed.

(*|
You don't need the ``rew H in x`` notation from ``EqNotations`` (it
just wraps ``eq_rect``, the equality recursion principle), but I find
it makes things much more readable.

However, you can prove this theorem more simply if you're willing to
use an axiom, specifically ``JMeq_eq`` (see `CPDT's equality chapter
<http://adam.chlipala.net/cpdt/html/Equality.html>`__ for more
details), since then you can use ``dependent induction`` or
``dependent destruction``:
|*)

Reset Initial. (* .none *)
Require Import Program.Equality.

Inductive bits : nat -> Set :=
| bitsNil : bits 0
| bitsCons : forall {l}, bool -> bits l -> bits (S l).

Lemma emptyIsAlwaysNil : forall {a: bits 0}, a = bitsNil.
Proof.
  intros. dependent destruction a; reflexivity.
Qed.

Print Assumptions emptyIsAlwaysNil. (* .unfold *)

(*|
Answer (Anton Trunov)
*********************

Here is a simple proof (borrowed from `this Coq Club thread
<http://coq-club.inria.narkive.com/wrDwvaNY/how-to-prove-that-all-vectors-of-0-length-are-equal-to-vector-nil>`__):
|*)

Reset emptyIsAlwaysNil. (* .none *)
Definition emptyIsAlwaysNil {a: bits 0} : a = bitsNil :=
  match a with bitsNil => eq_refl end.

Opaque emptyIsAlwaysNil.

(*| Here is what Coq builds under the hood: |*)

Print emptyIsAlwaysNil. (* .unfold *)

(*|
----

**A:** Reminds me of Monin's small inversions:
`hal.archives-ouvertes.fr/inria-00489412
<https://hal.archives-ouvertes.fr/inria-00489412/>`__
|*)
