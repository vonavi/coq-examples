(*|
############################################
Tactic automation: simple decision procedure
############################################

:Link: https://stackoverflow.com/q/47126795
|*)

(*|
Question
********

I'm trying to automate a decision procedure for whether an ASCII
character is whitespace or not. Here is what I currently have.
|*)

Require Import Ascii String.

Scheme Equality for ascii.

Definition IsWhitespace (c : ascii) := (c = "009"%char) \/ (c = "032"%char).

Definition isWhitespace (c : ascii) : {IsWhitespace c} + {not (IsWhitespace c)}.
Proof.
  unfold IsWhitespace.
  pose proof (ascii_eq_dec c "009"%char) as [H1 | H1];
    pose proof (ascii_eq_dec c "032"%char) as [H2 | H2]; auto.
  right. intros [H3 | H3]; auto.
Qed.

(*|
What would be a good approach for making the proof more concise?
|*)

(*|
Answer (ejgallego)
******************

The proof is almost the most concise it can be! At most what you can
do is to call a more powerful tactic such as ``intuition``:
|*)

Reset isWhitespace. (* .none *)
Definition isWhitespace (c : ascii) : {IsWhitespace c} + {not (IsWhitespace c)}.
Proof.
  now unfold IsWhitespace;
    case (ascii_eq_dec c "009"%char);
    case (ascii_eq_dec c " "%char); intuition.
Qed.

(*|
----

**A:** Just a bit more concise reformulation of the above:
|*)

Reset isWhitespace. (* .none *)
Definition isWhitespace (c : ascii) : {IsWhitespace c} + {not (IsWhitespace c)}.
Proof.
  compute; case (ascii_eq_dec c "009"%char), (ascii_eq_dec c " "%char); tauto.
Qed.

(*| We use ``compute`` to unfold everything here. |*)

(*|
Answer (Jason Gross)
********************

Frequently, making a proof more automated involves writing a bit more
code than you started with, so that you can handle more cases. Taking
this approach, I adapted some boilerplate from `fiat-crypto
<https://github.com/mit-plv/fiat-crypto/blob/5da42750e1349ce761107902ef3039195adac62c/src/Util/Decidable.v>`__:
|*)

Reset Initial. (* .none *)
Require Import Coq.Strings.Ascii Coq.Strings.String.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _ {_}.
Notation DecidableRel R := (forall x y, Decidable (R x y)).

Global Instance dec_or {A B} {HA : Decidable A} {HB : Decidable B} :
  Decidable (A \/ B).
Proof. hnf in *. tauto. Defined.
Global Instance dec_eq_ascii : DecidableRel (@eq ascii) := ascii_dec.

(*| With this boilerplate, your proof becomes |*)

Definition IsWhitespace (c : ascii) := (c = "009"%char) \/ (c = "032"%char).
Definition isWhitespace (c : ascii) : Decidable (IsWhitespace c) := _.

(*|
which is about as short as a proof can be. (Note that ``:= _`` is the
same as ``. Proof. exact _. Defined.``, which itself is the same as
``. Proof. typeclasses eauto. Defined.``.)

Note that this is fairly similar to ejgallego's proof, since ``tauto``
is the same as ``intuition fail``.

Note also that `the original boilerplate in fiat-crypto
<https://github.com/mit-plv/fiat-crypto/blob/5da42750e1349ce761107902ef3039195adac62c/src/Util/Decidable.v>`__
is much longer, but also more powerful than simply using ``hnf in *;
tauto``, and handles a few dozen different sorts of decidable
propositions.

----

**Q:** This is super interesting! Would you mind explaining the
``Arguments`` aspect? And why use ``Notation`` instead of
``Definition``?

**Q:** Also... This approach looks a lot like the
``Coq.Structures.Equalities`` part of the standard library, is there
any particular reason not to use it?

**A:** The ``Arguments`` bit lets you write ``dec (x = y)`` to mean
"find an instance of decidability of ``x = y`` by typeclass resolution
and use that here". Without it, ``dec (x = y)`` is a type error,
because ``dec`` means "find the first instance of decidability of any
proposition, by typeclass resolution, and use that here".
|*)

(*|
Answer (ejgallego)
******************

Following the spirit of Jason's answer, we can of course use some
libraries dealing with decidable equality to arrive at your result:

This will declare ``ascii`` as a type with decidable equality:
|*)

Reset Initial. (* .none *)
From Coq Require Import Ascii String ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat.

Lemma ascii_NK : cancel N_of_ascii ascii_of_N.
Proof. exact: ascii_N_embedding. Qed.

Definition ascii_eqMixin := CanEqMixin ascii_NK.
Canonical ascii_eqType := EqType _ ascii_eqMixin.

(*|
In this style, usually you state your properties are decidable
propositions so there is nothing to prove:
|*)

Definition IsWhitespaceb (c : ascii) := [|| c == "009"%char | c == " "%char].

(*|
However if you want, you can of course recover the non-computational one:
|*)

Definition IsWhitespace (c : ascii) := (c = "009"%char) \/ (c = "032"%char).

Lemma whitespaceP c : reflect (IsWhitespace c) (IsWhitespaceb c).
Proof. exact: pred2P. Qed.

(*| Some more automation can be used of course. |*)
