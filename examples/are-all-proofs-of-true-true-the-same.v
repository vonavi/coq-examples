(*|
###########################################
Are all proofs of ``true = true`` the same?
###########################################

:Link: https://stackoverflow.com/questions/50847669/are-all-proofs-of-true-true-the-same
|*)

(*|
Question
********

Can I prove the following in ``Coq``?
|*)

Lemma bool_uip (H1 : true = true): H1 = eq_refl true.

(*|
i.e. that all proofs of ``true = true`` are the same?

From it follows for example ``forall c (H1 H2: c = true), H1 = H2``.

It would be nice to not have to add any axiom (like UIP). I found the
following thread that suggests that it might be the case:

`Proof in COQ that equality is reflexivity
<https://stackoverflow.com/questions/39464476/proof-in-coq-that-equality-is-reflexivity/39474531#39474531>`__
|*)

(*|
Answer
******

Here's a proof written as an explicit term.
|*)

Definition bool_uip (H1 : true = true) : H1 = eq_refl true :=
  match H1 as H in _ = b
        return match b return (_ = b) -> Prop with
               | true => fun H => H = eq_refl true
               | false => fun _ => False
               end H with
  | eq_refl => eq_refl
  end.

(*|
The type of ``H1 : true = _`` is inductive with one index (``_``).
Pattern-matching proceeds by first generalizing that type to ``true =
b`` (``in`` clause), and instantiating the index ``b`` in every
branch.

The main obstacle to overcome is that this generalization ``H1 : true
= b`` makes the result type ``H1 = eq_refl true`` no longer well-typed
(the two sides have different types). The solution is to pattern-match
on ``b`` to realign the types (in one branch; the other branch is
unused and we can in fact put anything instead of ``False``).

We can use the same technique to prove uniqueness of identity proofs
whenever the type of the "equalees" (here ``true`` of type ``bool``)
is decidable.

----

**A:** This proof is a central pillar in the `Mathematical Components
<https://math-comp.github.io/math-comp/>`__ library, for instance.

**A:** In Coq, for any type ``A`` with decidable equality UIP holds;
there proofs in both the standard library and in Mathcomp
``eq_axiomK``.
|*)
