(*|
######################
Coq inference behavior
######################

:Link: https://stackoverflow.com/q/36996020
|*)

(*|
Question
********

I'm trying to write the following Agda snippet in Coq.

.. code-block:: agda

    open import Data.Fin using (Fin; suc; zero)
    open import Data.Nat using (ℕ; suc; zero)

    thin : {n : ℕ} -> Fin (suc n) -> Fin n -> Fin (suc n)
    thin zero    y       = suc y
    thin (suc x) zero    = zero
    thin (suc x) (suc y) = suc (thin x y)

I thought this could be straightforwardly translated to Coq as:
|*)

Inductive Fin : nat -> Type :=
| fz {n : nat} : Fin (S n)
| fs {n : nat} : Fin n -> Fin (S n).

Fail Fixpoint thin {n : nat} (x : Fin (S n)) (y : Fin n) : Fin (S n) :=
  match x, y with
  | fz,    y' => fs y'
  | fs x', fz => fz
  | fs x', fs y' => fs (thin x' y')
  end. (* .fails *)

(*|
I believe Coq should be able to figure out the implicit parameter
``n`` so I have no idea what is going on. I think I am unaware of a
difference between the type systems of Agda and Coq since the former
typechecks fine.
|*)

(*|
Answer
******

When pattern matching with dependent types, Coq does not usually
consider some essential relations between the variables in the context
and the variables introduced in the branches.

The easiest solution is to define the function in proof mode, at least
to understand what is going on.

This gives:
|*)

Fixpoint thin {n : nat} (x : Fin (S n)) (y : Fin n) : Fin (S n).
Proof.
  remember (S n) as n1. (* trick to keep the information when destructing *)
  destruct x; apply eq_add_S in Heqn1; subst n0.
  - apply fs. assumption.
  - destruct y.
    + apply fz.
    + apply fs. apply thin; assumption.
Defined. (* to create a transparent constant, as given by a classic Fixpoint *)

(*|
You can then print the value and read the lambda term to understand
how to define it directly. This could give:
|*)

Print thin. (* .unfold .messages *)

(*|
The ``return`` clauses of the pattern matchings is used to solve the
problem presented above: they connect the variables introduced in the
branches and the ones in the context. This is discussed more deeply
here: http://adam.chlipala.net/cpdt/html/MoreDep.html.

Also note that this particular inductive type was discussed a few
weeks ago on the coq-club mailing list. See
https://sympa.inria.fr/sympa/arc/coq-club/2016-03/msg00206.html.

----

**Q:** This helps a lot, thanks! I should have finished Chlipala's
book before actually trying to do stuff in Coq. One more question I
have: is it considered bad practice to define functions in proof mode?

**A:** I don't really know. Usually, I do that to check the lambda
term and write it myself. Anyway, I try to use mostly low-level
tactics to create a readable lambda term. Tactics like ``inversion``
create

**A:** Tactics like ``inversion`` create non-natural terms and should
be avoided. Maybe other users have stronger opinions on this
particular subject.
|*)
