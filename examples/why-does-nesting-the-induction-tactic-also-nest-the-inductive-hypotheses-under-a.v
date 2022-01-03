(*|
########################################################################################
Why does nesting the induction tactic also nest the inductive hypotheses under a lambda?
########################################################################################

:Link: https://stackoverflow.com/q/55596125
|*)

(*|
Question
********
|*)

Require Import Coq.Arith.PeanoNat. (* .none *)
Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof.
  intros. induction n.
  - simpl. rewrite (Nat.mul_0_r m). reflexivity.
  - simpl. rewrite <- IHn. induction m.
    + simpl. reflexivity.
    + simpl.

(*| The above is from the Software Foundation's second chapter. |*)

      Show 1. (* .unfold .messages *)

(*|
I am really confused as to what ``IHm`` is supposed to be here. The
way I understand it, Coq tactics get compiled under the hood to some
functional program, but I am really not sure what is going on here. I
am pretty sure that this is not I intended it to do.

What I wanted to do is something like the following Idris program.

.. code-block:: idris

    add_comm : {a,b : Nat} -> a + b = b + a
    add_assoc : {a,b,c : Nat} -> (a + b) + c = a + (b + c)

    total
    mult_comm : {m,n : Nat} -> (m * n) = n * m
    mult_comm {m = Z} {n = Z} = Refl
    mult_comm {m = Z} {n = (S k)} = mult_comm {m=Z} {n=k}
    mult_comm {m = (S k)} {n = Z} = mult_comm {m=k} {n=Z}
    mult_comm {m = (S k)} {n = (S j)} =
        let prf1 = mult_comm {m=k} {n=S j}
            prf2 = mult_comm {m=S k} {n=j}
            prf3 = mult_comm {m=k} {n=j}
            prf_add_comm = add_comm {a=k} {b=j}
            prf_add_assoc = add_assoc {a=k} {b=j} {c=j*k}
            prf_add_assoc' = add_assoc {a=j} {b=k} {c=j*k}
        in
            rewrite prf1 in
            rewrite sym prf2 in
            rewrite prf3 in
            rewrite sym prf_add_assoc in
            rewrite sym prf_add_assoc' in
            rewrite (add_comm {a=k} {b=j}) in
            Refl

More specifically, I need ``prf1``, ``prf2`` and ``prf3`` which I get
using recursive calls to ``mult_comm``. In Coq the two of the proofs
are stuck in a lambda and I am not sure how that happened. I see that
Coq's ``induction`` tactic is not doing what I think it should be
doing.

In addition to the explanation of the above, let me also ask is there
more introductory material to Coq than Software Foundations just in
case I get stuck like this again on some tactic? Note that I know how
to solve this in Coq as I've found the solution online.

I've tried tackling the SF book unsuccessfully back in 2016 as an
introduction to dependently typed programming and now with the benefit
of hindsight, I see that Little Typer and the Idris book are much
better in that regard.
|*)

(*|
Answer
******

When you call the ``induction`` tactic, Coq uses heuristics to
determine the predicate ``P : nat -> Prop`` that you want to prove by
induction. Before calling ``induction`` for the second time, the proof
state looks like this:
|*)
      Undo 6. (* .unfold .no-in *)
Abort. (* .none *)

(*|
What happened is that Coq decided to include the premise ``IHn`` in
the induction predicate, which was inferred to be

.. code-block:: coq

    P m := m * n = n * m -> m * S n = m + m * n

which is exactly what you had in your induction hypothesis. In this
case, you could argue that it was silly for Coq to use the premise,
but there are cases where dropping it would result in an unprovable
goal. For instance, consider the following proof attempt:
|*)

Lemma double_inj : forall n m, n + n = m + m -> n = m.
Proof.
  intros n m H.
  induction n as [|n IH].
  (* ... *)
Abort. (* .none *)

(*|
If ``H`` were dropped after calling ``induction``, you would have to
prove ``forall n m, n = m``, which clearly does not hold.

This example is one of the reasons why it is often a bad idea to call
``induction`` multiple times in a single Coq proof. As we suggest in
that exercise in Software Foundations, it is better to prove an
auxiliary lemma, since you can be explicit about the induction
predicate. For this example, there are other options as well. You
could, for instance, call ``clear IHn`` to drop the ``IHn`` premise,
which would lead Coq to the correct predicate. The ssreflect proof
language, which now ships with Coq, has a different tactic for
performing induction called ``elim``, which allows you to be more
explicit in the choice of the predicate.

I agree with your final comment, but I should add that it is not the
goal of Software Foundations to be an introduction to dependently
typed programming. Though Coq supports this paradigm, it is generally
cumbersome to write such programs directly, and much easier to use
tactics to prove lemmas about simply typed programs. For instance,
your proof of ``mult_comm`` is accepted by Idris because its
termination checker is smart enough to recognize all recursive calls
as decreasing, even though they are not decreasing with respect to a
fixed argument (in the second clause, ``n`` decreases, whereas in the
third ``m`` does). This is not possible in Coq, and you must split the
definition into multiple recursive functions, one for each argument,
or use well-founded induction on pairs of natural numbers, which would
be overkill for this example.

Adam Chlipala has another Coq textbook called `CPDT
<http://adam.chlipala.net/cpdt/>`__ that you might want to check out.
However, I don't think you will find a comprehensive description of
Coq's tactics there, either. Like ``induction``, many tactics rely on
heuristics and are hard to explain in detail.

On a final note, Matthieu Sozeau has developed a package called
`Equations <https://github.com/mattam82/Coq-Equations>`__ that makes
dependently typed programming in Coq much closer to Idris or Agda. If
you find this style of proving more intuitive, you could try to use
it.
|*)
