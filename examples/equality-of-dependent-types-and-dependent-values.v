(*|
################################################
Equality of dependent types and dependent values
################################################

:Link: https://stackoverflow.com/q/48227116
|*)

(*|
Question
********

Consider a dependent type
|*)

Inductive dep (n : nat) := mkDep : dep n.

(*| Now, consider a simple theorem I wish to prove: |*)

Theorem equalTypes (n n' : nat) : n = n' -> dep n = dep n'.
Proof.
  intros.
Abort.

(*|
How do I show that two dependent types are equal? What is a notion of
type equality?

Worse, consider this "theorem" (which does not compile)
|*)

Fail Theorem equalInhabitants (n n' : nat) : n = n' -> mkDep n = mkDep n'.
(* .fails *)

(*|
This very **statement** is wrong, because the types ``mkDep n`` and
``mkDep n'`` don't match. However, in some sense, this statement is
**true**, because they *are* the same value under the assumption ``n =
n'``.

I wish to understand how to formalize and prove statements about
dependent types (specifically, their equality and notions thereof)
|*)

(*|
Answer
******

    How do I show that two dependent types are equal?

In this case, you can prove it with ``apply f_equal; assumption`` or
``subst; reflexivity`` (or ``destruct H; reflexivity`` or ``case H;
reflexivity`` or ``induction H; reflexivity`` or ``exact (eq_rect n
(fun n' => dep n = dep n') eq_refl n' H)``).

    What is a notion of type equality?

The same as any other equality; ``Print eq.`` gives:
|*)

Print eq. (* .unfold .messages *)

(*|
which says that the only special fact you have to construct a proof of
equality is that ``x = x`` for any ``x``. The way to use a proof of
equality, ``eq_rect``, is that, if you have ``x = y``, to prove a
property ``P`` of ``y``, it suffices to prove ``P`` of ``x``. In this
case, since we have ``n = n'``, to prove ``dep n = dep n'``, it
suffices to prove ``dep n = dep n`` (where ``P := fun n' => dep n =
dep n'``).

There is a deeper sense in which this question can be asked, because
it turns out that equality of types in Coq is under-constrained. Given
|*)

Inductive unit1 := tt1.
Inductive unit2 := tt2.

(*|
you can not prove ``unit1 = unit2``, nor can you prove ``unit1 <>
unit2``. In fact, it turns out that the only type inequalities ``T1 <>
T2`` that you can prove are cases where you can prove that ``T1`` and
``T2`` are not isomorphic. The Univalence axiom is a way of "filling
in the details" of type equality to say that any isomorphic types are
equal. There are other consistent interpretations, though (for
example, I believe that it's consistent to assume ``A * B = C * D -> A
= C /\ B = D``, though this contradicts univalence).

    Worse, consider this "theorem" (which does not compile)
|*)

Fail Theorem equalInhabitants (n n' : nat): n = n' -> mkDep n = mkDep n'.
(* .fails *)

(*|
Right. This is because we do not have an equality reflection rule in
Coq, and judgmental/definitional equality is not the same as
propositional equality. The way to state this is to "cast" the term
``mkDep n`` across the proof of equality.
|*)

Import EqNotations.
Theorem equalInhabitants (n n' : nat) : forall H : n = n',
    rew H in mkDep n = mkDep n'.
Proof.
  intros. subst. reflexivity.
Qed.

(*|
Note that ``rew`` binds more tightly than ``=``, and is a notation for
``eq_rect``. This says that for any proof ``H`` of ``n = n'``, the
term ``mkDep n``, when transported across ``H`` to become a term of
type ``dep n'``, is equal to ``mkDep n'``. (Note also that we could
just as well have used ``destruct H`` or ``induction H`` or ``case H``
(but not ``apply f_equal``) instead of ``subst``.)
|*)
