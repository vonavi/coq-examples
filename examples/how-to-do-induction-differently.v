(*|
################################
How to do induction differently?
################################

:Link: https://stackoverflow.com/q/43011411
|*)

(*|
Question
********

I am doing an exercise in Coq and trying to prove if a list equals to
its reverse, it's a palindrome. Here is how I define palindromes:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Inductive pal {X : Type} : list X -> Prop :=
| emptypal : pal []
| singlpal : forall x, pal [x]
| inducpal : forall x l, pal l -> pal (x :: l ++ [x]).

(*| Here is the theorem: |*)

Theorem palindrome3 : forall {X : Type} (l : list X),
    l = rev l -> pal l.

(*|
According to my definition, I will need to do the induction my
extracting the front and tail element but apparently coq won't let me
do it, and if I force it to do so, it gives an induction result that
definitely doesn't make any sense:
|*)

Proof.
  intros X l H. remember (rev l) as rl. induction l, rl.
  - apply emptypal.
  - inversion H.
  - inversion H.
  - (* stuck *)

(*| context: |*)

    Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
apparently the inductive context is terribly wrong. is there any way I
can fix the induction?
|*)

(*|
Answer
******

The solution I propose here is probably not the shortest one, but I
think it is rather natural.

My solution consists in defining an induction principle on ``list``
specialized to your problem.

Consider natural numbers. There is not only the standard induction
``nat_ind`` where you prove ``P 0`` and ``forall n, P n -> P (S n)``.
But there are other induction schemes, e.g., the strong induction
`lt_wf_ind
<https://coq.inria.fr/library/Coq.Arith.Wf_nat.html#lt_wf_ind>`__, or
the two-step induction where you prove ``P 0``, ``P 1`` and ``forall
n, P n -> P (S (S n))``. If the standard induction scheme is not
strong enough to prove the property you want, you can try another one.

We can do the same for lists. If the standard induction scheme
``list_ind`` is not enough, we can write another one that works. In
this idea, we define for lists an induction principle similar to the
two-step induction on ``nat`` (and we will prove the validity of this
induction scheme using the two-step induction on ``nat``), where we
need to prove three cases: ``P []``, ``forall x, P [x]`` and ``forall
x l x', P l -> P (x :: l ++ [x'])``. The proof of this scheme is the
difficult part. Applying it to deduce your theorem is quite
straightforward.

I don't know if the two-step induction scheme is part of the standard
library, so I introduce it as an axiom.
|*)

Axiom nat_ind2 : forall P : nat -> Prop,
    P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) -> forall n : nat, P n.

(*| Then we prove the induction scheme we want. |*)

Lemma list_ind2 :
  forall {A} (P : list A -> Prop)
         (P_nil : P [])
         (P_single : forall x, P [x])
         (P_cons_snoc : forall x l x', P l -> P (x :: l ++ [x'])),
  forall l, P l.
Proof.
  intros. remember (length l) as n. symmetry in Heqn. revert dependent l.
  induction n using nat_ind2; intros.
  - apply length_zero_iff_nil in Heqn. subst l. apply P_nil.
  - destruct l; [discriminate|]. simpl in Heqn. inversion Heqn; subst.
    apply length_zero_iff_nil in H0. subst l. apply P_single.
  - destruct l; [discriminate|]. simpl in Heqn.
    inversion Heqn; subst. pose proof (rev_involutive l) as Hinv.
    destruct (rev l). destruct l; discriminate. simpl in Hinv. subst l.
    rewrite app_length in H0.
    rewrite PeanoNat.Nat.add_comm in H0. simpl in H0. inversion H0.
    apply P_cons_snoc. apply IHn. assumption.
Qed.

(*|
You should be able to conclude quite easily using this induction
principle.
|*)

Theorem palindrome3 : forall {X : Type} (l : list X),
    l = rev l -> pal l.
Admitted. (* .none *)

(*|
----

**A:** Yes, there is that induction principle in the standard library,
see `pair_induction
<https://coq.inria.fr/library/Coq.Numbers.Natural.Abstract.NBase.html#NBaseProp.pair_induction>`__.
|*)
