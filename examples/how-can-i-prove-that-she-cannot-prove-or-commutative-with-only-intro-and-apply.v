(*|
###################################################################################
How can I prove that she cannot prove ``Or_commutative`` with only intro and apply?
###################################################################################

:Link: https://stackoverflow.com/questions/51871265/how-can-i-prove-that-she-cannot-prove-or-commutative-with-only-intro-and-apply
|*)

(*|
Question
********

This question is related to a strategic game (bargaining, protocol,
crypto, ...) setting I investigate during holidays where players are
Coq users.

Some of them have limited reasoning capabilities such as for example
being only able to intro and apply an hypothesis or a lemma they were
given.

Some others may have access to ``tauto``.

In contrast, some rational players have unlimited reasoning
capabilities and know other players' type. Rational players can
therefore reflect on what other players can prove or not and build
their decision on it for their next move in the game.

Non-rational players have never access to CIC terms. I therefore
restrict their Ltac grammar to a consistent but smaller fragment. I
also restrict their list of atomic tactics. For example I would not
allow a variant of apply with patterns or other which opens the door
to CIC terms.

In the case of this question, it is simply a finite sequence of
vanilla intro and apply tactics separated by a dot.

To summarize, a player's type is defined by an Ltac grammar subset, a
list of atomic tactics and a bag of lemmas given at the start of the
game.

Here is the most verbose (smallest steps) proof of a tautology:
|*)

Lemma Or_commutative : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intro P.
  intro Q.
  intro H.
  elim H.
  intro HP.
  right.
  apply HP.
  intro HQ.
  left.
  apply HQ.
Qed.

(*|
It is clear that we need ``elim``, ``right`` and ``left`` tactics.
``intro`` and ``apply`` are not sufficient.

Question: how can I prove that she cannot prove ``Or_commutative``
with only ``intro`` and ``apply``?

.. code-block:: coq

    Goal cannot_prove_or_commutative_with_IAs : ????
    Proof.
    (* Here I want to show that no sequence of vanilla intro and apply
       tactics can solve the goal *)

    (* I may define a structure of proof that is a sequence of intro and
       apply and show that after step 3, it will fail or will not change
       the judgment. How would I do that? *)

    (* Or should I go to the definitions of intro an apply and show that
       they cannot handle OR terms? *)

    (* Or should I investigate plugins to reflect on tactics? I heard of
       Mtac2 recently *)
    Qed.
|*)

(*|
Answer
******

To state this theorem, you need to define a Coq data type that
captures the syntax of propositions you want to work with and
associated inference rules. This can encompass as much of Coq as you
are willing to formalize. To state your commutativity result, all we
need is a simple propositional logic with disjunction and implication.
|*)

Inductive prop : Type :=
| Atomic  : nat -> prop (* Basic propositions *)
| Or      : prop -> prop -> prop
| Implies : prop -> prop -> prop.

Definition commutativity :=
  Implies (Or (Atomic 0) (Atomic 1)) (Or (Atomic 1) (Atomic 0)).

(*|
We can give a semantics to this logic, tying it back to the notion of
truth that comes with Coq; ``assn`` is used to interpret atomic
propositions:
|*)

Fixpoint sem (assn : nat -> Prop) (P : prop) :=
  match P with
  | Atomic x => assn x
  | Or P Q => sem assn P \/ sem assn Q
  | Implies P Q => sem assn P -> sem assn Q
  end.

(*|
Instead of working with tactics, it is easier and more commonplace to
formalize proofs using an entailment relation, which states when a
theorem can proved from a list of assumptions. The following
definition gives all the useful rules for the above fragment:
|*)

Require Import Coq.Lists.List.

Inductive entails : list prop -> prop -> Type :=
| Ax : forall P G, In P G -> entails G P
| OrIL : forall G P Q, entails G P -> entails G (Or P Q)
| OrIR : forall G P Q, entails G Q -> entails G (Or P Q)
| OrE  : forall G P Q R,
    entails (P :: G) R -> entails (Q :: G) R ->
    entails G (Or P Q) -> entails G R
| ImpliesI : forall G P Q,
    entails (P :: G) Q -> entails G (Implies P Q)
| ImpliesE : forall G P Q,
    entails G (Implies P Q) -> entails G P -> entails G Q.

(*|
It should be possible to prove a soundness theorem, saying that the
proofs built from these inference rules yield valid theorems:
|*)

Theorem soundness assn G P :
  entails G P -> Forall (sem assn) G -> sem assn P.
Admitted. (* .none *)

(*|
Only allowing ``intros`` and ``apply`` would amount to ruling out uses
of ``OrE``, which we can enforce with a boolean predicate:
|*)

Fixpoint no_destruct {G P} (pf : entails G P) : bool :=
  match pf with
  | Ax _ _ _ => true
  | OrIL _ _ _ pf => no_destruct pf
  | OrIR _ _ _ pf => no_destruct pf
  | OrE _ _ _ _ _ _ _ => false
  | ImpliesI _ _ _ pf => no_destruct pf
  | ImpliesE _ _ _ pf1 pf2 => no_destruct pf1 && no_destruct pf2
  end.

(*|
You can finally state your metatheorem: any proof of commutativity
must use the ``OrE`` rule:
|*)

Theorem no_commutativity (pf : entails nil commutativity) :
  no_destruct pf = false.
Admitted. (* .none *)

(*|
On top of my head, I do not know exactly how this proof would proceed.
One possibility could be to give your restricted logic a non-standard
interpretation which validates all inference rules, except for
``OrE``, and where ``Or`` is not commutative.
|*)
