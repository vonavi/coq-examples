(*|
question about intros [=] and intros [= <- H]
=============================================

:Link: https://stackoverflow.com/questions/68059205/question-about-intros-and-intros-h
|*)

(*|
Question
--------

I am a beginner at coq.

I do not know the meaning of `intros [=]` and `intros [= <- H]`. and I
could not find an easy explanation. Would someone explain these two to
me please?

Regards
|*)

(*|
Answer
------

The documentation for this is `here
<https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns>`_.
I will add a little explanation note.

The first historical use of intro patterns is to decompose data that
is packed in inductive objects on the fly. Here is a first easy
example (tested with coq 8.13.2).
|*)

Goal forall A B, A /\ B -> B /\ A.
Proof.

(*|
If you run the tactic `intros A B H` then the hypothesis `H` will be a
proof of `A /\ B`. Morally, this contains knowledge that `A` holds,
but it cannot be used as such, because it is a proof of a stronger
fact. It is often the case that users want directly to decompose this
hypothesis, this would normally be done by typing `destruct H as [Ha
Hb]`. But if you know right away that you will not keep hypothesis
`H`, why not find a shorter expression. This is what the intro pattern
is used for.

So you type the following command and have the resulting goal:
|*)

  intros A B [Ha Hb]. (* .unfold *)
Abort. (* .none *)

(*|
I will not finish this proof. But you get the idea of what intro
patterns are for: decompose information on the fly when inductive
types (like conjunction here) pack several pieces of information
together.

Now, equality information also can pack several pieces of information
together. Assume now that we are working with lists of natural numbers
and we have the following equality.
|*)

Require Import List.

Lemma intro_pattern_example2 n m p q l1 l2 :
  (n :: S m :: l1) = (p :: S q :: l2) -> q :: p :: l2 = m :: n :: l1.

(*|
The equality in the left-hand side of the implication is an equality between two lists, but it actually packs several more elementary pieces of information: `n = p`, `m = q`, and `l1 = l2`. If you just type `intros H`, you obtain the equality between two lists of length 3, but if you type `intros [=]`, you ask the proof system to explore the structure of each equality member and check when constructors appear so that the smaller pieces of information can be placed in separate hypothesis instead of the big one. This is a short hand for the use of the `injection` tactic. Here is the example.
|*)

  intros [= Hn Hm Hl1]. (* .unfold *)

(*|
So you see, this *intro pattern* unpacks information that would
otherwise be stuck in a more complex hypothesis.

Now, when an hypothesis is an equality, there is another action you
might want to perform right away. You might want to rewrite with it.
In intro patterns, this is done by replacing the name you would give
to that equality with an arrow. Let's test this on the previous goal.
|*)

  Undo.
  intros [= -> -> ->]. (* .unfold *)

(*|
Now this goal can be solved quickly with `reflexivity`, `trivial`, or
`auto`. Please note that the hypotheses were used to rewrite, but they
were not kept in the goal context, so this possibility to rewrite
directly from the intro pattern has to be used with caution, because
you are actually losing some information.

The `[=]` intro pattern is used especially for equalities and when
both members are datatype constructors. It exploits the natural
injectivity property of these constructors. there is another property
that is respected by datatype constructors. It is the fact that two
pieces of data with different head constructors can never be equal.
This is exploited in Coq by the `discriminate` tactic. The `[=]` intro
pattern is shorthand for both the `injection` and `discriminate`
tactics.

----

**Q:** Would an explanation like this make it clearer?
https://github.com/tchajed/coq-tricks/blob/master/src/IntroPatterns.v
|*)
