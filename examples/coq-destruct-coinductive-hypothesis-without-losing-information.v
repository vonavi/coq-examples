(*|
#################################################################
Coq: destruct (co)inductive hypothesis without losing information
#################################################################

:Link: https://stackoverflow.com/q/45151308
|*)

(*|
Question
********

Consider the following development:
|*)

Require Import Relation_Definitions RelationClasses.

Set Implicit Arguments.

CoInductive stream (A : Type) : Type :=
| scons : A -> stream A -> stream A.

CoInductive stream_le (A : Type) {eqA R : relation A}
            `{PO : PartialOrder A eqA R} :
  stream A -> stream A -> Prop :=
| le_step : forall h1 h2 t1 t2, R h1 h2 ->
                                (eqA h1 h2 -> stream_le t1 t2) ->
                                stream_le (scons h1 t1) (scons h2 t2).

(*|
If I have a hypothesis ``stream_le (scons h1 t1) (scons h2 t2)``, it
would be reasonable for the ``destruct`` tactic to turn it into a pair
of hypotheses ``R h1 h2`` and ``eqA h1 h2 -> stream_le t1 t2``. But
that's not what happens, because ``destruct`` loses information
whenever doing anything non-trivial. Instead, new terms ``h0``,
``h3``, ``t0``, ``t3`` are introduced into the context, with no recall
that they are respectively equal to ``h1``, ``h2``, ``t1``, ``t2``.


I would like to know if there is a quick and easy way to do this kind
of "smart ``destruct``". Here is what i have right now:
|*)

Theorem stream_le_destruct :
  forall (A : Type) eqA R
         `{PO : PartialOrder A eqA R} (h1 h2 : A) (t1 t2 : stream A),
    stream_le (scons h1 t1) (scons h2 t2) ->
    R h1 h2 /\ (eqA h1 h2 -> stream_le t1 t2).
Proof.
  intros.
  destruct H eqn:Heq. Undo.
  remember (scons h1 t1) as s1 eqn:Heqs1.
  remember (scons h2 t2) as s2 eqn:Heqs2.
  destruct H.
  inversion Heqs1. inversion Heqs2. subst.
  split; assumption.
Qed.

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

Calling ``destruct`` will not directly give you what you want. You
need to use ``inversion`` instead.
|*)

Reset stream_le_destruct. (* .none *)
Theorem stream_le_destruct :
  forall (A : Type) eqA R
         `{PO : PartialOrder A eqA R} (h1 h2 : A) (t1 t2 : stream A),
    stream_le (scons h1 t1) (scons h2 t2) ->
    R h1 h2 /\ (eqA h1 h2 -> stream_le t1 t2).
Proof.
  intros.
  inversion H. subst.
  split; assumption.
Qed.

(*|
Unfortunately, the ``inversion`` tactic is quite ill behaved, as it
tends to generate a lot of spurious equality hypotheses, making it
hard to name them consistently. One (somewhat heavyweight, admittedly)
alternative is to use ``inversion`` only to prove a lemma like the one
you did, and apply this lemma in proofs instead of calling
``inversion``.
|*)

(*|
Answer (ejgallego)
******************

Indeed, ``inversion`` basically does what you want, however as Arthur
pointed out it is a bit unstable, mainly due to the different
congruence steps.

Under the hood, ``inversion`` just calls a version of ``destruct``,
but remembering some equalities first. As you have well discovered,
pattern matching in Coq will "forget" arguments of constructors,
except if these are variables, then, all the variables *under the
scope* of the destruct will be instantiated.

What does that mean? It means that in order to properly destruct an
inductive ``I : Idx -> Prop``, you want to get your goal of the form:
``I x -> Q x``, so that destructing the ``I x`` will also refine the
``x`` in ``Q``. Thus, a standard transformation for an inductive ``I
term`` and goal ``Q (f term)`` is to rewrite it to ``I x -> x = term
-> Q (f x)``. Then, destructing ``I x`` will get you ``x``
instantiated to the proper index.

With that in mind, it may be a good exercise to implement inversion
manually using the ``case:`` tactic of Coq 8.7;
|*)

Reset stream_le_destruct. (* .none *)
From Coq Require Import ssreflect.

Theorem stream_le_destruct A eqA R
        `{PO : PartialOrder A eqA R} (h1 h2 : A) (t1 t2 : stream A) :
  stream_le (scons h1 t1) (scons h2 t2) ->
  R h1 h2 /\ (eqA h1 h2 -> stream_le t1 t2).
Proof.
  move E1: (scons h1 t1) => sc1. move E2: (scons h2 t2) => sc2 H.
  by case: sc1 sc2 / H E1 E2 => h1' h2' t1' t2' hr ih [? ?] [? ?]; subst.
Qed.

(*|
You can read the manual for more details, but basically with the first
line, we create the equalities we need; then, in the second we can
destruct the term and get the proper instantiations solving the goal.
A good effect of the ``case:`` tactic is that, contrary to destruct,
it will try to prevent us from destructing a term without first
bringing its dependencies into scope.
|*)
