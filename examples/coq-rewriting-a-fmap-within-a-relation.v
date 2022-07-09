(*|
############################################
Coq - Rewriting a ``FMap`` Within a Relation
############################################

:Link: https://stackoverflow.com/q/70998788
|*)

(*|
Question
********

I am new to Coq, and was hoping that someone with more experience
could help me with a problem I am facing.

I have defined a relation to represent the evaluation of a program in
an imaginary programming language. The goal of the language is unify
function calls and a constrained subset of macro invocations under a
single semantics. Here is the definition of the relation, with its
first constructor (I am omitting the rest to save space and avoid
unnecessary details).

.. coq:: none
|*)

Require Import FMapList OrderedTypeEx ZArith.

Definition function_definition := nat.
Definition macro_definition := nat.

Module Import NatMap := FMapList.Make(OrderedTypeEx.Nat_as_OT).
Module Import StringMap := FMapList.Make(OrderedTypeEx.String_as_OT).

Definition store : Type := NatMap.t Z.
Definition environment : Type := StringMap.t nat.
Definition function_table : Type := StringMap.t function_definition.
Definition macro_table : Type := StringMap.t macro_definition.

Inductive expr : Type :=
| Num (z : Z).

(*||*)

Inductive EvalExpr :
  store ->         (* Store, mapping L-values to R-values *)
  environment ->   (* Local environment, mapping function-local variables names to L-values *)
  environment ->   (* Global environment, mapping global variables names to L-values *)
  function_table ->(* Mapping function names to function definitions *)
  macro_table ->   (* Mapping macro names to macro definitions *)
  expr ->          (* The expression to evaluate *)
  Z ->             (* The value the expression terminates to *)
  store ->         (* The final state of the program store after evaluation *)
  Prop :=
  (* Numerals evaluate to their integer representation and do not
     change the store *)
| E_Num : forall S E G F M z,
    EvalExpr S E G F M (Num z) z S.

(*|
The mappings are defined as follows:

.. coq:: none
|*)

Reset Initial.

Require Import FMapList OrderedTypeEx ZArith.

Definition function_definition := nat.
Definition macro_definition := nat.

(*||*)

Module Import NatMap := FMapList.Make(OrderedTypeEx.Nat_as_OT).
Module Import StringMap := FMapList.Make(OrderedTypeEx.String_as_OT).

Definition store : Type := NatMap.t Z.
Definition environment : Type := StringMap.t nat.
Definition function_table : Type := StringMap.t function_definition.
Definition macro_table : Type := StringMap.t macro_definition.

(*| .. coq:: none |*)

Inductive expr : Type :=
| Num (z : Z).

Inductive EvalExpr :
  store ->         (* Store, mapping L-values to R-values *)
  environment ->   (* Local environment, mapping function-local variables names to L-values *)
  environment ->   (* Global environment, mapping global variables names to L-values *)
  function_table ->(* Mapping function names to function definitions *)
  macro_table ->   (* Mapping macro names to macro definitions *)
  expr ->          (* The expression to evaluate *)
  Z ->             (* The value the expression terminates to *)
  store ->         (* The final state of the program store after evaluation *)
  Prop :=
  (* Numerals evaluate to their integer representation and do not
     change the store *)
| E_Num : forall S E G F M z,
    EvalExpr S E G F M (Num z) z S.

(*|
I do not think the definitions of the other types are relevant to this
question, but I can add them if needed.

Now when trying to prove the following lemma, which seems intuitively
obvious, I get stuck:
|*)

Lemma S_Equal_EvalExpr_EvalExpr : forall S1 S2,
    NatMap.Equal S1 S2 ->
    forall E G F M e v S',
      EvalExpr S1 E G F M e v S' <-> EvalExpr S2 E G F M e v S'.
Proof.
  intros. split.
  (* -> *)
  - intros. induction H0.
    + (* Num *)
      Fail constructor.

(*|
If I were able to rewrite ``S2`` for ``S1`` in the goal, the proof
would be trivial; however, if I try to do this, I get the following
error:
|*)

      Show. (* .unfold .messages *)
      Fail rewrite <- H. (* .unfold .in .messages *)
Abort. (* .none *)

(*|
I think this has to do with finite mappings being abstract types, and
thus not being rewritable like concrete types are. However, I noticed
that I *can* rewrite mappings within other equations/relations found
in ``Coq.FSets.FMapFacts``. How would I tell Coq to let me rewrite
mapping types inside my ``EvalExpr`` relation?

Update: `Here is a gist
<https://gist.github.com/PappasBrent/140de54b8dbf9bf25214852c6e99daf5>`__
containing a minimal working example of my problem. The definitions of
some of the mapping types have been altered for brevity, but the
problem is the same.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

The issue here is that the relation ``NatMap.Equal``, which says that
two maps have the same bindings, is *not* the same as the notion of
equality in Coq's logic, ``=``. While it is always possible to rewrite
with ``=``, rewriting with some other relation ``R`` is only possible
if you can prove that the property you are trying to show is
compatible with it. This is already done for the relations in
``FMap``, which is why rewriting there works.

You have two options:

1. Replace ``FMap`` with an implementation for which the intended map
   equality coincides with ``=``, a property usually known as
   *extensionality*. There are many libraries that provide such data
   structures, including my own `extructures
   <https://github.com/arthuraa/extructures>`__, but also `finmap
   <https://github.com/math-comp/finmap>`__ and `std++
   <https://gitlab.mpi-sws.org/iris/stdpp>`__. Then, you never need to
   worry about a custom equality relation; all the important
   properties of maps work with ``=``.

2. Keep ``FMap``, but use the `generalized rewriting
   <https://coq.inria.fr/refman/addendum/generalized-rewriting.html>`__
   mechanism to allow rewriting with ``FMap.Equal``. To do this, you
   probably need to modify the definition of your execution relation
   so that it is compatible with ``FMap.Equal``. Unfortunately, I
   believe the only way to do this is by explicitly adding equality
   hypotheses everywhere, e.g.
|*)

Definition EvalExpr' S E G F M e v S' :=
  exists S0 S0', NatMap.Equal S S0 /\
                   NatMap.Equal S' S0' /\
                   EvalExpr S0 E G F M e v S0'.

(*|
   Since this will pollute your definitions, I would not recommend
   this approach.
|*)

(*|
Answer (larsr)
**************

Arthur's answer explains the problem very well.

One other (?) way to do it could be to modify your ``Inductive``
definition of ``EvalExpr`` to explicitly use the equality that you
care about (``NatMap.Equal`` instead of ``Eq``). You will have to say
in each rule that it is enough for two maps to be ``Equal``.

For example:

.. code-block:: coq

    | E_Num : forall S E G F M z,
        EvalExpr S E G F M (Num z) z S

becomes

.. code-block:: coq

    | E_Num : forall S1 S2 E G F M z,
        NatMap.Equal S1 S2 ->
        EvalExpr S1 E G F M (Num z) z S2

Then when you want to prove your ``Lemma`` and apply the constructor,
you will have to provide a proof that ``S1`` and ``S2`` are equal.
(you'll have to reason a little using that ``NatMap.Equal`` is an
equivalence relation).
|*)
