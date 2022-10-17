(*|
#################################################
Case analysis on evidence of equality type in Coq
#################################################

:Link: https://stackoverflow.com/q/48161372
|*)

(*|
Question
********

I have a query about inductively defined relation ``eq`` in Coq.
Consider the following definition of ``eq`` in Coq:
|*)

Print eq. (* .unfold .messages *)

(*|
This is an inductively defined relation just like ``Le`` (``<=``).
Therefore I should be able to do case analysis on any evidence of this
type. However, when I tried proving the following result I could not
succeed.
|*)

Lemma true_num : forall m : nat, forall x y : m = m, x = y.
Proof.
  intros. Fail destruct x. (* .fails .unfold .in .messages *)

(*|
I am unable to decode this error.

The only proof for ``m = m`` should be ``@eq_refl nat m`` since
``eq_refl`` is the only constructor. Hence one should be able to prove
the equality of ``x`` and ``y`` by doing case analysis.

What is wrong with this line of reasoning?
|*)

(*|
Answer (ejgallego)
******************

The error is due to the way ``destruct`` works, recall that the tactic
tries to build a match statement, and in order to do so it has some
heuristics as to bring dependent hypotheses into context.

In particular, in this case it tries to abstract over the variable
``m``, which is an index to the ``eq`` inductive in ``y : m = m``;
however ``y`` is not brought into context, hence the error as ``m !=
m0`` [with ``m0`` being the abstracted ``m``]. You can workaround that
problem it by doing a "less smart" match, which won't modify ``m``:
|*)

  refine (match x with | @eq_refl _ _ => _ end). Undo. (* .none *)

(*|
but usually, the best solution is to bring the hypothesis at fault
into scope:
|*)

  revert y. destruct x.
Abort. (* .none *)

(*|
On the other hand, to prove your goal simple pattern-matching won't
suffice as pointed out by the other excellent answers. My preferred
practical approach to solve goals like yours is to use a library:
|*)

From mathcomp Require Import all_ssreflect.

Lemma true_num (m : nat) (x y : m = m) : x = y.
Proof. exact: eq_irrelevance. Qed.

(*|
In this case, the proper side conditions for the ``nat`` type are
inferred automatically by the machinery of the library.
|*)

(*|
Answer (Jason Gross)
********************

    The only proof for ``m = m`` should be ``@eq_refl nat m`` since
    ``eq_refl`` is the only constructor

No. Your theorem happens to be true because you are talking about
equality of ``nat``, but your reasoning goes through just as well (or
poorly) if you replace ``nat`` with ``Type``, and replacing ``nat``
with ``Type`` makes the theorem unprovable.

The issue is that the equality type *family is freely generated* by
the reflexively proof. Therefore, since everything in Coq respects
equality in the right way (this is the bit I'm a bit fuzzy on), to
prove a property of all proofs of equality in a family (i.e. all
proofs of ``x = y`` for some fixed ``x`` and *for all* ``y``), it
suffices to prove the property of the generator, the reflexively
proof. However, once you fix both endpoints, so to speak, you no
longer have this property. Said another way, the induction principle
for ``eq`` is really an induction principle for ``{ y | x = y }``, not
for ``x = y``. Similarly, the induction principle for vectors
(length-indexed lists) is really an induction principle for ``{ n &
Vector.t A n }``.

To decode the error messages, it might help to try manually applying
the induction principle for ``eq``. The induction principle states:
given a type ``A``, a term ``x : A``, and a property ``P : forall y :
A, x = y -> Prop``, to prove ``P y e`` for any given ``y : A`` and any
proof ``e : x = y``, it suffices to prove ``P x eq_refl``. (To see why
this makes sense, consider the non dependent version: given a type
``A``, a term ``x : A``, and a property ``P : A -> Prop``, for any ``y
: A`` and any proof ``e : x = y``, to prove ``P y``, it suffices to
prove ``P x``.)

If you try applying this by hand, you will find that there is no way
to construct a well-typed function ``P`` when you are trying to induct
over the second proof of equality.

There is an excellent blog post that explains this in much more depth here: http://math.andrej.com/2013/08/28/the-elements-of-an-inductive-type/
|*)
