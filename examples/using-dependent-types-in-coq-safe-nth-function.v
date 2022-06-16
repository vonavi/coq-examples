(*|
####################################################
Using dependent types in Coq (safe ``nth`` function)
####################################################

:Link: https://stackoverflow.com/q/27637949
|*)

(*|
Question
********

I'm trying to learn Coq, but I find it hard to make the leap from what
I read in *Software Foundations and Certified Programming with
Dependent Types* to my own use cases.

In particular, I thought I'd try to make a verified version of the
``nth`` function on lists. I managed to write this:
|*)

Require Import Arith.
Require Import List.
Import ListNotations.

Lemma zltz : 0 < 0 -> False.
Proof.
  intros. contradict H. apply Lt.lt_irrefl.
Qed.

Lemma nltz : forall n : nat, n < 0 -> False.
Proof.
  intros. contradict H. apply Lt.lt_n_0.
Qed.

Lemma predecessor_proof : forall {X : Type} (n : nat) (x : X) (xs : list X),
    S n < length (x :: xs) -> n < length xs.
Proof.
  intros. simpl in H. apply Lt.lt_S_n. assumption.
Qed.

Fixpoint safe_nth {X : Type} (n : nat) (xs : list X) : n < length xs -> X :=
  match n, xs with
  | 0, [] => fun pf : 0 < length [] => match zltz pf with end
  | S n', [] => fun pf : S n' < length [] => match nltz (S n') pf with end
  | 0, x :: _ => fun _ => x
  | S n', x :: xs' => fun pf : S n' < length (x :: xs') =>
                        safe_nth n' xs' (predecessor_proof n' x xs' pf)
  end.

(*|
This works, but it raises two questions:

1. How would experienced Coq users write this? Are the three lemmas
   really necessary? Is this a use case for ``{ | }`` types?
2. How do I call this function from other code, i.e., how do I supply
   the required proofs?

I tried this:

.. code-block:: coq

    Require Import NPeano.
    Eval compute in
      if ltb 2 (length [1; 2; 3]) then safe_nth 2 [1; 2; 3] ??? else 0.

But of course this won't work until I figure out what to write for the
``???`` part. I tried putting ``2 < length [1; 2; 3]`` there but that
has type ``Prop`` rather than type ``2 < length [1; 2; 3]``. I could
write and prove a lemma of that specific type, and that works. But
what's the general solution?
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

I don't think there is a consensus on what the best way for doing this
sort of thing is.

I believe that usually Coq developments tend to favor indexed
inductive types for writing code like that. This is the solution
followed by the `vector library
<https://coq.inria.fr/distrib/current/stdlib/Coq.Vectors.Vector.html>`__
in the Coq distribution. There, you would define an indexed inductive
type for vectors and another one for bounded integers (called
``Vector.t`` and ``Fin.t`` in the standard library, respectively).
Some functions, such as ``nth``, are much simpler to write in this
style, since pattern matching on vectors and indices ends up doing a
little bit of reasoning for you when getting rid of contradictory
cases and doing recursive calls, for instance. The disadvantage is
that dependent pattern matching in Coq is not very intuitive, and
sometimes you have to write your functions in a weird way to get them
to work. Another problem with this approach is that one needs to
redefine many functions that work on lists to work on vectors.

Another solution is to define bounded integers as a dependent pair of
a ``nat`` and a proof that that index is bounded, which is essentially
what you going for when you mentioned ``{ | }`` types. This is the
approach followed by the `ssreflect
<http://ssr.msr-inria.inria.fr/~jenkins/current/Ssreflect.fintype.html>`__
library, for instance (look fot the ``ordinal`` type). To define a
safe ``nth`` function, what they do is to define a simple version that
takes a default element to return when the index is out of bounds, and
use the proof that ``n < length l`` to supply that default element
(have a look for instance at `tuple
<http://ssr.msr-inria.inria.fr/~jenkins/current/Ssreflect.tuple.html>`__
library of ssreflect, where they define length-indexed lists, and see
how they define ``tnth``). The advantage is that it is easier to
relate the more informative types and functions to the simpler
variants. The disadvantage is that some things become harder to
express directly: for instance, you can't do pattern-matching directly
on an ssreflect tuple.

Another point worth noting is that very often it is easier to work
with boolean properties instead of inductively defined ones, because
computation and simplification obviate the need for some lemmas. Thus,
when using a boolean version of ``<``, Coq doesn't make a difference
between a proof of ``0 < 0 = true`` and ``false = true``, or between a
proof of ``S n < length (x :: l) = true`` and a proof of ``n < length
l = true``, which means that you would be able to use those proofs
directly in your definition of ``nth`` without having to massage them
with auxiliary lemmas. The Coq standard library, unfortunately, tends
to favor inductively defined types over boolean computations in many
cases where they are not useful, such as for defining ``<``. The
`ssreflect <http://ssr.msr-inria.inria.fr/>`__ library, on the other
hand, makes much more use of boolean computations for defining
properties, making it more appropriate for this style of programming.
|*)

(*|
Answer (Perce Strop)
********************

``zltz`` has the same type as ``nltz 0``.
|*)

Check zltz.
Check nltz 0.

(*|
To use your function with ``2`` and ``[1; 2; 3]`` from within another
function, you can use ``lt_dec``.
|*)

Eval compute in match lt_dec 2 (length [1; 2; 3]) with
                | left pf => safe_nth 2 [1; 2; 3] pf
                | right _ => 0
                end.

(*|
If you extract ``lt_dec``, you'll find it's very similar to ``ltb``
after the proofs are erased. You don't need to use ``lt_dec`` if you
can build your proof from within the function where ``safe_nth`` is
called.

You can shorten your function a bit like this.
|*)

Fixpoint safe_nth' {X : Type} (xs : list X) (n : nat) : n < length xs -> X :=
  match xs, n with
  | [], _ => fun pf => match nltz n pf with end
  | x :: _, 0 => fun _ => x
  | x :: xs', S n' => fun pf => safe_nth' xs' n' (predecessor_proof n' x xs' pf)
  end.

(*|
I'm not sure what best practices are, but you get tidier extracted
code if you use ``sig``.

----

**Q:** Thanks for the explanation using ``lt_dec``, that was the piece
I was missing! And yes, I had seen the similarity between ``zltz`` and
``nltz`` but missed the equivalence...
|*)
