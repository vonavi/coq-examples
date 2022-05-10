(*|
#######################################################################################
Coq losing information from if-statement when doing recursive function with ``Program``
#######################################################################################

:Link: https://stackoverflow.com/q/43897968
|*)

(*|
Question
********

I want to write this recursive variant of ``gcd`` as simply and
"naturally" as possible in Coq.
|*)

Require Import Arith.
Require Import Program.

Program Fixpoint gcd (a b : nat) {measure b} :=
  if 0 <? b then gcd b (a mod b) else a.
Next Obligation.
  (* Here I need to prove that `a mod b < b` *)
  apply Nat.mod_upper_bound.

(*|
Now I need to prove that ``b <> 0`` but I have lost the info that we
are in the ``0 <? b = false`` branch.
|*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
How do I keep the information from the if statement?

I know I could use ``match``, but how to I write it with ``if``?
|*)

Reset gcd. (* .none *)
Program Fixpoint gcd (a b : nat) {measure b} :=
  match b with 0 => a | S b' => gcd b (a mod b) end.
Next Obligation.
  apply Nat.mod_upper_bound.
  (* Goal:  S b' <> 0 *)
  congruence.
Defined.

(*|
=== EDIT ===

I noticed that Coq (in more recent versions?) remembers the
association between ``0 <? b`` and the match patterns (``true`` or
``false`` in this case). Or is it a feature of ``Program``? Anyway, I
thought that ``if`` essentially was expanded into this ``match``
statement, but apparently it isn't...
|*)

Reset gcd. (* .none *)
Program Fixpoint gcd (a b : nat) {measure b} : nat:=
  match 0 <? b with
  | true => gcd b (a mod b)
  | false => a
  end.
Next Obligation.
  apply Nat.mod_upper_bound.
  (* now we have ` true = (0 <? b)` in the assumptions, and the goal `b <> 0` *)
  now destruct b.
Defined.

(*|
----

**A:** `This
<http://stackoverflow.com/questions/42285235/writing-well-founded-programs-in-coq-using-fix-or-program-fixpoint>`__
is a related question.
|*)

(*|
Answer
******

One can use ``lt_dec`` to do that.
|*)

Print lt_dec. (* .unfold .messages *)

(*|
This way we can keep the proofs we need in the context, unlike when
using ``<?``, which returns a ``bool``.
|*)

Reset Initial. (* .none *)
Require Import Arith.
Require Import Program.

Program Fixpoint gcd (a b : nat) {measure b} :=
  if lt_dec 0 b then gcd b (a mod b) else a.
Next Obligation.
  apply Nat.mod_upper_bound.
  now destruct H.
Defined.

(*|
----

Yes, it is a feature of ``Program``. Actually the reference manual
explain it in a very clear manner (see `§24.1
<https://coq.inria.fr/distrib/current/refman/Reference-Manual027.html#sec752>`__):

    Generation of equalities. A ``match`` expression is always
    generalized by the corresponding equality. As an example, the
    expression:

    .. code-block:: coq

        match x with
        | 0 => t
        | S n => u
        end.

    will be first rewritten to:

    .. code-block:: coq

        (match x as y return (x = y -> _) with
         | 0 => fun H : x = 0 -> t
         | S n => fun H : x = S n -> u
         end) (eq_refl n).

Here is the reason why ``if`` is different:

    To give more control over the generation of equalities, the
    typechecker will fall back directly to Coq's usual typing of
    dependent pattern-matching if a ``return`` or ``in`` clause is
    specified. Likewise, the ``if`` construct is not treated specially
    by ``Program`` so boolean tests in the code are not automatically
    reflected in the obligations. One can use the ``dec`` combinator
    to get the correct hypotheses as in:
|*)

Program Definition id (n : nat) : { x : nat | x = n } :=
  if dec (leb n 0) then 0
  else S (pred n).
