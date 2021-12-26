(*|
############################
Cannot determine termination
############################

:Link: https://stackoverflow.com/questions/48289090/cannot-determine-termination
|*)

(*|
Question
********

Function for determining if a set is a subset of another:

.. coq:: none
|*)

Variable (A : Type).
Definition bag := list A.
Variables (beq_nat : nat -> nat -> bool)
          (count : A -> bag -> nat)
          (remove_all : A -> bag -> bag).

Require Import List.
Import ListNotations.

(*||*)

Fail Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => match (beq_nat (count h s1) (count h s2)) with
              | true => subset (remove_all h t) (remove_all h s2)
              | false => false
              end
  end. (* .fails .unfold *)

(*|
For clarity

- ``beq_nat`` determines equality of two natural numbers
- ``count`` counts the number of times a given natural number occurs
  in a set
- ``remove_all`` removes each instance of a given natural number from
  a set

CoqIDE "Cannot guess decreasing argument of fix." Given that the
recursion is being done on a subset of ``t`` (the tail of ``s1``) why
is this not guaranteed to terminate?

**Note:** This problem is from `this website
<https://softwarefoundations.cis.upenn.edu/>`__ whose authors request
solutions not to be posted publicly. Furthermore I have already solved
this exercise so **a solution is not desired**. An explanation of why
Coq can't determine termination would be much appreciated.
|*)

(*|
Answer (Yves)
*************

As a first approximation, the rule for accepting a recursive call is
that in the recursive call one of the arguments should be a *variable*
obtained through *pattern-matching* from the input variable at the
*same rank* in the inputs. In reality, the rule is slightly more
relaxed, but not much.

Here is an instance:
|*)

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.

(*|
The explanation for acceptance is that ``p`` is the argument at rank
1, it is obtained as a pattern-matching variable from ``n``, which is
the initial argument at rank 1. So the function is structurally
recursive, decreasing on the first argument. There should always be an
argument that decreases. Combined decrease between several arguments
is not accepted.

You should stop reading here if you do not want to be drowned in
details.

The first relaxation of the rule is that the decreasing recursive
argument may be a pattern matching construct, as long as the value in
all branches is indeed a variable that is smaller than the first one.
Here is an example of an awkward function that exploits this idea:
|*)

Require Import List Arith.

Fixpoint awk1 (l : list nat) :=
  match l with
  | a :: ((b :: l'') as l') =>
    b :: awk1 (if Nat.even a then l' else l'')
  | _ => l
  end.

(*|
So in the function ``awk1`` the recursive call is not on a variable,
but on a pattern-matching expression, but it is okay because all
possible values of this recursive call are indeed variables obtained
through pattern matching. This also illustrates how picky the
termination checker can be, because the expression ``(if Nat.even a
then (b :: l'') else l'')`` would not be accepted: ``(b :: l'')`` is
not a variable.

The second relaxation of the rule is that the recursive argument can
be a function call, as long as this function call is convertible to an
expression that is accepted. Here is an example, following up on the
previous one.
|*)

Definition arg n (l : list nat) :=
  if Nat.even n then
    l
  else
    match l with _ :: l' => l' | _ => l end.

Fixpoint awk2 (l : list nat) :=
  match l with
  | a :: l' => a :: awk2 (arg a l')
  | _ => l
  end.

(*|
The third relaxation of the rule is that the function used to compute
the recursive argument can even be recursive, as long as it can
transmit the decreasing property recursively. Here is an illustration:
|*)

Fixpoint mydiv (n : nat) (m : nat) :=
  match n, m with
  | S n', S m' => S (mydiv (Nat.sub n' m') m)
  | _, _ => n
  end.

(*|
If you print the definition of ``Nat.sub`` you will see that it is
carefully crafted to always return either the result of a recursive
call, or the first input, and moreover, in recursive calls, the first
argument is indeed a variable obtained through pattern-matching from
the first input. This kind of decreasing property is recognized.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

Your termination argument is correct, but Coq is not smart enough to
figure this out by itself. Roughly speaking, Coq only accepts
recursive calls performed on syntactic subterms of its principal
argument. This is a very restrictive notion: for instance, ``[1; 3]``
is a sublist of ``[0; 1; 2; 3]``, but not a syntactic subterm.

If you want Coq to accept this, you probably need to rewrite your
function using well-founded recursion. Adam Chipala's book CPDT has a
`nice chapter on this
<http://adam.chlipala.net/cpdt/html/GeneralRec.html>`__.
|*)
