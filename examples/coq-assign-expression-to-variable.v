(*|
###################################
Coq - Assign expression to variable
###################################

:Link: https://stackoverflow.com/q/72565664
|*)

(*|
Question
********

First and foremost, I'm not yet very familiar with Coq lingo, so I
will use terms like e.g. 'expression' and 'variable' loosely, but they
are probably not the correct Coq terms.

I'm trying to prove the following subgoal of a Theorem.

.. coq:: none
|*)

Require Import Arith.
Require Import List.
Import ListNotations.

Definition natlist := list nat.
Definition bag := natlist.

Variables (add : nat -> natlist -> natlist) (count : nat -> natlist -> nat).

Section Foo.
Variables (b : bag) (v b' : nat) (b'' : natlist).
Hypotheses (B : b = b' :: b'')
           (IHb'' : b = b'' -> count v (add v b'') = count v b'' + 1).

Goal S (if v =? b' then S (count v b'') else count v b'') =
       (if v =? b' then S (count v b'') else count v b'') + 1.

(*||*)

  Show. (* .unfold .messages *)

(*|
You can ignore ``S`` and ``+ 1``, I'm basically looking for a way to
assign

.. code-block:: coq

    if v =? b' then S (count v b'') else count v b''

to a variable of type ``nat`` because it occurs on both sides of the
equation. How can I do this? Or do I need to go through destroying
``v`` and ``b'`` and proving all cases separately?
|*)

(*|
Answer (Gilles 'SO- stop being evil')
*************************************

Here are two possibilities. There may well be better ones.

You can use `set
<https://coq.inria.fr/refman/proof-engine/tactics.html?highlight=set#coq:tacn.set>`__
to give a name to a term. All the occurrences of that term are
replaced by the variable.
|*)

  set (x := if v =? b' then S (count v b'') else count v b'').

(*|
Sometimes you need to hide the definition of the variable, and only
remember it as an equality that you invoke on demand. For that, use
`remember
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.remember>`__.

You can match the goal against a pattern using the `context
<https://coq.inria.fr/refman/proof-engine/ltac.html#match-term-context>`__
form of `match goal
<https://coq.inria.fr/refman/proof-engine/ltac.html#ltac-match-goal>`__
and give a name to whatever's inside that pattern.
|*)

  Undo. (* .none *)
  match goal with |- context [S ?_x = ?_x + 1] => set (x := _x) end.
End Foo. (* .none *)

(*|
If this is your real goal and not a simplified example, it's a simple
arithmetic statement and you can just call `lia
<https://coq.github.io/doc/v8.13/refman/addendum/micromega.html#coq:tacn.lia>`__
and let Coq figure it out.

.. code-block:: coq

    Require Import Lia.

    ...
    lia.
|*)

(*|
Answer (Ana Borges)
*******************

Besides Gilles's suggestions you can use the `ssreflect set
<https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html>`__
to achieve this, in at least two ways illustrated here:
|*)

Reset Initial. (* .none *)
Require Import Arith ssreflect.

Variables v b' b'' : nat.
Variable count : nat -> nat -> nat.

Goal
  S match v =? b' with
    | true => S (count v b'')
    | false => count v b''
    end
  = match v =? b' with
    | true => S (count v b'')
    | false => count v b''
    end + 1.
Proof.
  set t := (X in S X = X + _).
  Undo.
  set t := match _ with true => _ | false => _ end.

(*|
The latter one also works with the `regular set
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.set>`__
but it needs brackets:
|*)

  Undo. (* .none *)
  set (t := match _ with true => _ | false => _ end).
