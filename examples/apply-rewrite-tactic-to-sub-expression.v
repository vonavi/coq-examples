(*|
######################################
apply rewrite tactic to sub-expression
######################################

:Link: https://stackoverflow.com/q/55786746
|*)

(*|
Question
********

How can I apply ``rewrite ->`` targetting only a sub-expression? For
example, consider this theorem:
|*)

Parameter add : nat -> nat -> nat.
Axiom comm : forall a b, add a b = add b a.

Theorem t1 : forall a b : nat,
    add (add a b) (add a (add a b)) = add (add a b) (add a (add b a)).
Abort. (* .none *)

(*|
Intuitively, it requires commuting only one ``(add a b)``
sub-expression, but if I do ``rewrite -> (comm a b)``, it rewrites all
the occurrences. How can I target a particular sub-expression?
|*)

(*|
Answer (ejgallego)
******************

This is a case where the ssreflect matching facilities will usually be
more convenient than "``at``" [I'd dare to say sub-term rewrites are
often a cause of people switching to ssreflect's rewrite]. In
particular:

- ``rewrite {pos}[pat]lemma`` will select occurrences ``pos`` of
  pattern ``pat`` to rewrite,
- ``pat`` can be a `contextual pattern
  <https://coq.inria.fr/distrib/current/refman/proof-engine/ssreflect-proof-language.html#contextual-patterns>`__
  that may allow you improve the robustness of your scripts.
|*)

(*|
Answer (Gilles 'SO- stop being evil')
*************************************

You can target a specific occurrence with the ``rewrite`` tactic using
the suffix ``at N``. Occurrences are numbered from 1 in left-to-right
order. You can rewrite multiple occurrencess by separating their
indices with spaces. You need ``Require Import Setoid``. The ``at``
suffix is also available with some other tactics that target
occurrences of a term, including many tactics that perform conversions
(``change``, ``unfold``, ``fold``, etc.), ``set``, ``destruct``, etc.
|*)

Require Import Setoid. (* .none *)
Theorem t1 : forall a b : nat,
    add (add a b) (add a (add a b)) = add (add a b) (add a (add b a)). (* .none *)
  intros. rewrite -> (comm a b) at 2. reflexivity.
  Restart. (* .none *)

(*|
There are other possible approaches, especially if all you need is to
apply equalities. The ``congruence`` tactic can find what to rewrite
and apply symmetry and transitivity on its own, but you need to prime
it by adding all equivalences to the context (in the form of
universally-quantified equalities), it won't query hint databases.
|*)

  intros. (* .none *)
  assert (Comm := comm). congruence.
  Restart. (* .none *)

(*|
To get more automation, ``Hint Rewrite`` creates a database of
theorems which the tactic ``autorewrite`` will try applying. For more
advanced automation, look up `generalized rewriting
<https://coq.inria.fr/refman/addendum/generalized-rewriting.html>`__
with setoids, which I'm not sufficiently familiar with to expound on.

----

**A:** In cases like this one, we can target the right subexpression
by choosing the arguments of ``comm``:
|*)

  intros a b. rewrite (comm b a). reflexivity.
Qed. (* .none *)
