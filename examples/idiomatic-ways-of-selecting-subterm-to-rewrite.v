(*|
##############################################
Idiomatic ways of selecting subterm to rewrite
##############################################

:Link: https://stackoverflow.com/q/44516470
|*)

(*|
Question
********

Suppose we have a conclusion of form: ``a + b + c + d + e``. We also
have a lemma:
|*)

Lemma plus_assoc : forall n m p : nat, n + (m + p) = n + m + p.
Admitted.

(*|
What are idiomatic ways to arbitrarily "insert a pair of parentheses"
into the term? That is, how can we easily choose where to rewrite if
there's more than one available place.

What I generally end up doing is the following:

.. coq:: none
|*)

Goal forall a b c d e, a + b + c + d + e = a + b + c + (d + e).
Proof.
  intros a b c d e.

(*||*)

  replace (a + b + c + d + e) with (a + b + c + (d + e))
    by now rewrite plus_assoc.

(*|
And while this formulation does state exactly what I want to do, it
gets extremely long-winded for formulations more complicated than ``a
+ b + c + ...``.
|*)

(*|
Answer (Gilles 'SO- stop being evil')
*************************************

``rewrite <- lemma`` expects ``lemma`` to be an equality, that is, a
term whose type is of the form ``something1 = something2``. Like with
most other tactics, you can also pass it a function that returns an
equality, that is, a term whose type is of the form ``forall param1
... paramN, something1 = something2``, in which case Coq will look for
a place where it can apply the lemma to parameters to form a subterm
of the goal. Coq's algorithm is deterministic, but letting it choose
is not particularly useful except when performing repeated rewrites
that eventually exhaust all possibilities. Here Coq happens to choose
your desired goal with ``rewrite <- plus_assoc``, but I assume that
this was just an example and you're after a general technique.

You can get more control over where to perform the rewrite by
supplying more parameters to the lemma, to get a more specific
equality. For example, if you want to specify that ``(((a + b) + c) +
d) + e`` should be turned into ``((a + b) + c) + (d + e)``, i.e. that
the associativity lemma should be applied to the parameters ``(a + b)
+ c``, ``d`` and ``e``, you can write
|*)

  Undo. (* .none *) rewrite <- (plus_assoc ((a + b) + c) d e).

(*|
You don't need to supply all the parameters, just enough to pinpoint
the place where you want to apply the lemma. For example, here, it's
enough to specify ``d`` as the second argument. You can do this by
leaving the third parameter out altogether and specifying the wildcard
``_`` as the first parameter.
|*)

  Undo. (* .none *) rewrite <- (plus_assoc _ d).

(*|
Occasionally there are identical subterms and you only want to rewrite
one of them. In this case you can't use the ``rewrite`` family of
tactics alone. One approach is to use ``replace`` with a bigger term
where you pick what you want to change, or event ``assert`` to replace
the whole goal. Another approach is to use the ``set`` tactics, which
lets you give a name to a specific occurrence of a subterm, then rely
on that name to identify specific subterms, and finally call ``subst``
to get rid of the name when you're done.

An alternative approach is to forget about which lemmas to apply, and
just specify how you want to change the goal with something like
``assert`` or a plain ``replace ... with ... .``. Then let automated
tactics such as ``congruence``, ``lia``, ``solve [firstorder]``, etc.
find parameters that make the proof work. With this approach, you do
have to write down big parts of the goal, but you save on specifying
lemmas. Which approach works best depends on where you are on a big
proof and what tends to be stable during development and what isn't.
|*)

(*|
Answer (ejgallego)
******************

IMO your best option is to use the ssreflect pattern selection
language, available in Coq 8.7 or by installing math-comp in earlier
versions. This language is documented in the manual:
https://hal.inria.fr/inria-00258384

Example (for Coq 8.7):
|*)

Reset Initial. (* .none *)
(* Replace with From mathcomp Require ... in Coq < 8.7 *)
From Coq Require Import ssreflect ssrfun ssrbool.

Lemma addnC n m : m + n = n + m. Admitted.
Lemma addnA m n o : m + (n + o) = m + n + o. Admitted.

Lemma example m n o p : n + o + p + m = m + n + o + p.
Proof. by rewrite -[_ + _ + o]addnA -[m + _ + p]addnA [m + _]addnC.
Qed.

(*|
Answer (Anton Trunov)
*********************

If you don't want to prove a helper lemma, then one of your choices is
using Ltac to pattern match on the structure of the equality on your
hands. This way you can bind arbitrary complex subexpressions to
pattern variables:
|*)

Require Import Coq.Arith.Arith.

Goal forall a b c d e,
    (a + 1 + 2) + b + c + d + e = (a + 1 + 2) + (b + c + d) + e -> True.
  intros a b c d e H.
  match type of H
  with ?a + ?b + ?c + ?d + ?e = _ =>
         replace (a + b + c + d + e)
         with (a + (b + c + d) + e) in H
           by now rewrite <- ?plus_assoc
  end.
Abort.

(*|
In the above piece of code ``?a`` stands for ``a + 1 + 2``. This, of
course, doesn't improve anything if you are dealing with simple
variables, it helps only when you are dealing with complex nested
expressions.

Also, if you need to rewrite things in the goal, then you can use
something like this:

.. code-block:: coq

    match goal with
    | |- ?a + ?b + ?c + ?d + ?e = _ => <call your tactics here>
    end.
|*)
