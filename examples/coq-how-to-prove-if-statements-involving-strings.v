(*|
##################################################
Coq: How to prove if statements involving strings?
##################################################

:Link: https://stackoverflow.com/q/46434503
|*)

(*|
Question
********

I have a ``string a`` and on comparison with ``string b``, if equals
has an ``string c``, else has ``string x``. I know in the hypothesis
that ``fun x <= fun c``. How do I prove this below statement? ``fun``
is some function which takes in ``string`` and returns ``nat``.

.. code-block:: coq

    fun (if a == b then c else x) <= S (fun c).

The logic seems obvious but I am unable to split the if statements in
coq. Any help would be appreciated.
|*)

(*|
Answer (ejgallego)
******************

Let me complement Yves answer pointing out to a general "view" pattern
that works well in many situations were case analysis is needed. I
will use the built-in support in math-comp but the technique is not
specific to it.

Let's assume your initial goal:
|*)

From mathcomp Require Import all_ssreflect.

Variables (T : eqType) (a b : T).
Lemma u : (if a == b then 0 else 1) = 2.
Proof.

(*|
now, you could use ``case_eq`` + ``simpl`` to arrive to next step;
however, you can also match using more specialized "view" lemmas. For
example, you could use ``ifP``:
|*)

  Check ifP. (* .unfold .messages *)

(*| where ``if_spec`` is: |*)

  Print if_spec. (* .unfold .messages *)

(*|
That looks a bit confusing, the important bit is the parameters to the
type family ``bool -> A -> Set``. The first exercise is "prove the
``ifP`` lemma!".

Indeed, if we use ``ifP`` in our proof, we get:
|*)

  case: ifP.
  Show. (* .unfold .goals *)

(*|
Note that we didn't have to specify anything! Indeed, lemmas of the
form ``{ A } + { B }`` are just special cases of this view pattern.
This trick works in many other situations, for example, you can also
use ``eqP``, which has a spec relating the boolean equality with the
propositional one. If you do:
|*)

  Undo. (* .none *)
  case: eqP.

(*| you'll get: |*)

  Show. (* .unfold .goals *)
Abort. (* .none *)

(*|
which is very convenient. In fact, ``eqP`` is basically a generic
version of the ``type_dec`` principle.

----

**Q:** Where does the name "view" come from and what is the general
intuition one should have about views? I mean, they are not rewriting
equations or inversion lemmas.

**A:** I am not sure where does the name "view" come from, likely
there are better names, maybe "specification". I call it view as for
some operators (ie ``<=``) you have different "views" on the case
analysis. The intuition behind a "view" is that it will do case
analysis on some construction, *populating the context properly* as to
continue the proof. This is sometimes not trivial and usually saves
quite a bit amount of time.
|*)

(*|
Answer (Yves)
*************

If you can write an if-then-else statement, it means that the test
expression ``a == b`` is in a type with two constructors (like
``bool``) or (``sumbool``). I will first assume the type is ``bool``.
In that case, the best approach during a proof is to enter the
following command.

.. coq:: none
|*)

Reset Initial.
Require Import Coq.Strings.String.
Notation "a == b" := (eqb a b) (at level 70, no associativity).

Variables (a b c x : string) (fn : string -> nat).

Goal fn (if a == b then c else x) <= S (fn c).

(*||*)

  case_eq (a == b); intros hyp_ab.

(*|
This will generate two goals. In the first one, you will have an
hypothesis that asserts that the test succeeds and the goal conclusion
has the following shape (the *if-then-else* is replaced by the *then*
branch):
|*)

  Show 1. (* .unfold .messages *)

(*|
In the second goal, you will have an hypothesis and the goal
conclusion has the following shape (the *if-then-else* is replaced by
the *else* branch).
|*)

  Show 2. (* .unfold .messages *)
Abort. (* .none *)

(*|
You should be able to carry on from there.

On the other hand, the ``String`` library from Coq has a function
``string_dec`` with return type
|*)

Check string_dec. (* .unfold .messages *)

(*|
If your notation ``a == b`` is a pretty notation for ``string_dec a
b``, it is better to use the following tactic:

.. coq:: none
|*)

Reset Initial.
Require Import Coq.Strings.String.
Notation "a == b" := (string_dec a b) (at level 70, no associativity).

Variables (a b c x : string) (fn : string -> nat).

Goal fn (if a == b then c else x) <= S (fn c).

(*||*)

  destruct (a == b) as [hyp_ab | hyp_ab].
  Abort. (* .none *)

(*|
The behavior will be quite close to what I described above, only
easier to use.

Intuitively, when you reason on an *if-then-else* statement, you use a
command like ``case_eq``, ``destruct``, or ``case`` that leads you to
studying separately the two executions paths, remember in an
hypothesis why you took each of these executions paths.
|*)
