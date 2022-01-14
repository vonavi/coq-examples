(*|
####################################################
How to define an automatically unfoldable definition
####################################################

:Link: https://stackoverflow.com/q/47594706
|*)

(*|
Question
********

I sometimes want to define some shortcut for existing functions like
in the following example:
|*)

Parameter T : Set.
Parameter zero one : T.
Parameter f : T -> T -> option T.
Hypothesis f_unit : forall t, f zero t = None.

Definition g (t : T) := f t one.

(*|
However, this definition seems to be abstract since I cannot use
theorems about ``f`` on instances of ``g`` without first unfolding:
|*)

Goal g zero = None.
  unfold g. rewrite f_unit. reflexivity.
Qed.

(*|
Is there a way to mark definitions as automatically unfoldable?

----

**A:** Yes, I would like not to have to manually ``unfold``.

**A:** You could allow ``simpl`` to expand the definition of ``g`` by
declaring ``Arguments g t /.``

**A:** Or define ``g`` as a "parsing-only" shorthand notation instead
of a function. Something like: ``Notation "'g' t" := (f t one) (at
level 0, parsing only).``

**A:** Or ``Hint Unfold g.`` and then use ``autounfold`` tactic in the
proof.

**A:** Also, ssreflect can do it with with context patterns: ``Require
Import ssreflect.`` then your goal can be proved by ``by rewrite [g
_]f_unit.``. This ``[g _]`` pattern makes ``rewrite`` to unfold the
definition of ``g``.
|*)

(*|
Answer
******

There are a couple of ways to accomplish what you ask, and here is an
explanation of the ones I know:

----

1. Use an abbreviation. To quote `the reference manual
   <https://coq.inria.fr/refman/syntax-extensions.html#Abbreviations>`__:

       An *abbreviation* is a name, possibly applied to arguments,
       that denotes a (presumably) more complex expression.

       [...]

       Abbreviations are bound to an absolute name as an ordinary
       definition is, and they can be referred by qualified names too.

       Abbreviations are syntactic in the sense that they are bound to
       expressions which are not typed at the time of the definition
       of the abbreviation but at the time it is used.

   In your case, this would be
|*)

Reset g. (* .none *)
Notation g t := (f t one).

(*|
   This is much like Daniel Schepler's suggestion of a ``Notation``,
   except that it does not reserve ``g`` as a global keyword.

----

2. Use ``setoid_rewrite``. Coq's ``setoid_rewrite`` tactic is similar
   to ``rewrite``, except that it looks for occurrences modulo δ
   (unfolding), can rewrite under binders, and a few other minor
   things.

   For your example, this is:
|*)

Reset g. (* .none *)
Definition g (t : T) := f t one. (* .none *)
Require Import Coq.Setoids.Setoid.
Goal g zero = None.
Proof.
  setoid_rewrite f_unit. reflexivity.
Qed.

(*|
----

3. In some cases, you can use ``Set Keyed Unification`` and ``Declare
   Equivalent Keys``, though this does not work in your case (I've
   opened an issue `on GitHub here
   <https://github.com/coq/coq/issues/6317>`__. This tells ``rewrite``
   to "unfold" one head constant to another, though it apparently
   isn't quite good enough to handle your case. There's a bit of
   documentation `on the relevant commit message
   <https://github.com/coq/coq/commit/3fe4912b568916676644baeb982a3e10c592d887>`__,
   and an `open issue to add proper documentation
   <https://github.com/coq/coq/issues/4551>`__.

   Here is an example this is useful:
|*)

Reset Initial. (* .none *)
Parameter T : Set.
Parameter zero one: T.
Parameter f : T -> T -> option T.
Hypothesis f_unit : forall t, f zero t = None.

Definition g := f zero zero.

Set Keyed Unification.
Goal g = None.
Proof.
  Fail rewrite f_unit. (* .fails *)
  Declare Equivalent Keys g f.
  rewrite f_unit. reflexivity.
Qed.
