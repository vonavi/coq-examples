(*|
#############################################################################
Ltac pattern matching: why does ``forall x, ?P x`` not match ``forall x, x``?
#############################################################################

:Link: https://stackoverflow.com/q/44359515
|*)

(*|
Question
********
|*)

Ltac checkForall H :=
  let T := type of H in
  match T with
  | forall x, ?P x => idtac
  | _ => fail 1 "not a forall"
  end.

Example test : (forall x, x) -> True.
Proof.
  intros H.
  Fail checkForall H. (* not a forall *)
Abort.

(*|
I would naively expect ``checkForall H`` to succeed, but it doesn't.

In his book *Certified Programming with Dependent Types*, Adam
Chlipala `discusses
<http://adam.chlipala.net/cpdt/html/Cpdt.Match.html#lab89>`__ a
limitation of pattern matching on dependent types:

    The problem is that unification variables may not contain locally
    bound variables.

Is this the reason for the behaviour I'm seeing here?
|*)

(*|
Answer (larsr)
**************

The type of ``H`` is ``forall x, x``, not ``forall x, P x``.
|*)

Reset checkForall. (* .none *)
Ltac checkForall H :=
  let T := type of H in
  match T with
  | forall x, ?P x => idtac
  | forall x, x => idtac "this matches"
  | _ => fail 1 "not a forall"
  end.

Example test : (forall x, x) -> True.
Proof.
  intros H.
  checkForall H. (* not a forall *)
Abort.

(*| or to match your ``checkForall`` |*)

Example test {T} (f : T -> Prop) : (forall x, f x) -> True.
Proof.
  intros H.
  checkForall H.
Abort.

(*|
----

**A:** I would add that ``?P x`` represents an `application
<https://coq.inria.fr/refman/Reference-Manual003.html#applications>`__,
whereas ``x`` is an `identifier
<https://coq.inria.fr/refman/Reference-Manual003.html#qualid>`__. They
are syntactically different and cannot be unified.
|*)

(*|
Answer
******

As larsr explained, the pattern ``?P x`` can only match a term that is
syntactically an application, which does not cover the case you are
considering. However, Ltac does provide features for the match you are
looking for. As the `user manual
<https://coq.inria.fr/refman/proof-engine/ltac.html>`__ says:

    There is also a special notation for second-order pattern-matching
    problems: in an applicative pattern of the form ``@?id id1 ...
    idn``, the variable id matches any complex expression with
    (possible) dependencies in the variables ``id1 ... idn`` and
    returns a functional term of the form fun ``id1 ... idn => term``.

Thus, we can write the following proof script:
|*)

Goal (forall x : Prop, x) -> False.
  intros H.
  match goal with
  | H : forall x : Prop, @?P x |- _ => idtac P
  end.

(*| which prints ``(fun x : Prop => x)``. |*)
