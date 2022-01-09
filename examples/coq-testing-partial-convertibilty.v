(*|
##################################
Coq: Testing partial convertibilty
##################################

:Link: https://stackoverflow.com/q/47838883
|*)

(*|
Question
********

In the following example, unification (unsurprisingly) doesn't infer a
canonical structure:
|*)

Structure Pn := sr {gs: nat}.
Canonical Structure Pn_1: Pn := sr 1.
Canonical Structure Pn_2: Pn := sr 2.

(* fail *)
Check ltac:(tryif unify 2 (gs _) then idtac "success" else idtac "fail").
(* success *)
Check ltac:(tryif unify 2 (gs Pn_2) then idtac "success" else idtac "fail").

(*|
Is it possible to make the first unification to succeed, e.g. with
``unify ... with ...``? Or is there a better tactic instead of `unify
<https://coq.inria.fr/refman/tactics.html#sec431>`__ for testing the
partial convertibility of ``2`` and ``(gs _)``? Feel free to use e.g.
type classes instead of canonical structures to make this work
|*)

(*|
Answer
******

Instance inference for canonical structures is dispatched on a term's
head. The numbers 1 and 2 have the same head (``S``), leading to
overlapping instances that break inference. (Indeed, Coq gives an
error message once you declare the second instance.)

One solution is to use separate definitions, since those change the
term's head:
|*)

Reset Initial. (* .none *)
Record Pn := sr {gs: nat}.
Definition one := 1.
Definition two := 2.
Canonical Structure Pn_1 := sr one.
Canonical Structure Pn_2 := sr two. (* Now the error message goes away *)

(*|
(There is even a `paper
<https://people.mpi-sws.org/~beta/lessadhoc/>`__ by Georges Gonthier
and collaborators showing how to program the inference mechanism in
this way.)

As for the ltac, it seems that ``unify`` type-checks its arguments
separately, which prevents canonical-structure inference from
triggering. We can fix this problem by putting two terms in a context
that forces the checker to unify them.
|*)

Ltac check_instance t :=
  let p := constr:(eq_refl : t = gs _) in idtac.

(*| Now these work: |*)

Check ltac:(tryif check_instance one then idtac "success"
             else idtac "fail").
Check ltac:(tryif check_instance two then idtac "success"
             else idtac "fail").

(*|
I suspect that with type classes you should be able to avoid the
inference problem, because it is not dispatched on the head of a term.

----

**Q:** "We can fix this problem by putting two terms in a context that
forces the checker to unify them." -- Do I understand correctly that
defining ``p`` is instrumental for creating the context?

**A:** I wouldn't say that defining ``p`` is the important bit by
itself, but calling into the type checker. Defining ``p`` is one way
of doing it, but there could be also be another tactic that
accomplishes that directly.
|*)
