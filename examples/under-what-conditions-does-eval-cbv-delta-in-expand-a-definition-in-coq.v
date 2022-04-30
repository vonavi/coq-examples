(*|
############################################################################
Under what conditions does ``Eval cbv delta in`` expand a definition in Coq?
############################################################################

:Link: https://stackoverflow.com/q/45248213
|*)

(*|
Question
********

In Proof General (with Coq 8.5), I executed the following:
|*)

Require Import Arith.
Eval cbv delta in Nat.add_comm 3 7.

(*| The output is |*)

Eval cbv delta in Nat.add_comm 3 7. (* .unfold .messages *)

(*|
However, ``Print Nat.add_comm.`` gives a long and complicated function
taking two nats as input. I expected my code to expand the definition
of ``Nat.add_comm``, which is what ``Eval cbv delta in _.`` does in
similar situations. As a beginner, I know there is a naive
misconception lurking. What am I missing?

----

**A (Daniel Schepler):** Probably it's just that ``Nat.add_comm`` is
opaque - if you went through its proof (and the proofs of dependent
lemmas) and replaced ``Qed.`` with ``Defined.`` everywhere, it would
presumably evaluate to ``eq_refl``.
|*)

(*|
Answer
******

Expanding a bit on Daniel's comment, ``cbv delta`` will unfold an
identifier if

1. it has a body (i.e., is not a context variable, axiom, field in a
   module argument to the current module functor, bound variable,
   etc.), and
2. it's body was given transparently, i.e., either the proof script
   was closed with ``Defined`` rather than ``Qed`` or the body was
   given via ``:=`` or the automatic obligation tactic (for ``Program
   Definition``) or typeclass resolution (for ``Instance``\ s without
   a body), and
3. it has not been marked opaque via ``Opaque id`` or ``Strategy
   opaque [id]``, and
4. it was not created by "module-locking" another constant, i.e.,
   defined within a module (or module functor) with a module-type
   ascription via ``:`` rather than ``<:`` (exception: if the module
   type itself provides the body for the constant)

Note that, at present, ``vm_compute`` can get around 3 (and the
unification engine can too, but ``compute``, ``lazy``, ``cbv``,
``hnf``, ``cbn`` (usually), ``simpl`` (usually), and ``red`` cannot),
but nothing will get around the others.
|*)
