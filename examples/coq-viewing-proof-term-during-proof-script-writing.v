(*|
###################################################
Coq: viewing proof term during proof script writing
###################################################

:Link: https://stackoverflow.com/questions/48875967/coq-viewing-proof-term-during-proof-script-writing
|*)

(*|
Question
********

So, I've got a proof that looks like this:

.. code-block:: coq

    induction t; intros; inversion H; crush.

It solves all my goals, but when I do ``Qed``, I get the following
error:

    Cannot guess decreasing argument of fix.

So somewhere in the generated proof term, there's non-well-founded
recursion. The problem is, I have no idea where.

Is there a way to debug this kind of error, or to see the (possibly
non halting) proof term that the tactics script generates?
|*)

(*|
Answer (Tej Chajed)
*******************

You can use ``Show Proof.`` to view the proof term so far.

Another command that can help with seeing where the recursion went
wrong is ``Guarded.``, which runs the termination checker on the proof
term so far. You'll need to break apart the tactic script into
independent sentences to use it, though. Here's an example:
|*)

Fixpoint f (n : nat) : nat.
Proof.
  apply plus.
  - exact (f n).
  - Fail Guarded. (* .fails .unfold .no-goals *)
Fail Defined. (* .fails *)

(*|
----

**Q:** Does ``Guarded`` work when Coq cannot guess the decreasing
argument of fix?

**A:** It turns out when you define a ``Fixpoint`` in proof mode, Coq
always uses the last argument as the decreasing argument (and if it's
not inductive, the command just fails). Then ``Guarded`` ensures that
this argument is decreased. Note that you can always explicitly
provide a ``{struct n}`` annotation at definition time, though.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

You can use the ``Show Proof.`` command inside proof mode to print the
proof term produced so far.
|*)

(*|
Answer (Lily Chung)
*******************

In addition to the other excellent answers, I also want to point out
that using ``induction`` inside an interactive-mode ``Fixpoint`` is
usually a mistake, because you're recursing twice. Writing fixpoints
in interactive mode is often tricky because most automation tools will
happily make a recursive call at every possible opportunity, even when
it would be ill-founded.

I would advise to use ``Definition`` instead of ``Fixpoint`` and use
``induction`` in the proof script. This invokes the explicit recursor,
which allows for much better control of automation. The disadvantage
is decreased flexibility since fixpoints have fewer restrictions than
recursors - but as we've seen, that is both a blessing and a curse.

----

**A:** If you are very careful, using ``induction`` inside of a
``Fixpoint`` is a relatively easy way to prove things about functions
which contain nested fixpoints. You have to make sure to specialize
the fixpoint before running anything like ``auto``, though.

**A:** That's reasonable, though I would also consider abstracting the
necessary nested induction into its own scheme so that there's no need
to be so careful.
|*)
