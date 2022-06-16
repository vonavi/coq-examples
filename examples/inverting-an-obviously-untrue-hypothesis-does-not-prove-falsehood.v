(*|
#################################################################
Inverting an obviously untrue hypothesis does not prove falsehood
#################################################################

:Link: https://stackoverflow.com/q/27806859
|*)

(*|
Question
********

I am trying to prove a trivial lemma, which is a recreation of a
situation I found myself in at another point.
|*)

Lemma Sn_neq_n : forall n, S n <> n.

(*| The proof seems as simple as it gets: |*)

Proof.
  unfold not. intros.

(*| Now my goal state shows: |*)

  Show. (* .unfold .messages *)

(*|
Well it is obvious that ``S n`` can't be unified with ``n``, so I
should be able to just invert this hypothesis:
|*)

  inversion H.

(*| But instead of solving the goal, my state now shows: |*)

  Show. (* .unfold .messages *)

(*|
Huh? I'm just in an infinite loop now. I can ``inversion H0`` and I
just get an ``H1``, etc.

I was able to prove the lemma by induction:
|*)

  Restart. (* .none *)
  unfold not. intros. induction n.
  - inversion H.
  - inversion H. apply IHn. apply H1.

(*|
But that's a bit silly, because conceivably the unification algorithm,
which allows reflexive equality to make sense in the first place,
should not be able to unify ``S n`` with ``n``.

What's going on here?
|*)

(*|
Answer
******

To see why ``inversion`` isn't able to solve this goal on its own, we
need to understand what it is doing in more detail.

When you invert a hypothesis of (co)inductive type, what Coq does,
roughly speaking, is to extract as much information as it can from it
*using only pattern matching* (remember that Coq tactics are always
producing proof terms under the hood). Thus, when proving ``1 <> 0``
by inversion, Coq will produce a term that looks like this:
|*)

    Definition one_neq_zero (p : 1 = 0) : False :=
      match p in _ = n return match n with
                              | 0 => False
                              | _ => True
                              end
      with
      | eq_refl => I (* "I" is the only constructor of the True proposition *)
      end.

(*|
The ``return`` annotation on the ``match`` statement is crucial for
this to work. What is happening here is essentially the following:

- We need to match on the equality proof ``p`` to use it.
- In order to be able to talk about the right-hand side of that
  equation when pattern-matching on its proof, we must add a return
  annotation to our match.
- Unfortunately, this return annotation can't mention ``0`` directly.
  Instead, it needs to work for a *generic* ``n``, *even though we
  know that that element is actually* ``0``. This is just because of
  the way pattern matching works in Coq.
- On the return annotation, we play a "trick" on Coq: we say that we
  will return ``False`` on the case that we actually care about (i.e.,
  ``n = 0``), but say that we'll return something else on the other
  branches.
- To type-check the ``match``, each branch must return something of
  the type that appears on the ``return`` clause, but after
  substituting the *actual values* of the variables that were bound on
  the ``in`` clause.
- In our case, there is only one constructor for the equality type,
  ``eq_refl``. Here, we know that ``n = 1``. Substituting ``1`` for
  ``n`` in our return type, we obtain ``True``, so we must return
  something of type ``True``, which we do.
- Finally, since the right-hand side of ``p`` is ``0``, Coq
  understands that the type of the whole match is ``False``, so the
  whole definition type-checks.

The last step only works because ``0`` is a constructor, so Coq is
able to simplify the match on the return type to realize that we are
returning the right thing. *This* is what fails when trying to invert
``S n = n``: since ``n`` is a variable, the entire match can't be
simplified.

We could try to flip the equality and invert ``n = S n`` instead, so
that Coq would be able to simplify the return type a little bit.
Unfortunately, this wouldn't work either, and for a similar reason.
For instance, if you tried to annotate the match with ``in _ = m
return match m with 0 => True | _ => False end``, inside the
``eq_refl`` we would have to return something of type ``match n with 0
=> True | _ => False end``, which we can't.

Finally I should mention that the unification algorithm inside Coq
cannot be used "negatively" like you alluded to, because the theory
only defines the things that are *provable*, and not which things are
*refutable*. In particular, when we prove a negated proposition such
as ``S n <> n``, the type checker is always testing whether certain
unification problems have a solution, as opposed to testing whether
they have *no* solution. For instance, assuming that ``n = m`` is a
perfectly fine thing to do, and doesn't result in any contradictions,
even though ``n`` and ``m`` are *not* unifiable. Also notice that, if
``nat`` were declared as a *co-inductive* type instead, ``S n = n`` is
*not* a contradictory hypothesis, and the difference between the two
is just that on this case we wouldn't be able to do induction on
``n``.
|*)
