(*|
################################################
Shorter notation for matching hypotheses in Coq?
################################################

:Link: https://stackoverflow.com/questions/55992567/shorter-notation-for-matching-hypotheses-in-coq
|*)

(*|
Question
********

I find myself often wanting to refer to hypotheses by their type
rather than by their name; especially in proofs with inversions on
semantic rules, i.e., rules with several cases each of which may have
multiple antecedents.

I know how to do this with ``match goal with ...``, as in the
following trivial example.
|*)

Lemma l0:
  forall P1 P2, P1 \/ (P1 = P2) -> P2 -> P1.
Proof.
  intros.
  match goal with H:_ \/ _ |- _ => destruct H as [H1|H2] end.
  assumption.
  match goal with H: _ = _ |- _ => rewrite H end.
  assumption.
Qed.
Reset l0. (* .none *)

(*|
*Is there a more concise way? Or a better approach?*

(Introduction patterns, like ``intros [???? HA HB|??? HA|????? HA HB
HC HD]``, are not an option—I am tired of finding the right number of
``?``'s!)

For instance, is it possible to write a ``grab`` tactic to combine a
pattern and a tactic, as in

.. code-block:: coq

    grab [H:P1 \/ _] => rename H into HH.
    grab [H:P1 \/ _] => destruct H into [H1|H2].

    grab [P1 \/ _] => rename it into HH.
    grab [P1 \/ _] => destruct it into [H1|H2].

From my understanding of `Tactic Notations
<https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#tactic-notations>`__,
it is not possible to have a cpattern as an argument, but maybe there
is another way?

Ideally, I would like to be able to use an hypothesis pattern instead
of an identifier in any tactic as in Isabelle:

.. code-block:: coq

    rename ⟨P1 \/ _⟩ into HH.
    destruct ⟨P1 \/ _⟩ as [H1|H2].
    rewrite ⟨P1 = _⟩.

But I imagine this to be quite an invasive change.
|*)

(*|
Answer
******

You can iterate over all the assumptions until you find a matching
one:
|*)

Tactic Notation "summon" uconstr(ty) "as" ident(id) :=
  match goal with H : _ |- _ => pose (id := H : ty) end.

(*|
The trick is that you take the type to be found not as a pattern, but,
well, as a type :). Specifically, if you issue something like ``summon
(P _) as id``, then Coq will take the ``_`` as an unsolved existential
variable. In turn, each assumption will be typechecked against ``P
_``, trying to instantiate that hole along the way. When one succeeds,
the ``pose`` names it ``id``. The iteration arises because ``match
goal`` will keep retrying with different matches until something
sticks or everything fails.

You can define a form without ``as`` that just names the found thing
``it`` (while kicking anything else out):
|*)

Tactic Notation "summon" uconstr(ty) :=
  let new_it := fresh "it"
  in try (rename it into new_it); summon ty as it.

(*| Ta-da! |*)

Lemma l0 : forall P1 P2, P1 \/ (P1 = P2) -> P2 -> P1.
Proof.
  intros.
  summon (_ \/ _). destruct it.
  - assumption.
  - summon (_ = _). rewrite it. assumption.
Qed.
Reset l0. (* .none *)

(*|
You can also get your ``=>`` syntax. I don't think it's terribly
useful, but...
|*)

(* assumption of type ty is summoned into id for the duration of tac
   anything that used to be called id is saved and restored
   afterwards, if possible. *)
Tactic Notation "summon" uconstr(ty) "as" ident(id) "=>" tactic(tac) :=
  let saved_id := fresh id
  in try (rename id into saved_id);
     summon ty as id; tac;
     try (rename saved_id into id).

Lemma l0 : forall P1 P2, P1 \/ (P1 = P2) -> P2 -> P1.
Proof.
  intros.
  summon (_ \/ _) as H => destruct H.
  - assumption.
  - summon (_ = _) as H => rewrite H. assumption.
Qed.
Reset l0. (* .none *)

(*|
Old answer
==========

(You may want to read this, because the above solution is really a
variant of this one, and there's more explanation here.)

You can summon an assumption matching a type pattern into a name with
``eassert (name : ty) by eassumption.``.
|*)

Lemma l0 : forall P1 P2, P1 \/ (P1 = P2) -> P2 -> P1.
Proof.
  intros.
  eassert (HH : _ \/ _) by eassumption. destruct HH.
  - assumption.
  - eassert (HH : _ = _) by eassumption. rewrite HH. assumption.
Qed.
Reset l0. (* .none *)

(*|
Why is this an improvement? Because the ``_ \/ _`` and ``_ = _`` are
now full types, not just patterns. They just contain unsolved
existential variables. Between ``eassert`` and ``eassumption``, these
variables get solved at the same time the matching assumption is
located. Tactic notations can definitely work with types (i.e. terms).
Sadly, there appears to be a bit of a mishap in the parsing rules.
Specifically, the tactic notation needs an untyped term (so we don't
try and fail to resolve the variables too early), so we need
``uconstr``, but `there's no luconstr
<https://sympa.inria.fr/sympa/arc/coq-club/2015-10/msg00054.html>`__,
meaning we're forced to add extraneous parentheses. To avoid
bracket-mania, I've reworked the syntax of your ``grab``. I'm also not
entirely sure if your ``=>`` syntax makes much sense, because why not
just bring the name into scope for good, instead of only on the
``=>``, as you seem to imply?
|*)

Tactic Notation "summon" uconstr(ty) "as" ident(id) :=
  eassert (id : ty) by eassumption.

Lemma l0 : forall P1 P2, P1 \/ (P1 = P2) -> P2 -> P1.
Proof.
  intros.
  summon (_ \/ _) as HH. destruct HH.
  - assumption.
  - summon (_ = _) as HH. rewrite HH. assumption.
Qed.
Reset l0. (* .none *)

(*|
You can make ``summon``-sans-``as`` name the found assumption ``it``,
while booting anything else under that name out.
|*)

Tactic Notation "summon" uconstr(ty) "as" ident(id) :=
  eassert (id : ty) by eassumption.

Tactic Notation "summon" uconstr(ty) :=
  let new_it := fresh "it"
  in (try (rename it into new_it); summon ty as it).

Lemma l0 : forall P1 P2, P1 \/ (P1 = P2) -> P2 -> P1.
Proof.
  intros.
  (* This example is actually a bad demonstration of the name-forcing
     behavior because destruct-ion, well, destroys. Save the summoned
     proof under the name it, but destroy it from another, then
     observe the way the second summon shoves the original it into
     it0. *)
  summon (_ \/ _) as prf. pose (it := prf). destruct prf.
  - assumption.
  - summon (_ = _). rewrite it. assumption.
Qed.
Reset l0. (* .none *)

(*| Idiomatically, that would really just be |*)

Lemma l0 : forall P1 P2, P1 \/ (P1 = P2) -> P2 -> P1.
Proof.
  intros.
  summon (_ \/ _). destruct it.
  - assumption.
  - summon (_ = _). rewrite it. assumption.
Qed.

(*|
I believe that you could go and create a bunch of specialized ``Tactic
Notations`` to replace the ``ident`` arguments in ``destruct``,
``rewrite``, etc. with these holey-type ``uconstrs``, if you really
wanted to. Indeed, ``summon _ as _`` is almost your modified ``rename
_ into _``.

Another caveat: ``assert`` is opaque; the definitions generated by
``summon`` look like new assumptions that don't reveal that they are
equal to one of the old ones. Something like ``refine (let it := _ in
_)`` or ``pose`` should be used to rectify this, but my Ltac-fu is not
strong enough to do this. See also: this issue advocating for a
literal `transparent assert
<https://github.com/coq/coq/issues/3551>`__.

(The new answer solves this caveat.)
|*)
