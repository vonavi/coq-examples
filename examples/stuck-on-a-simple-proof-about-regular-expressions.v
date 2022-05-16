(*|
#################################################
Stuck on a simple proof about regular expressions
#################################################

:Link: https://stackoverflow.com/q/40796214
|*)

(*|
Question
********

I'm trying to formalize some properties on regular expressions (REs)
using Coq. But, I've got some troubles to prove a rather simple
property:

    For all strings ``s``, if ``s`` is in the language of
    ``(epsilon)*`` RE, then ``s = ""``, where ``epsilon`` and ``*``
    denotes the empty string RE and Kleene star operation.

This seems to be an obvious application of induction / inversion
tactics, but I couldn't make it work.

The minimal working code with the problematic lemma is in the
following `gist
<https://gist.github.com/rodrigogribeiro/e8f6bde70b54c871f8c744a9b3570bb2>`__.
Any tip on how should I proceed will be appreciated.

**EDIT**: One of my tries was something like:

.. coq:: none
|*)

Set Implicit Arguments.

Require Import Ascii String.

Inductive regex : Set :=
| Emp : regex
| Eps : regex
| Chr : ascii -> regex
| Cat : regex -> regex -> regex
| Choice : regex -> regex -> regex
| Star : regex -> regex.

Open Scope string_scope.

Notation "'#0'" := Emp.
Notation "'#1'" := Eps.
Notation "'$' c" := (Chr c) (at level 40).
Notation "e '@' e1" := (Cat e e1) (at level 15, left associativity).
Notation "e ':+:' e1" := (Choice e e1) (at level 20, left associativity).
Notation "e '^*'" := (Star e) (at level 40).

(** Semantics of regular expressions *)

Reserved Notation "s '<<-' e" (at level 40).

Inductive in_regex : string -> regex -> Prop :=
| InEps : "" <<- #1
| InChr : forall c, (String c EmptyString) <<- ($ c)
| InCat : forall e e' s s' s1,
    s <<- e -> s' <<- e' -> s1 = s ++ s' -> s1 <<- (e @ e')
| InLeft : forall s e e', s <<- e -> s <<- (e :+: e')
| InRight : forall s' e e',  s' <<- e' -> s' <<- (e :+: e')
| InStar : forall s e, s <<- (#1 :+: (e @ (e ^*))) -> s <<- (e ^*)
where "s '<<-' e" := (in_regex s e).

Hint Constructors in_regex.

(*||*)

Lemma star_lemma : forall s, s <<- (#1 ^*) -> s = "".
Proof.
  intros s H. inversion_clear H. inversion_clear H0.
  - now inversion_clear H.
  - inversion_clear H.
    inversion_clear H2. clear s.
    inversion_clear H0. clear s0.
    simpl.

(*| that leave me with the following goal: |*)

    Show. (* .unfold .messages *)

(*|
At least to me, it appears that using induction would finish the
proof, since I could use ``H1`` in induction hypothesis to finish the
proof, but when I start the proof using
|*)

    Restart. (* .none *) intros s H. (* .none *)
    induction H.

(*| instead of |*)

    Restart. (* .none *) intros s H. (* .none *)
    inversion_clear H.
Abort. (* .none *)

(*|
I got some (at least for me) senseless goals. In Idris / Agda, such
proof just follows by pattern matching and recursion over the
structure of ``s <<- (#1 ^*\ )``. My point is how to do such recursion
in Coq.
|*)

(*|
Answer (Anton Trunov)
*********************

Here is one possible solution of the original problem:
|*)

Lemma star_lemma : forall s, s <<- (#1 ^*) -> s = "".
Proof.
  refine (fix star_lemma s prf {struct prf} : s = "" := _).
  inversion_clear prf; subst.
  inversion_clear H; subst.
  - now inversion H0.
  - inversion_clear H0; subst. inversion_clear H; subst.
    rewrite (star_lemma s' H1).
    reflexivity.
Qed.

(*|
The main idea is to introduce a term in the context which will
resemble the recursive call in a typical Idris proof. The approaches
with ``remember`` and ``dependent induction`` don't work well (without
modifications of ``in_regex``) because they introduce impossible to
satisfy equations as induction hypotheses' premises.

*Note*: it can take a while to check this lemma (around 40 seconds on
my machine under Coq 8.5pl3). I think it's due to the fact that the
``inversion`` tactic tends to generate big proof terms.

----

**A:** Nice! I really don't see how to prove it without using an
hand-crafted fixpoint. Following your example, `I factored the proof
<https://gist.github.com/gallais/58b42d5d9571ff0e6a432a9f40cf06c9>`__
through a ``star_unfold`` lemma which says that if ``s <<- (e ^*\ )``
then ``exists n, s <<- ntimes n e``. In the case of a full-blown
library, this should isolate the expensive check to ``star_unfold``
alone given that later proofs can simply use induction on a natural
number.

**A:** Very good point! Please consider making your comment into an
answer -- I hear comments are not very reliable on SO. You could've
also used ``Nat.iter`` instead of ``ntimes`` to make the code shorter:
``exists n, s <<- Nat.iter n (Cat e) #1.`` (But maybe it hurts
readability a bit).
|*)

(*|
Answer (eponier)
****************

This problem has obsessed me for a week, and I have finally found a
solution that I find elegant.

I had already read that when an induction principle does not fit your
needs, you can write and prove another one, more adapted to your
problem. That is what I have done in this case. What we would want is
the one obtained when using the more natural definition given in `this
answer <https://stackoverflow.com/a/40806050/5153939>`__. By doing
this, we can keep the same definition (if changing it implies too many
changes, for example) and reason about it more easily.

Here is the proof of the induction principle (I use a section to
specify precisely the implicit arguments, since otherwise I observe
strange behaviours with them, but the section mechanism is not
necessary at all here).
|*)

Reset star_lemma. (* .none *)
Section induction_principle.

Context (P : string -> regex -> Prop)
  (H_InEps : P "" #1)
  (H_InChr : forall c, P (String c "") ($ c))
  (H_InCat : forall {e e' s s' s1}, s <<- e -> P s e -> s' <<- e' ->
    P s' e' -> s1 = s ++ s' -> P s1 (e @ e'))
  (H_InLeft : forall {s e e'}, s <<- e -> P s e -> P s (e :+: e'))
  (H_InRight : forall {s' e e'}, s' <<- e' -> P s' e' -> P s' (e :+: e'))
  (H_InStar_Eps : forall e, P "" (e ^*))
  (H_InStar_Cat : forall {s1 s2 e}, s1 <<- e -> s2 <<- (e ^*) ->
    P s1 e -> P s2 (e ^*) -> P (s1 ++ s2) (e ^*)).

Arguments H_InCat {_ _ _ _ _} _ _ _ _ _.
Arguments H_InLeft {_ _ _} _ _.
Arguments H_InRight {_ _ _} _ _.
Arguments H_InStar_Cat {_ _ _} _ _ _ _.

Definition in_regex_ind2 : forall (s : string) (r : regex), s <<- r -> P s r.
Proof
  using H_InCat H_InChr H_InEps H_InLeft H_InRight H_InStar_Cat H_InStar_Eps.
  refine (fix in_regex_ind2 {s r} prf {struct prf} : P s r :=
    match prf with
    | InEps => H_InEps
    | InChr c => H_InChr c
    | InCat prf1 prf2 eq1 =>
        H_InCat prf1 (in_regex_ind2 prf1) prf2 (in_regex_ind2 prf2) eq1
    | InLeft _ prf => H_InLeft prf (in_regex_ind2 prf)
    | InRight _ prf => H_InRight prf (in_regex_ind2 prf)
    | InStar prf => _
    end).
  inversion prf; subst.
  - inversion H1. apply H_InStar_Eps.
  - inversion H1; subst.
    apply H_InStar_Cat; try assumption; apply in_regex_ind2; assumption.
Qed.

End induction_principle.

(*|
And it turned out that the ``Qed`` of this proof was not instantaneous
(probably due to ``inversion`` producing large terms as in `this
answer <https://stackoverflow.com/a/40807209/5153939>`__), but took
less than 1s (maybe because the lemma is more abstract).

The ``star_lemma`` becomes nearly trivial to prove (as soon as we know
the ``remember`` trick), as with the natural definition.
|*)

Lemma star_lemma : forall s, s <<- (#1 ^*) -> s = "".
Proof.
  intros s H. remember (#1 ^*) as r.
  induction H using in_regex_ind2; try discriminate.
  - reflexivity.
  - inversion Heqr; subst.
    inversion H. rewrite IHin_regex2 by reflexivity. reflexivity.
Qed.

(*|
Answer (Zimm i48)
*****************

I modified a bit the definition of your in_regex predicate:
|*)

Reset in_regex. (* .none *)
Inductive in_regex : string -> regex -> Prop :=
| InEps : "" <<- #1
| InChr : forall c, (String c EmptyString) <<- ($ c)
| InCat : forall e e' s s' s1,
    s <<- e -> s' <<- e' -> s1 = s ++ s' -> s1 <<- (e @ e')
| InLeft : forall s e e', s <<- e -> s <<- (e :+: e')
| InRight : forall s' e e',  s' <<- e' -> s' <<- (e :+: e')
| InStarLeft : forall e, "" <<- (e ^*)
| InStarRight : forall s s' e, s <<- e -> s' <<- (e ^*) -> (s ++ s') <<- (e ^*)
where "s '<<-' e" := (in_regex s e).

(*| and could prove your lemma: |*)

Lemma star_lemma : forall s, s <<- (#1 ^*) -> s = "".
Proof.
  intros s H.
  remember (#1 ^*) as r.
  induction H; inversion Heqr; clear Heqr; trivial.
  subst e.
  rewrite IHin_regex2; trivial.
  inversion H; trivial.
Qed.

(*|
Some explanations are necessary.

1. I did an induction on ``H``. The reasoning is: if I have a proof of
   ``s <<- (#1 ^*\ )`` then this proof must have the following form...
2. The tactic `remember
   <https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.remember>`__
   create a new hypothesis ``Heqr`` which, combined with `inversion
   <https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.inversion>`__
   will help get rid of cases which cannot possibly give this proof
   (in fact all the cases minus the ones where ``^*`` is in the
   conclusion).
3. Unfortunately, this path of reasoning does not work with the
   definition you had for the ``in_regex`` predicate because it will
   create an unsatisfiable condition to the induction hypothesis.
   That's why I modified your inductive predicate as well.
4. The modified inductive tries to give a more basic definition of
   being in ``(e ^*\ )``. Semantically, I think this is equivalent.

I would be interested to read a proof on the original problem.

----

**A:** The proof of the original problem is `here
<http://stackoverflow.com/a/40807209/2747511>`__ :).
|*)
