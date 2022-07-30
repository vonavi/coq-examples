(*|
##############################################################
Proving uniqueness of an instance of an indexed inductive type
##############################################################

:Link: https://proofassistants.stackexchange.com/q/1246
|*)

(*|
Question
********

Consider the simple indexed inductive type
|*)

Inductive Single : nat -> Set :=
| single_O : Single O
| single_S {n} : Single n -> Single (S n).

(*|
Intuitively, I thought that ``Single n`` has a unique value for each
``n : nat``. I started by trying to prove that ``forall s : Single O,
s = single_O``. However, the usual tactics ``inversion``,
``destruct``, and ``induction`` did not work:
|*)

Lemma single_O_unique (s : Single O) : s = single_O.
  inversion s. (* No effect *)
  Fail destruct s.
  Fail induction s.

(*| The error messages were: |*)

  Fail destruct s. (* .unfold .messages *)

(*| So I resorted to a manual ``match`` expression: |*)

  refine match s with
         | single_O => _
         | single_S _ => _
         end.

(*| Resulting in the following proof context: |*)

  Show. (* .unfold .messages *)

(*| which was puzzling, but easy to prove: |*)

  - reflexivity.
  - exact idProp.
Qed.

(*|
Questions:

- Why was ``inversion`` unable to recognize that ``s`` could only be
  ``single_O`` and substitute accordingly?
- Why did the ``refine`` tactic produce the subgoal ``IDProp``?
- Is there a way to get ``inversion`` or ``destruct`` to work in this
  case? Or, what would a better way to prove ``s = single_O``?

Full example:
|*)

Reset Initial. (* .none *)
Inductive Single : nat -> Set :=
| single_O : Single O
| single_S {n} : Single n -> Single (S n).

Lemma single_O_unique (s : Single O) : s = single_O.
  inversion s.  (* No effect *)
  Fail destruct s.
  Fail induction s.
  refine match s with
         | single_O => _
         | single_S _ => _
         end.
  - reflexivity.
  - exact idProp.
Qed.

(*|
Answer (gallais)
****************

    Or, what would a better way to prove ``s = single_O``?

I would define a function that, given a nat ``n``, computes the
canonical proof ``Single n``.
|*)

Reset single_O_unique. (* .none *)
Fixpoint Canonical (n : nat) : Single n :=
  match n with
  | O => single_O
  | S n => single_S (Canonical n)
  end.

(*|
You can then easily prove that any ``Single n`` proof is equal to the
canonical one by induction. Here the abstraction won't fail because
the equality is already generic over ``n``.
|*)

Lemma single_canonical (n : nat) (s : Single n) : s = Canonical n.
Proof.
  induction s.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

(*| Your original lemma is then a direct corollary. |*)

Lemma single_O_unique (s : Single O) : s = single_O.
  apply single_canonical with (n := O).
Qed.

(*|
Answer (Meven Lennon-Bertrand)
******************************

Regarding ``IDProp``, this is the pattern-matching compilation of Coq
at work. Basically, because you scrutinee has a type that can only
correspond to the ``single_O`` branch, Coq was smart enough to craft a
return predicate that gave you an interesting goal only in that
branch, the other being replaced by the trivially inhabited ``IDProp``
(as you noticed in your proof). So ``match`` was smart enough "to
recognize that ``s`` could only be ``single_O``". If you wish to see
what exactly happened, you can use the ``Show Proof.`` command.

I'm a bit suprised that ``destruct``, ``inversion`` and friends, which
are supposed to be built on top of pattern-matching, were not able to
succeed where the simpler ``refine (match …)`` was. In such cases with
complex dependencies, ``dependent inversion`` works better than
``inversion``, but it still fails here, sadly.

If you wish to have ``inversion`` work here, you'd have to replace
``single_O`` by something generic enough. Using gallais' solution, you
can do
|*)

Reset Canonical. (* .none *)
Fixpoint Canonical (n : nat) : Single n :=
  match n with
  | O => single_O
  | S n => single_S (Canonical n)
  end.

Lemma single_O_can (s : Single 0) : s = single_O.
Proof.
  change single_O with (Canonical 0).
  dependent inversion s.
  reflexivity.
Qed.

(*|
Now ``dependent inversion`` succeeds because ``Canonical 0`` can
successfully be abstracted over ``0``, while ``single_O`` could not.
|*)
