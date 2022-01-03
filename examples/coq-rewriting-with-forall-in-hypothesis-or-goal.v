(*|
####################################################
Coq: Rewriting with ``forall`` in hypothesis or goal
####################################################

:Link: https://stackoverflow.com/q/52602536
|*)

(*|
Question
********

I have proved 'correctness' of the reverse function on polymorphic
``Lists`` in Coq. The following proof works just fine, but I have a
few questions about how the ``rewrite`` tactic works.

Here's the code:
|*)

Require Export Coq.Lists.List.
Import ListNotations.

Fixpoint rev {T : Type} (l : list T) : list T :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

(* Prove rev_acc equal to above naive implementation. *)
Fixpoint rev_acc {T : Type} (l acc : list T) : list T :=
  match l with
  | nil => acc
  | h :: t => rev_acc t (h::acc)
  end.

Theorem app_assoc : forall  (T : Type) (l1 l2 l3 : list T),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
Admitted.

Theorem rev_acc_correct : forall (T : Type) (l k : list T),
    rev l ++ k = rev_acc l k.
Proof.
  intros T l. induction l as [ | h l' IHl' ].
  - reflexivity.
  - simpl. intro k.
    (* Why is "intro k" required for "rewrite -> app_assoc" but
       "rewrite -> IHl'" works regardless of "intro k". generalize
       (rev l'), [h], k. *)
    rewrite -> app_assoc. simpl.
    rewrite -> IHl'. reflexivity.

(*|
In the inductive step of the proof for ``rev_acc_correct`` if I skip
``intro k``, then rewriting with ``app_assoc`` complains that it
cannot find a matching subterm.
|*)

    Undo 5. (* .none *)
    Fail rewrite -> app_assoc. (* .fails .unfold .messages *)

(*|
Here, I presume that the ``?`` before the placeholder names denote
that the terms are constrained, in this case to be of type ``List T``
for some type ``T``; and since ``rev l'`` and ``[h]`` in the goal are
instances of ``List T``, one would expect a match in the goal.

On the other hand, rewriting with inductive hypothesis (``rewrite ->
IHl'``) instead of ``app_assoc`` goes through without needing an
``intro k`` before.

I find this behaviour of ``rewrite`` a bit confusing and the Coq
manual doesn't provide any details. I don't want to have to read
through the implementation but I need a good operational understanding
of what the rewrite tactic does, especially with regards to how term
matching works. Any answers/references in this direction are highly
appreciated.
|*)

(*|
Answer
******

The complication with this rewrite is that there's a *binder* (the
``forall k``), which can complicate things. If you just want things to
work, use ``setoid_rewrite`` instead of ``rewrite`` and it will
rewrite under binders.

- ``rewrite IHl'`` looks like it happens under a binder, but the
  pattern being re-written doesn't actually involve the bound
  variable, so the binder isn't actually important. Here's what I
  mean: the goal is

  .. code-block:: coq

      forall k : list T, (rev l' ++ [h]) ++ k = rev_acc l' (h :: k)

  which is the same thing as (that is, equal to):

  .. code-block:: coq

      (fun l : list T => forall k : list T,
           l ++ k = rev_acc l' (h :: k)) (rev l' ++ [h])

  which I got using ``pattern (rev l' ++ [h])`` in Ltac. Now it's
  clear that you can just rewrite the part being applied to and ignore
  the binder. When you do ``rewrite IHl'`` Coq easily figures out that
  ``IHl`` should be specialized to ``[h]`` and the rewrite proceeds.

- ``rewrite app_assoc``, on the other hand, needs to be specialized to
  three lists, specifically ``rev l'``, ``[h]``, and ``k``. It can't
  be specialized in the current context because the variable ``k`` is
  only bound underneath the ``forall``. This is why the pattern ``(?x
  ++ ?y) ++ ?z`` doesn't appear in the goal.

So what do you actually do? You can of course introduce ``k`` so there
is no binder, but there's a simpler and more general technique: Coq
has generalized rewriting that can rewrite under binders, which you
can use by instead calling ``setoid_rewrite`` (see `Rewriting under
binders
<https://coq.inria.fr/refman/addendum/generalized-rewriting.html#extensions>`__
in the Coq reference manual). The manual tells you you need to declare
morphisms, but the relevant ones have all been implemented for you in
this case for ``forall``, so ``setoid_rewrite app_assoc`` will just
work.

Note that while you can always introduce a ``forall`` to get rid of
the binder, ``setoid_rewrite`` can be really handy when your goal is
an ``exists``. Rather than using ``eexists`` you can just rewrite
under the binder.
|*)
