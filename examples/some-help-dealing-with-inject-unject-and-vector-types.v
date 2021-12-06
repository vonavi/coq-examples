(*|
#####################################################
Some help dealing with inject/unject and vector types
#####################################################

:Link: https://stackoverflow.com/questions/63017478/some-help-dealing-with-inject-unject-and-vector-types
|*)

(*|
Question
********

I'm reading through CPDT while doing the readings and exercises from
Pierce's course here:
https://www.cis.upenn.edu/~bcpierce/courses/670Fall12/

This question relates to HW10 here:
https://www.cis.upenn.edu/~bcpierce/courses/670Fall12/HW10.v

Here's the code up to my question
|*)

Require Import Arith Bool List.

Set Implicit Arguments.

(* Length-Indexed Lists *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Definition ilength n (l : ilist n) := n.

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2))
    with
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Fixpoint inject (ls : list A) : ilist (length ls) :=
    match ls with
      | nil => Nil
      | h :: t => Cons h (inject t)
    end.

  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
      | Nil => nil
      | Cons h t => h :: unject t
    end.

  Theorem inject_inverse : forall ls, unject (inject ls) = ls.
    induction ls. Admitted.

(*|
Because I really want to better understand dependent types and how to
use proofs in programs, I decided to try to do the latter. Here is
what I have so far.
|*)

  Definition ilists_sizechange (n1 n2 : nat) (l1 : ilist n1) (P : n1=n2) :
    ilist n2.
  Proof.
    subst. assumption.
  Defined.

  Lemma ilists_size_equal : forall n (ls : ilist n), n = length (unject ls).
  Proof.
    intros. induction ls. reflexivity. simpl. auto.
  Qed.

  Theorem unject_inject_thehardway : forall n (ls : ilist n),
      inject (unject ls) = ilists_sizechange ls (ilists_size_equal ls).
  Proof.
    intros. induction ls. simpl.
    (* ????????????????? *)

(*|
When I get to "?????????????????" that's where I'm stuck. I have a
target like
|*)

    Show 1. (* .unfold .messages *)
  Admitted. (* .none *)

(*|
and I'm not really sure what I can do here.

I tried writing ``ilists_sizechange`` as a more direct function, but
failed to do so. Not sure how to massage the type checking.

I guess I'm curious first if this approach is fruitful, or if I'm
making some fundamental mistake. I'm also curious what the most
concise way of expressing ``inject (unject ls) = ilists_sizechange ls
(ilists_size_equal ls).`` is...here there are two custom functions
(the sizechange and the proof of equality), and one imagines it should
be possible with just one.

Coq is great but the syntax around dependently types stuff can be
tricky. I appreciate any help!

Edit: I realize that an inductive type or something expressing
equality of two lists and then building up and showing the sizes are
equal is probably easier (eg the first suggestion they have), but I
want to understand this case because I can imagine running into these
sorts of issues in the future and I want to know how to work around
them.

Edit2: I was able to make it past the Nil case using the following

.. code-block:: coq

    dep_destruct (ilists_size_equal Nil).
    compute.
    reflexivity.

But then get stuck on the Cons case...I will try to prove some
theorems and see if I can't get there, but I think I'm still missing
something conceptual here.
|*)

(*|
Answer
******

Although functions may depend on proof objects, one approach (I'm
going to show below) is to define the functions so that they don't use
the proof objects except to construct other proof objects and to
eliminate absurd cases, ensuring that opaque proofs never block
computation. Another approach is to fully embrace dependently typed
programming and the unification of "proofs as programs", but that's a
much bigger paradigm shift to explain, so I'm not going to do that.

Starting with ``ilists_sizechange``, we now care about the shape of
the term constructed by tactics, so not all tactics are allowed. Not
wanting to use the equality proof rules out the tactic ``subst``.
Instead we can recurse (``induction``) on the list ``l1`` and
pattern-match (``destruct``) on the natural number ``n2``; there are
four cases:

- two absurd ones, which can be eliminated by using the equality
  (``discriminate``)
- the ``0 = 0`` case, where you can just construct the empty list
- the ``S m1 = S m2`` case, where you can construct ``Cons``, use the
  induction hypothesis (i.e., recursive call), and then you are asked
  for a proof of ``m1 = m2``, which is where you can fall back to
  regular reasoning without caring what the proof term looks like.

.. coq::
|*)

  Reset ilists_sizechange. (* .none *)
  Definition ilists_sizechange (n1 n2 : nat) (l1 : ilist n1) (P: n1=n2) :
    ilist n2.
  Proof.
    revert n2 P. (* Generalize the induction hypothesis. *)
    induction l1; destruct n2; discriminate + constructor; auto.
  Defined.

(*|
While the rest of the proof below would technically work with that
definition, it is still not ideal because any computation would unfold
``ilist_sizechange`` into an ugly function. While we've been careful
to give that function the "right" computational behavior, tactic-based
programming tends to be sloppy about some finer details of the syntax
of those functions, which makes later proofs where they appear hard to
read.

To have it look nicer in proofs, one way is to define a ``Fixpoint``
with the ``refine`` tactic. You write down the body of the function in
Gallina, and put underscores for the proof terms, which become
obligations that you have to prove separately. ``refine`` is not the
only way to perform this technique, there's also the ``Program
Fixpoint`` command and the Equations plugin. I would recommend looking
into Equations. I stick with ``refine`` out of familiarity.

As you can see, intuitively all this function does is deconstruct the
list ``l1``, indexed by ``n1``, and reconstruct it with index ``n2``.
|*)

  Reset ilists_sizechange. (* .none *)
  Fixpoint ilists_sizechange (n1 n2 : nat) (l1 : ilist n1) {struct l1} :
    n1 = n2 -> ilist n2.
  Proof.
    refine (
        match l1, n2 with
        | Nil, 0 => fun _ => Nil
        | Cons x xs, S n2' => fun EQ => Cons x (ilists_sizechange _ _ xs _)
        | _, _ => fun _ => _
        end
      ); try discriminate.
    auto.
  Defined.

(*| The proof of ``ilists_size_equal`` needs no modification. |*)

  Lemma ilists_size_equal : forall n (ls : ilist n), n = length (unject ls).
  Proof.
    intros. induction ls. reflexivity. simpl. auto.
  Qed.

(*|
For the final proof, there is one more step: first generalize the
equality proof. The idea is that ``ilists_sizechange`` doesn't
actually look at it, but when it makes a recursive call it will need
to construct some other proof, and this generalization allows you to
use the induction hypothesis independently of that particular proof.
|*)

  Theorem unject_inject_ :
    forall n (ls : ilist n) (EQ : n = length (unject ls)),
      inject (unject ls) = ilists_sizechange ls EQ.
  Proof.
    intros n ls; induction ls; cbn.
    - reflexivity.
    - intros EQ. f_equal. apply IHls.
      (* Here we have ilists_sizechange applied to some big proof
         object, which we can ignore because the induction hypothesis
         generalizes over all such proof objects *)
  Qed.

(*|
Then you want to specialize that theorem to use a concrete proof,
ensuring that such a proof exists so the theorem is not vacuous.
|*)

  Theorem unject_inject : forall n (ls : ilist n),
      inject (unject ls) = ilists_sizechange ls (ilists_size_equal _).
  Proof.
    intros; apply unject_inject_.
  Qed.

End ilist.
