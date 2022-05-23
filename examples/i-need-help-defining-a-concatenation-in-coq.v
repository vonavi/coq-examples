(*|
###########################################
I need help defining a concatenation in Coq
###########################################

:Link: https://stackoverflow.com/q/35947749
|*)

(*|
Question
********

I need to define a concatenation function, first some context, I
define the set "accepts"
|*)

Inductive accepts : Set :=
| True  : accepts
| fun_m : accepts -> accepts -> accepts
| n_fun : nat -> accepts -> accepts.

(*|
Then I need to be able to manipulate a very specific subset of
accepts: the first and last ones on the list, so True and n_fun only.
I do it with a mix of inductive and record like this:
|*)

Inductive n_sub : accepts -> Prop :=
| a1 : n_sub True
| a2 : forall (n : nat) (A : accepts), n_sub A -> n_sub (n_fun n A).

Record sub : Set := mk_s {A : accepts ; WS : n_sub A}.

(*|
As you might see this will give me strings of natural numbers followed
by ``True``, exclusively, so I want to deal with the subset of accepts
that yields ``n ... k True``. Consider I have two of this strings, I
want to define the function that sends ``ab... True`` and ``xy...
True`` into ``ab...xy... True``.
|*)

Fail Fixpoint concatenate (A0 A1 : accepts) (x : n_sub A0) (y : n_sub A1) : accepts
  := match x, y with
     | a1, q => B
     | a2 n A0 x, y => n_fun n (concatenate A0 A1)
     end. (* .fails *)

(*|
Clearly, this doesn't work... I have tried 100 variations of this:
using the accepts directly and sending the things to void, using the
record inside, mixing the accepts and the sub in different variations,
etc, etc... I'm just out of ideas and need someone to help me fix this
concatenate, please! Thank you in advance for your help!
|*)

(*|
Answer (jbapple)
****************

Sometimes it is helpful to write computable predicates, rather than
inductive ones (my ``ok``, below, vs. your ``n_sub``).
|*)

Reset Initial. (* .none *)
Inductive accepts :=
| valid : accepts
| fun_m : accepts -> accepts -> accepts
| n_fun : nat -> accepts -> accepts.

Fixpoint ok x :=
  match x with
  | valid => true
  | n_fun _ y => ok y
  | _ => false
  end.

(*|
Since ``ok`` is computable, you can use it for all sorts of things
later you might car about, but you can also use it in proofs (see
below).
|*)

Fixpoint concat x y :=
  match x with
  | valid => y
  | n_fun z zs => n_fun z (concat zs y)
  | _ => y
  end.

(*|
``concat`` punts on non-``ok`` input. Later, I'll show a more
strictly-typed version, ``concatLegit``.
|*)

Lemma concatOk : forall x y,
    ok x = true -> ok y = true -> ok (concat x y) = true.
Proof. induction x; auto. Qed.

Definition legit := { x : accepts & ok x = true }.

Definition concatLegit (x y : legit) : legit.
Proof.
  destruct x as [x p]. destruct y as [y q].
  exists (concat x y).
  apply concatOk; auto.
Defined.

Print concatLegit. (* .unfold *)

(*|
Answer (galas)
****************

The problem here is that you are trying to pattern-match on a thing
whose type lives in ``Prop`` to generate something of type ``accepts``
which lives in ``Set``. This is not allowed by Coq's type system. What
you have to do is pattern-match on the things of type ``accepts`` and
then use the properties to dismiss the impossible cases.

Here I'll use the interactive mode. This allows me to only define the
part of the computation I am interested in using ``refine`` and
leaving blank (using ``_``) the parts I will deal with later on.

Because some irrelevant branches might appear when inspecting ``A0``,
I need to generalise the return type: instead of building an
``accepts``, I'll build a proof that ``n_sub a -> accepts`` where
``a`` is whatever ``A0`` was matched to.

.. coq:: none
|*)

Reset Initial.

Inductive accepts : Set :=
| True  : accepts
| fun_m : accepts -> accepts -> accepts
| n_fun : nat -> accepts -> accepts.

Inductive n_sub : accepts -> Prop :=
| a1 : n_sub True
| a2 : forall (n : nat) (A : accepts), n_sub A -> n_sub (n_fun n A).

(*||*)

Fixpoint concatenate (A0 A1 : accepts) (x : n_sub A0) (y : n_sub A1) : accepts.
Proof.
  refine
    ((match A0 as a return n_sub a -> accepts with
      | True        => fun _      => A1
      | n_fun n A0' => fun Hn_fun => n_fun n (concatenate A0' A1 _ y)
      | _           => _
      end) x).

(*|
I now am left with two proofs: I need to define the case I left empty
but that is rather easy: the assumption ``n_sub (fun_m a a0)`` is
contradictory! I can prove ``False`` by inverting it:
|*)

  - intro Hf. apply False_rec. inversion Hf.

(*|
Now, I have to prove that ``n_sub A0'`` holds given the assumption
``Hn_fun`` that ``n_sub (n_fun n A0')`` holds true. Once more
``inversion`` will do the trick:
|*)

  - inversion Hn_fun. assumption.

(*|
And that's it! The tricky part here is to identify the hypothesis that
needs to be generalised and use the appropriate ``as ... return ...``
in the `dependent pattern-matching
<https://coq.inria.fr/refman/Reference-Manual020.html#sec644>`__. The
rest is made quite convenient by the use of the interactive mode and
the help of ``refine`` to build incomplete proof terms.
|*)
