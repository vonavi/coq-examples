(*|
###########################################################################
Coq can't compute a well-founded function on ``Z``, but it works on ``nat``
###########################################################################

:Link: https://stackoverflow.com/q/44186751
|*)

(*|
Question
********

I'm writing (for myself) an explanation of how to do well-founded
recursion in Coq. (see i.e. the Coq'Art book, chapter 15.2). First I
made an example function based on ``nat`` and that worked fine, but
then I did it again for ``Z``, and when I use ``Compute`` to evaluate
it, it doesn't reduce all the way down to a ``Z`` value. Why?

Here is my example (I put the text inside comments so one can
copy-paste the whole thing into your editor):
|*)

(* Test of well-founded recursion *)

(* TL;DR: To do well-founded recursion, first create 'functional' and
then create the recursive function using Acc_iter, the iterator for
accessible relations *)

(* As an example, compute the sum of the series from 1 to n, something
like this sketch:

fix f n := (if n = 0 then 0 else n + f (n-1))

Now, let's not use structural recursion on n.

Instead, we use well-founded recursion on n, using that the relation
less-than ('lt') is wellfounded. The function f terminates because the
recursive call is made on a structurally smaller term (in the
decreasing Acc-chain). *)

(* First we do it for nat *)

Require Import Arith.Arith.
Require Import Program.Utils. (* for 'dec' *)
Require Import Wellfounded.

(* From a proof that a relation is wellfounded, we can get a proof
that a particular element in its domain is accessible.

The Check commands here are not necessary, just for documentation,
dear reader. *)

Check well_founded : forall A : Type, (A -> A -> Prop) -> Prop.
Check lt_wf : well_founded lt.
Check (lt_wf 4711 : Acc lt 4711).

(* First define a 'functional' F for f. It is a function that takes a
function F_rec for the 'recursive call' as an argument. Because we
need to know n <> 0 in the second branch we use 'dec' to turn the
boolean if-condition into a sumbool. This we get info about it into
the branches.

We write most of it with refine, and leave some holes to be filled in
with tactics later. *)

Definition F (n : nat) (F_rec : (forall y : nat, y < n -> nat)) : nat.
  refine (if dec (n =? 0) then 0 else n + (F_rec (n - 1) _ )).
  (* now we need to show that n-1 < n, which is true for nat if n<>0 *)
  destruct n; now auto with *.
Defined.

(* The functional can be used by an iterator to call f as many times
as is needed.

Side note: One can either make an iterator that takes the maximal
recursive depth d as a nat argument, and recurses on d, but then one
has to provide d, and also a 'default value' to return in case d
reaches zero and one must terminate early.

The neat thing with well-founded recursion is that the iterator can
recurse on the proof of wellfoundedness and doesnt need any other
structure or default value to guarantee it will terminate. *)

(* The type of Acc_iter is pretty hairy *)

Check Acc_iter :
  forall (A : Type) (R : A -> A -> Prop) (P : A -> Type),
    (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
    forall x : A, Acc R x -> P x.

(* P is there because the return type could be dependent on the
argument, but in our case, f:nat->nat, and R = lt, so we have *)

Check Acc_iter (R:=lt) (fun _:nat=>nat) :
  (forall n : nat, (forall y : nat, y < n -> nat) -> nat) ->
  forall n : nat, Acc lt n -> nat.

(* Here the first argument is the functional that the iterator takes,
the second argument n is the input to f, and the third argument is a
proof that n is accessible. The iterator returns the value of f
applied to n.

Several of Acc_iter's arguments are implicit, and some can be
inferred. Thus we can define f simply as follows: *)

Definition f n := Acc_iter _ F (lt_wf n).

(* It works like a charm *)

Compute (f 50). (* This prints 1275 *)
Check eq_refl : f 50 = 1275.

(* Now let's do it for Z. Here we can't use lt, or lt_wf because they
are for nat. For Z we can use Zle and (Zwf c) which takes a lower
bound. It needs a lower bound under which we know that the function
will always terminate to guarantee termination. Here we use (Zwf 0) to
say that our function will always terminate at or below 0. We also
have to change the if-statement to 'if n <= 0 then 0 else ...' so we
return zero for arguments less than zero. *)

Require Import ZArith.
Require Import Zwf.

Open Scope Z.

(* Now we define the function g based on the functional G *)

Definition G (n : Z) (G_rec : (forall y : Z, Zwf 0 y n -> Z)) : Z.
  refine (if dec (n <? 0) then 0 else n + (G_rec (n - 1) _ )).
  (* now we need to show that n-1 < n *)
  now split; [apply Z.ltb_ge | apply Z.lt_sub_pos].
Defined.

Definition g n := Acc_iter _ G (Zwf_well_founded 0 n).

(* But now we can't compute! *)

Compute (g 1).

(* We just get a huge a term *)

(*|
Comment: I noticed that ``Zwf_well_founded`` is defined as ``Opaque``
in the library, so I tried to make it ``Transparent`` by copying the
proof and ending the lemma with ``Defined.`` instead of ``Qed.`` but
that didn't help...

Added observation:

If I define ``f'`` for ``nat`` with ``Fixpoint`` instead, and recurse
on the accesibility proof, *and end with* ``Defined``. then it
computes. But if I end with ``Qed.``. it doesn't reduce. Is this
related? I guess there is an issue of transparency in the definition
of ``G`` or ``g`` somewhere... Or am I completely mistaken?
|*)

Close Scope Z. (* .none *)
Fixpoint f' (n : nat) (H: Acc lt n) : nat.
  refine (if dec (n <=? 0) then 0 else n + (f' (n - 1) (Acc_inv H _))).
  apply Nat.leb_gt in e.
  apply Nat.sub_lt; auto with *.
Defined.
(* Compute (f' 10 (lt_wf 10)). doesn't evaluate to a nat if ended with Qed. *)

(*| Anyway, my problem persists for ``Z``. |*)

Open Scope Z. (* .none *)
Fixpoint g' (n : Z) (H : Acc (Zwf 0) n) : Z.
  refine (if dec (n <=? 0) then 0 else n + (g' (n - 1) (Acc_inv H _))).
  split; now apply Z.leb_gt in e; auto with *.
Defined.

Compute (g' 10 (Zwf_well_founded 0 10)).

(*|
----

**A:** This is a related `question
<https://stackoverflow.com/questions/32354286/compute-with-a-recursive-function-defined-by-well-defined-induction>`__.

**A:** This `one <https://stackoverflow.com/questions/28478445/>`__ is
somewhat related as well.
|*)

(*|
Answer
******

Making `Zwf_well_founded
<https://coq.inria.fr/library/Coq.ZArith.Zwf.html#Zwf_well_founded>`__
transparent won't help, because of the way it is defined in the
standard library:

.. code-block:: coq

    Lemma Zwf_well_founded : well_founded (Zwf c).
      ...
      case (Z.le_gt_cases c y); intro; auto with zarith.
      ...
    Qed.

If you replace the line in the proof above with

.. code-block:: coq

      case (Z_le_gt_dec c y); intro; auto with zarith.

and replace ``Qed.`` with ``Defined.`` (which you already did)
everything should work. This is due the fact that the original proof
depends on a logical term, and that prevents the evaluator from doing
pattern-matching, because logical entity ``Z.le_gt_cases`` is opaque,
while computational entity ``Z_le_gt_dec`` is transparent. See `Using
Coq's evaluation mechanisms in anger
<http://gallium.inria.fr/blog/coq-eval/>`__ blog post by Xavier Leroy.
You might also find useful `Qed Considered Harmful
<https://gmalecha.github.io/reflections/2017/qed-considered-harmful>`__
post by Gregory Malecha.

Instead of modifying the proof of ``Zwf_well_founded`` you can reuse
`Zlt_0_rec
<https://coq.inria.fr/library/Coq.ZArith.Wf_Z.html#Zlt_0_rec>`__ like
so:
|*)

Require Import Coq.ZArith.ZArith.

Open Scope Z.

Definition H (x : Z) (H_rec : (forall y : Z, 0 <= y < x -> Z))
           (nonneg : 0 <= x) : Z.
  refine (if Z_zerop x then 0 else x + (H_rec (Z.pred x) _ )).
  auto with zarith.
Defined.

Definition h (z : Z) : Z :=
  match Z_lt_le_dec z 0 with left _ => 0 | right pf => (Zlt_0_rec _ H z pf) end.

Check eq_refl : h 100 = 5050.

(*|
It's a bit less convenient because now we have to deal with negative
numbers in ``h``.
|*)
