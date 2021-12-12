(*|
#####################################################################
Defining a function that returns one element satisfying the condition
#####################################################################

:Link: https://stackoverflow.com/questions/51112347/defining-a-function-that-returns-one-element-satisfying-the-condition
|*)

(*|
Question
********

I want to declare a function that yeilds the element ``(b, n)`` that
the ``b`` is equal to true.
|*)

Require Export List.
Import Coq.Lists.List.ListNotations.

Definition lstest := list (bool * nat).

Fixpoint existbool (l : lstest) : option (bool * nat) :=
match l with
| [] => None
| (b, n) :: l' => if b then Some (b, n) else existbool l'
end.

(*|
The function always get the first element satisfyting ``b = true``. I
want to express that there exists an element satisfyting ``b = true``
and returns the element. How can I define such a function?
|*)

(*|
Answer
******

You could write a function ``get_number`` that requires a proof that
the list has a ``true`` value somewhere.
|*)

Definition has_true (l : lstest) := exists n, In (true, n) l.

(*|
``get_number`` is defined with the help of ``refine`` which lets us
leave 'holes' (written ``_``) in the proof term to fill in later. Here
we have two holes; one for the absurd case when the list is ``[]``,
and one where we construct the proof term for the recursive call.
|*)

Fixpoint get_number (l: lstest) (H: has_true l) : nat.
  refine (
      match l as l' return l = _ -> nat with
      | (true, n) :: _ => fun L => n
      | (false, _) :: l' => fun L => get_number l' _
      | [] => fun L => _
      end eq_refl).

  - exfalso. subst l. now inversion H.
  - subst l. inversion H.
    inversion H0; [inversion H1 | now (exists x)].
Defined.

(*|
The function uses the *convoy pattern* so that the ``match`` statement
does not forget the shape of ``l`` in the different branches.

If you want to, you can prove rewriting lemmas to make it easier to
use.
|*)

Lemma get_number_false l m H: exists H',
    get_number ((false, m) :: l) H = get_number l H'.
Proof. eexists; reflexivity. Qed.

Lemma get_number_true l m H: get_number ((true, m) :: l) H = m.
Proof. reflexivity. Qed.

Lemma get_number_nil H m: get_number [] H <> m.
Proof. now inversion H. Qed.

Lemma get_number_proof_irrel l H1 H2: get_number l H1 = get_number l H2.
Proof. induction l as [ | [[|] ?] l']; eauto; now inversion H1. Qed.
