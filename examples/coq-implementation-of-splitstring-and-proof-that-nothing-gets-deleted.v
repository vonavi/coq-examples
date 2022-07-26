(*|
###########################################################################
Coq: Implementation of ``split_string`` and proof that nothing gets deleted
###########################################################################

:Link: https://stackoverflow.com/q/73026651
|*)

(*|
Question
********

After working for a whole day on this with no success, I might get
some help here. I implemented a splitString function in Coq: It takes
a String (In my case a ``list ascii``) and a function ``f : ascii ->
bool``. I want to return a list of strings (In my case a ``list (list
ascii)``) containing all the substrings. This means that the input
string has been split at all ``ascii``\ s where f is true. Note that
my output also includes the delimiter as a string (``list ascii``) of
length 1.

My first question: exists this function in a library somewhere? Many
other, non-functional, programming languages I know includes this
function in the default library.

I didn't found something, so I implemented it by myself:
|*)

Require Import Ascii List. (* .none *)
Import ListNotations. (* .none *)
Fixpoint split_string (f : ascii -> bool) (z s : list ascii): list (list ascii) :=
  match s with
  | [] => [rev z]
  | h :: t => match f h with
              | true => ([rev z] ++ [[h]]) ++ split_string f [] t
              | false => split_string f (h :: z) t
              end
  end.

(*|
The function needs to be called with an empty ``z``, like ``Compute
split_string isWhite [] some_string.``

The clue of that List ``z`` is that the current string gets saved in
it until a delimiter is found, then the whole string ``z`` gets
returned. I don't see another way of solving this.

The problem with the List ``z`` is that, when it comes to proofing, it
makes trouble.

I want to proove that, when the output of the splitString function
gets flattened (in Coq with ``concat``) it is equal to the input,
because the splitString method does not remove information. I
formulated a theorem:
|*)

Variable isWhite : ascii -> bool. (* .none *)
Theorem not_more_not_less_splitWhite : forall s : list ascii,
    s = concat (split_string isWhite [] s).

(*|
But every time when I try to solve this with induction, I get stuck
because the List ``z`` is not empty anymore (since one char which is
not white has been processed). Then I can never apply the induction
hypothesis. This is how far I've made it:
|*)

Proof.
  intros s. induction s.
  - simpl. reflexivity.
  - simpl. destruct isWhite eqn:W.
    * simpl. rewrite <- IHs. reflexivity.
    *
Abort. (* .none *)

(*|
I found myself in willing to induce in ``s`` a second time, but I
think this is bullshit and does not use the power of induction. So, if
the answer to my first question is no, my second question is how do I
solve this, or is there a better implementation for ``split_string``.
|*)

(*|
Answer (Ana Borges)
*******************

This problem is common whenever proving things by induction about a
fixpoint with an accumulator, such as yours. The standard advice is to
find a stronger statement that has your desired result as a corollary.
This stronger statement should be about all lists, not only the empty
list. The latter should hopefully be easier to prove with induction,
since the stronger statement leads to a stronger induction hypothesis.

In your case, I guess (but haven't checked) the stronger statement
could be something like:
|*)

Theorem not_more_not_less_splitWhite_stronger : forall (z s : list ascii),
    rev z ++ s = concat (split_string isWhite z s).
Abort. (* .none *)

(*|
Answer (Pierre Castéran)
************************

Here is a proof of your theorem:
|*)

Goal forall p l buf, rev buf ++ l = concat (split_string p buf l).
Proof.
  induction l as [ | a l IHl].
  - intro. now cbn.
  - cbn. case_eq (p a); intro Ha.
    + intro buf. repeat rewrite concat_cons. now rewrite <- IHl.
    + intro buf. rewrite <- IHl. cbn. now rewrite <- app_assoc.
Qed.

(*|
Please note that it worked thanks to the universal quantification on
``buf`` in the induction hypothesis. It was made easier thanks to the
order of quantifications in the goal statement.

Ana's statement can be proved the same way, with a small bookkeeping
sequence before the induction:
|*)

Goal forall p buf l, rev buf ++ l = concat (split_string p buf l).
Proof.
  intros p buf l; revert buf.
  induction l as [| a l IHl].
  (* ... *)
