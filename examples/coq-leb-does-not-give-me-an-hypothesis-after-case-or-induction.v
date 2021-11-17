(*|
Coq leb <=? does not give me an hypothesis after case or induction
==================================================================

:Link: https://stackoverflow.com/questions/66709518/coq-leb-does-not-give-me-an-hypothesis-after-case-or-induction
|*)

(*|
Question
--------

I have simplified my situation to the following piece of code,
hopefully this makes it easier to understand.

I would like to prove the following Lemma:
|*)

Require Import Arith.
Lemma example: forall a b,
    if a <=? b then a <= b else a > b.
Proof.
  intros. (* .unfold *)

(*|
It seems trivial that either `a` is smaller than or equal to `b`, in
which case I could prove `a<=b`. In the other case that `b` is larger
than `a` I could prove that `a>b`.

I've tried to prove this with `induction (a <=? b)` or `case (a <=?
b)` but both give me the following result.
|*)

induction (a <=? b). (* .unfold *)
Abort. (* .none *)

(*|
Now I have no way to prove these goals. I expected to gain an
hypothesis such as `H: a <= b` and `H: a > b` in the second case. This
way, I would be able to prove my goals.

Could anybody tell me how I could this issue of the non-appearing
hypothesis?

Edit: The whole lemma can be proven as follows:
|*)

Require Import Arith.
Lemma example: forall a b,
    if a <=? b then a <= b else a > b.
Proof.
  intros.
  case (Nat.leb_spec a b); intuition.
Qed.

(*|
Answer
------

To do the case distinction that you are looking for you can use
|*)

Lemma leb_spec x y : BoolSpec (x <= y) (y < x) (x <=? y).

(*|
The type `BoolSpec` embodies exactly what you are trying to do: if `(x
<=? y)` is *the boolean* `true`, then *the proposition* `x <= y` is
true, and if `(x <=? y)` is `false` then `y < x` is true. Thus,
`Nat.leb_spec` embodies the specification of the function `x <=? y`,
as its name suggests.

Now using `case (Nat.leb_spec a b)` does exactly what you were trying
to do with `case (a <=? b)`: it gives you two subgoals, one where `x
<=? y` is replaced by `true` and you have `x <= y` as an extra
hypothesis, and the other where `x <=? y` is replaced by `false` and
you have `y < x` as an hypothesis instead. The fact that you case
distinction was on a term of type `BoolSpec` rather than simply `bool`
did the trick.
|*)
