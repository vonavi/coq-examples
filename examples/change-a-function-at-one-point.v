(*|
##############################
Change a function at one point
##############################

:Link: https://stackoverflow.com/q/27106530
|*)

(*|
Question
********

I have two elements ``f : X -> bool`` and ``x : X``.

How to define ``g : X -> bool`` such ``g x = true`` and ``g y = f y``
for ``y != x``.
|*)

(*|
Answer (Vinz)
*************

Following your answer to my comment, I don't think you can define a
"function" ``g``, because you need a constructive way do distinguish
``x`` from other instances of type ``X``. However you could define a
relation between the two, which could be transformed into a function
if you get decidability. Something like:
|*)

Parameter X : Type.
Parameter f : X -> bool.
Parameter x : X.

Inductive gRel : X -> bool -> Prop :=
| is_x : gRel x true
| is_not_x : forall y : X, y <> x -> gRel y (f y).

Definition gdec (h : forall a b : X, {a = b} + {a <> b}) : X -> bool :=
  fun a => if h a x then true else f a.

Lemma gRel_is_a_fun: (forall a b : X, {a = b} + {a <> b}) ->
                     exists g : X -> bool, forall a, gRel a (g a).
Proof.
  intro hdec. exists (gdec hdec).
  unfold gdec. intro a. destruct (hdec a x).
  - now subst; apply is_x.
  - now apply is_not_x.
Qed.

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

Just complementing Vinz's answer, there's no way of defining such a
function for arbitrary ``X``, because it implies that ``X`` has
"almost decidable" equality:
|*)

Section Dec.

  Variable X : Type.

  Variable override : (X -> bool) -> X -> X -> bool.

  Hypothesis Hoverride_eq : forall f x, override f x x = true.
  Hypothesis Hoverride_neq : forall f x x', x <> x' -> override f x x' = f x'.

  Lemma xeq_dec' (x x' : X) : {~ x <> x'} + {x <> x'}.
  Proof using override Hoverride_eq Hoverride_neq.
    destruct (override (fun _ => false) x x') eqn:E.
    - left. intros contra.
      assert (H := Hoverride_neq (fun _ => false) _ _ contra).
      simpl in H. congruence.
    - right. intros contra. subst x'.
      rewrite Hoverride_eq in E. discriminate.
  Qed.

End Dec.

(*|
This lemma says that if there's a way of doing what you asked for for
X, then one can test whether two elements ``x`` and ``x'`` of ``X``
are equal, except that the proof of equality that one gets in the
``true`` case is actually a proof of the double negation of ``x =
x'``.
|*)
