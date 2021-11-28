(*|
##################################################
How to make algebraic manipulations in Coq easier?
##################################################

:Link: https://stackoverflow.com/questions/55406985/how-to-make-algebraic-manipulations-in-coq-easier
|*)

(*|
Question
********

I'm experimenting with Coq's standard libraries for integers and
rationals. So far my proofs are very time-consuming and look terrible.
I guess I miss some important proof techniques. Such simple lemmas
shouldn't be so long to prove. Any hints?

Here is an example:
|*)

Require Import ZArith.
Require Import QArith.
Open Scope Q_scope.

Theorem q_less: forall x y z, (0 <= x <= y)%Z -> x # z <= y # z.
Proof.
  intros. destruct H as [Hl Hr]. rewrite (Zle_Qle x y) in Hr.
  rewrite <- (Qmult_le_l (inject_Z x) (inject_Z y) (/ inject_Z (Zpos z))) in Hr.
  - rewrite Qmult_comm in Hr.
    rewrite Qmult_comm with (x := / inject_Z (Z.pos z)) in Hr.
    unfold inject_Z in Hr. unfold Qinv in Hr.
    destruct (Qnum (Z.pos z # 1)) eqn:ZV.
    + simpl in ZV. discriminate.
    + simpl in Hr. simpl in ZV. injection ZV. intro ZP.
      unfold Qmult in Hr. simpl in Hr. rewrite <- ZP in Hr.
      rewrite Z.mul_1_r in Hr. rewrite Z.mul_1_r in Hr. exact Hr.
    + simpl in ZV. discriminate.
  - unfold Qinv. simpl. apply Z.lt_0_1.
Qed.

(*|
Answer
******

I did not have the courage to analyze your lengthy proof, but I see
you choose to use a *forward* proof style. The telltale sign is the
fact that you have several ``rewrite ... in ...`` in your script. Most
libraries of theorems are designed to work in *backward* proof style.

Contrast this with my proposal for the same proof:
|*)

Reset q_less. (* .none *)
Theorem q_less: forall x y z, (0 <= x <= y)%Z -> x # z <= y # z.
Proof.
  intros x y z cmp. rewrite !Qmake_Qdiv. apply Qmult_le_compat_r.
  - rewrite <- Zle_Qle. tauto.
  - apply Qinv_le_0_compat. replace 0 with (inject_Z 0) by easy.
    now rewrite <- Zle_Qle.
Qed.

(*|
Here is how I proceed. First, ``x # z`` is a notation for a very
specific form of division: the one that appears in a basic fraction.
There are many chances that this specific form of division is less
well covered by theorems in the library, so I choose to replace it by
a regular division between rational numbers. To find the theorem, I
just use the ``Search`` query with the patterns ``(_ # _) (_ / _)``.
This gives me ``Qmake_Qdiv``.

Then I simply expect that there is a theorem expressing ``a <= b -> a
/ c <= b / c`` under suitable conditions. I use ``Search (_ / _ <= _ /
_).`` to find such a theorem. Alas, none is found. So I remember that
division is often described as multiplication by the inverse so I
search for the other possibility ``Search (_ * _ <= _ * _).``. This
gives me ``Qmult_le_compat_r``. I try applying it and it works.

Here is what I mean by working in a *backward* proof style: I look at
the conclusion and I think *what theorem could help me obtain this
conclusion*? *I will then try to fulfill its conditions.*

There are two conditions. The first one is ``(inject_Z x <= inject_Z
y)``. So now I need a theorem relating comparison in ``Z`` and
comparison in ``Q`` through function ``inject_Z``. To find it I type
``Search inject_Z (_ <= _).``. This gives me ``Zle_Qle``. Please note
that your hypothesis is too strong: you don't need ``x`` to be
positive. The automatic tactic ``tauto`` obtains the right condition
from your hypothesis (which I named ``cmp``).

The last condition is ``(0 <= inject_Z (Z.pos z))``. I can re-use the
same theorem as above, because surely ``0`` must be the same thing as
``inject_Z 0``.

All this being said, I do not recommend using ``QArith`` for
mathematical reasoning (the kind of algebraic reasoning that you show
here), because it is less well populated than other libraries. If you
want to work with numbers and reason on them, you should use
``math-comp`` or ``Reals``: you will find more theorems that are
already proved for you.

----

**Q:** thanks for the elaborate explanation. I repeated your steps.
Makes sense! How did you acquire such a strategy? Is it just the
experience?

**A:** I don't remember, I learned by trials and errors, too long ago
(28 years). But I remember that in the beginning there were no
``rewrite ... in ...`` or ``apply ... in ...`` tactics, so that the
backward style was practically
|*)
