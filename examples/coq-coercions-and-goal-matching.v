(*|
###############################
Coq coercions and goal matching
###############################

:Link: https://stackoverflow.com/q/45482430
|*)

(*|
Question
********

Assume I have the following setup:
|*)

Inductive exp: Set :=
| CE: nat -> exp.

Inductive adt: exp -> Prop :=
| CA: forall e, adt e.

Coercion nat_to_exp := CE.

Ltac my_tactic := match goal with
                  | [ |- adt (CE ?N) ] => apply (CA (CE N))
                  end.

(*| And I try to prove a simple theorem using the custom tactic: |*)

Theorem silly: adt 0.
Proof.
  Fail my_tactic. (* .unfold .fails .no-goals *)
Abort.

(*|
This fails, because the goal is not of the form ``adt (CE ?N)`` but of
the form ``adt (nat_to_exp ?N)`` (This is shown explicitly when using
``Set Printing Coercions``).

Trying to prove a slightly different theorem works:
|*)

Theorem silly: adt (CE 0).
Proof.
  my_tactic.
Qed.

(*|
Possible workarounds I know of:

- Not using coercions.
- Unfolding coercions in the tactic (with ``unfold nat_to_exp``). This
  alleviates the problem slightly, but fails as soon as a new coercion
  is introduced the tactic doesn't know about.

Ideally, I would like the pattern matching to succeed if the pattern
matches after unfolding all definitions (The definitions should not
stay unfolded, of course).

Is this possible? If not, are there reasons why it is not possible?
|*)

(*|
Answer
******

You can directly declare the constructor ``CE`` as a coercion rather
than wrapping it as ``nat_to_exp`` like so:
|*)

Coercion CE : nat >-> exp.

(*|
The proof then goes through without any issue. If you insist on naming
your coercion (e.g. because it's a compound expression rather than a
single constructor), you can change your tactics so that it handles
non unfolded coercions explicitly:
|*)

Reset my_tactic. (* .none *)
Ltac my_tactic := match goal with
                  | [ |- adt (CE ?N) ] => apply (CA (CE N))
                  | [ |- adt (nat_to_exp ?N) ] => apply (CA (CE N))
                  end.

(*|
----

**A:** There is also syntactic sugar for the case when constructors
are coercions:
|*)

Reset exp. (* .none *)
Inductive exp: Set := | CE :> nat -> exp.

(*|
automatically declares ``CE`` as a coercion (notice that I used ``:>``
instead of ``:`` for ``CE``).

**A:** You can also use e.g. ``cbv delta.`` before pattern-matching on
the goal to unfold transparent definitions. Then your original
``my_tactic`` would work.
|*)
