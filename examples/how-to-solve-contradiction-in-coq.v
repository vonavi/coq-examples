(*|
How to solve contradiction in Coq
=================================

https://stackoverflow.com/questions/63028399/how-to-solve-contradiction-in-coq
|*)

(*|
Question
--------

I have statement `true <> false`, in hypothesis. I want to prove `true
= false`. Can I solve it? The problem is that, it can not be solved by
contradiction.
|*)

(*|
Answer
------

I agree that you should provide a better example. That said! You need
to be clear...is `true <> false` above the line (eg a hypothesis) or
below the line (a goal)?

I'm assuming it is a goal, because as a hypothesis, it doesn't
actually tell you anything (it's just a tautology).

If it's a goal:
|*)

Goal (true <> false).
  intros contra. discriminate.
Qed.

(*|
There are a lot of general ways to deal with
contradictions...`discriminate` and `inversion` are quite common. But
a clearer example would be better.

Something to note in general is that `A <> B` is just a notation for
`A = B -> False`, which is why `intros contra` above works, because
it's pulling out the hypothesis. In cases where you're not sure what
to do, you can use intros to put the equality above the line and then
derive a contradiction.

In the case where you have something like `true <> true` *above* the
line (that's important), then you can apply it.

Example
|*)

Goal (true <> true -> 0 = 1).
  intros contra. exfalso. apply contra. reflexivity.
Qed.

(*|
`exfalso` clears out the current goal and replaces it with `False` --
this is useful when you have an impossible goal but a contradiction in
your hypothesis (above the line). `apply contra` uses the fact that
`<>` is `... -> False` like I mentioned above.
|*)
