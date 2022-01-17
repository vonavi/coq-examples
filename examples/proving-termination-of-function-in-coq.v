(*|
######################################
Proving Termination of Function in Coq
######################################

:Link: https://stackoverflow.com/q/46928911
|*)

(*|
Question
********

I am having trouble proving termination of the following function:

.. coq:: none
|*)

Require Import Arith Ascii.

Inductive regex : Set :=
| Empty   : regex
| Epsilon : regex
| Symbol  : ascii -> regex
| Union   : regex -> regex -> regex
| Concat  : regex -> regex -> regex
| Star    : regex -> regex.

Lemma eq_regex_dec : forall u v : regex, {u = v} + {u <> v}.
Proof. decide equality. apply ascii_dec. Defined.

Fixpoint le_regex u v : bool :=
  match u, v with
  | Empty       , _            => true
  | _           , Empty        => false
  | Epsilon     , _            => true
  | _           , Epsilon      => false
  | Symbol a    , Symbol b     => nat_of_ascii a <=? nat_of_ascii b
  | Symbol _    , _            => true
  | _           , Symbol _     => false
  | Star u      , Star v       => le_regex u v
  | Star u      , _            => true
  | _           , Star v       => false
  | Union u1 u2 , Union v1 v2  => if eq_regex_dec u1 v1
                                  then le_regex u2 v2
                                  else le_regex u1 v1
  | Union _ _   , _            => true
  | _           , Union _ _    => false
  | Concat u1 u2, Concat v1 v2 => if eq_regex_dec u1 v1
                                  then le_regex u2 v2
                                  else le_regex u1 v1
  end.

(*||*)

Fail Fixpoint norm_union u v : regex :=
  match u, v with
  | Empty    , v         => v
  | u        , Empty     => u
  | Union u v, w         => norm_union u (norm_union v w)
  | u        , Union v w => if eq_regex_dec u v
                            then Union v w
                            else if le_regex u v
                                 then Union u (Union v w)
                                 else Union v (norm_union u w)
  | u        , v         => if eq_regex_dec u v
                            then u
                            else if le_regex u v
                                 then Union u v
                                 else Union v u
  end. (* .fails *)

(*|
where ``regex`` is the type of regular expressions and ``le_regex``
implements a total ordering on regular expressions. The source is page
five of `this <http://www21.in.tum.de/~krauss/papers/rexp.pdf>`__
document. The function occurs as part of a normalization function for
regular expressions (formalized in Isabelle/HOL). The ``le_regex``
function is adapted from the same paper. I am using ``ascii`` to avoid
parameterizing ``regex`` by a decidable total ordering (and want to
extract the program).
|*)

Reset Initial. (* .none *)
Require Import Arith Ascii. (* .none *)
Inductive regex : Set :=
| Empty   : regex
| Epsilon : regex
| Symbol  : ascii -> regex
| Union   : regex -> regex -> regex
| Concat  : regex -> regex -> regex
| Star    : regex -> regex.

Lemma eq_regex_dec : forall u v : regex, {u = v} + {u <> v}.
Proof. decide equality. apply ascii_dec. Defined.

Fixpoint le_regex u v : bool :=
  match u, v with
  | Empty       , _            => true
  | _           , Empty        => false
  | Epsilon     , _            => true
  | _           , Epsilon      => false
  | Symbol a    , Symbol b     => nat_of_ascii a <=? nat_of_ascii b
  | Symbol _    , _            => true
  | _           , Symbol _     => false
  | Star u      , Star v       => le_regex u v
  | Star u      , _            => true
  | _           , Star v       => false
  | Union u1 u2 , Union v1 v2  => if eq_regex_dec u1 v1
                                  then le_regex u2 v2
                                  else le_regex u1 v1
  | Union _ _   , _            => true
  | _           , Union _ _    => false
  | Concat u1 u2, Concat v1 v2 => if eq_regex_dec u1 v1
                                  then le_regex u2 v2
                                  else le_regex u1 v1
  end.

(*|
I think the correct approach is to define a decreasing measure and use
``Program Fixpoint`` to prove termination. However, I'm having trouble
coming up with the correct measure (attempts based on the number of
operators have been unsuccessful). I have tried factoring the work
into separate functions, but ran into similar problems. Any help would
be appreciated, or hints pointing in the right direction.
|*)

(*|
Answer (Yves)
*************

Your code is more complex than what is usually handled with a measure
function, because you have a nested recursive call in the following
line:

.. code-block:: coq

    Union u v, w         => norm_union u (norm_union v w)  (* line 5 *)

I suggest that you should not return a value in type ``regex``, but in
type ``{r : regex | size r < combined_size u v}`` for suitable notions
of ``size`` and ``combined_size``.

After several hours of study on your problem, it also turns out that
your recursion relies on lexical ordering of the arguments.
``norm_union v w`` may well return ``Union v w``, so you need that the
argument pair ``(u, Union v w)`` is smaller than ``(Union u v, w)``.
So if you really want to use a measure, you need the weight of the
left-hand side to be larger than the weight of the right-hand side,
and you need the measure of a component of a ``Union`` to be less than
the measure of the whole.

Because of the lexical ordering nature, I chose to not use a measure
but a well-founded order. Also, I don't know ``Program Fixpoint`` well
enough, so I developed a solution to your problem using another tool.
The solution I came up with can be seen `here on github
<https://github.com/ybertot/norm_union_example>`__. At least this
shows all the decrease conditions that need to be proved.
|*)

(*|
Answer (Yves)
*************

After an extra day of work, I now have a more complete answer to this
question. It is still visible at `this link
<https://github.com/ybertot/norm_union_example>`__. This solution
deserves a few comments.

First, I am using a function constructor called ``Fix`` (the long name
is ``Coq.Init.Wf.Fix``). This is a higher order function that can be
used to define functions by well-founded recursion. I need a well
founded order for this, this order is called ``order``. Well founded
orders were studied intensively in the early 2000s and they are still
at the foundation of the ``Program Fixpoint`` command.

Second, the code you wrote performs case analyses on two values of
type ``regex`` simultaneously, so this leads to 36 cases (a bit less,
because there is no case analysis on the second argument when the
first one is ``Empty``). You don't see the 36 cases in your code,
because several constructors are covered by the same rule where the
pattern is just a variable. To avoid this multiplication of cases, I
devised a specific inductive type for the case analyses. I called this
specific type ``arT``. Then I define a function ``ar`` that maps any
element of type ``regex`` to the corresponding element of ``arT``. The
type ``arT`` has three constructors instead of six, so pattern
matching expressions will contain much less code and proofs will be
less verbose.

Then I proceeded to define ``norm_union`` using ``Fix``. As usual in
Coq (and in most theorem provers, including Isabelle), the language of
recursive definitions ensures that recursive functions always
terminate. In this case, this is done by imposing that recursive calls
only happen on arguments that are *smaller* than the function's input.
In this case, this is done by describing the body of the recursive
function by a function that takes as first argument the initial input
and as second argument the function that will be used to represent the
recursive calls. The name of this function is ``norm_union_F`` and its
type is as follows:

.. code-block:: coq

    forall p : regex * regex,
      forall g : (forall p', order p' p ->
                             {r : regex | size_regex r <= size_2regex p'}),
        {r : regex | size_regex r <= size_2regex p}

In this type description, the name of the function used to represent
recursive calls is ``g`` and we see that the type of ``g`` imposes
that it can only be used on pairs of ``regex`` terms that are smaller
than the initial argument ``p`` for the order named ``order``. In this
type description, we also see I chose to express that the returned
type of the recursive calls is not ``regex`` but ``{r : regex |
size_regex r <= size_2regex p'}``. This is because we have to handle
*nested* recursion, where outputs of recursive calls will be used as
inputs of other recursive calls. **This is the main trick of this
answer.**

Then we have the body of the ``norm_union_F`` function:

.. coq:: none
|*)

Require Import Psatz Relation_Operators.

Fixpoint size_regex u :=
  match u with
  | Union u v => size_regex u + size_regex v + 1
  | _ => 0
  end.

Definition size_2regex (p : regex * regex) :=
  let (u, v) := p in
  size_regex u + size_regex v + 1.

Inductive arT (u : regex) : Type :=
| arE : u = Empty -> arT u
| arU : forall v w, u = Union v w -> arT u
| arO : u <> Empty -> (forall v w, u <> Union v w) -> arT u.

Definition ar u : arT u.
Proof.
  destruct u as [| |s|u v| |];
    [apply arE; auto | apply arO| apply arO | apply (arU _ u v); auto |
      apply arO | apply arO ]; discriminate.
Defined.

Lemma th1 p : size_regex (snd p) <= size_2regex p.
Proof.
  destruct p. unfold size_2regex. simpl. lia.
Qed.

Lemma th2' p u v (h : fst p = Union u v) :
  size_regex (Union u v) <= size_2regex p.
Proof.
  destruct p. rewrite <- h. unfold size_2regex. simpl. lia.
Qed.

Definition order : regex * regex -> regex * regex -> Prop :=
  fun p1 p2 =>
    lexprod nat (fun _ =>  nat)
            lt (fun _ => lt)
            (existT _ (size_2regex p1) (size_regex (fst p1)))
            (existT _ (size_2regex p2) (size_regex (fst p2))).

Lemma th3' p u v (h : fst p = Union u v) :
  order (v, snd p) p.
Proof.
  destruct p. unfold order. apply left_lex. simpl.
  simpl in h. rewrite h. simpl. lia.
Qed.

Lemma th4' p u v (eq1 : fst p = Union u v) (h : order (v, snd p) p)
      r (rs : size_regex r <= size_2regex (v, snd p)) :
  order (u, r) p.
Proof.
  destruct p as [p1 p2]. simpl in eq1. rewrite eq1.
  simpl in rs |- *.
  apply le_lt_or_eq in rs. destruct rs as [rlt | req].
  - now apply left_lex; simpl; lia.
  - unfold order. simpl.
    replace (size_regex u + size_regex r + 1) with
      (size_regex u + size_regex v + 1 + size_regex p2 + 1) by
      ring [req].
    apply right_lex. lia.
Qed.

Lemma th5' p u v (eq1 : (fst p) = Union u v)
      r1 (r1s : size_regex r1 <= size_2regex (v, snd p))
      r2 (r2s : size_regex r2 <= size_2regex (u, r1)) :
  size_regex r2 <= size_2regex p.
Proof.
  destruct p as [p1 p2]. simpl in eq1, r1s, r2s |- *.
  rewrite eq1. simpl. lia.
Qed.

Lemma th7' p v w (eq2 : snd p = Union v w) :
  size_regex (Union v w) <= size_2regex p.
Proof. destruct p. rewrite <- eq2. simpl. lia. Qed.

Lemma th8' p v w (eq1 : snd p = Union v w) :
  size_regex (Union (fst p) (Union v w)) <= size_2regex p.
Proof.
  destruct p. rewrite <- eq1. simpl. lia.
Qed.

Lemma th9' p v w (eq2 : snd p = Union v w) :
  order (fst p, w) p.
Proof.
  destruct p as [p1 p2]. simpl in eq2 |- *.
  rewrite eq2. apply left_lex. simpl. lia.
Qed.

Lemma th10' p v w (eq2 : snd p = Union v w)
      r (rs : size_regex r <= size_2regex (fst p, w)) :
  size_regex (Union v r) <= size_2regex p.
Proof.
  destruct p as [p1 p2]. simpl in eq2, rs |- *.
  rewrite eq2. simpl. lia.
Qed.

Lemma th11' p : size_regex (fst p) <= size_2regex p.
Proof.
  destruct p as [p1 p2]. simpl. lia.
Qed.

Lemma th12' p : size_regex (Union (fst p) (snd p)) <= size_2regex p.
Proof.
  destruct p. simpl. lia.
Qed.

Lemma th13' p : size_regex (Union (snd p) (fst p)) <= size_2regex p.
Proof.
  destruct p. simpl. lia.
Qed.

(*||*)

Definition norm_union_F : forall p : regex * regex,
  forall g : (forall p', order p' p ->
                         {r : regex | size_regex r <= size_2regex p'}),
    {r : regex | size_regex r <= size_2regex p} :=
  fun p norm_union =>
    match ar (fst p) with
    | arE _ eq1 => exist _ (snd p) (th1 p)
    | arU _ u v eq1 =>
        match ar (snd p) with
        | arE _ eq2 => exist _ (Union u v) (th2' _ _ _ eq1)
        | _ => exist _ (proj1_sig
                          (norm_union (u,
                                        proj1_sig (norm_union (v, snd p)
                                                              (th3' _ _ _ eq1)))
                                      (th4' _ _ _ eq1 (th3' _ _ _ eq1)
                                            (proj1_sig (norm_union (v, snd p)
                                                                   (th3' _ _ _ eq1)))
                                            _)))
                     (th5' _ _ _ eq1
                           (proj1_sig (norm_union (v, snd p)
                                                  (th3' _ _ _ eq1)))
                           (proj2_sig (norm_union (v, snd p)
                                                  (th3' _ _ _ eq1)))
                           (proj1_sig
                              (norm_union
                                 (u, proj1_sig (norm_union (v, snd p)
                                                           (th3' _ _ _ eq1)))
                                 (th4' _ _ _ eq1 (th3' _ _ _ eq1)
                                       (proj1_sig (norm_union (v, snd p)
                                                              (th3' _ _ _ eq1)))
                                       (proj2_sig (norm_union (v, snd p)
                                                              (th3' _ _ _ eq1))))))
                           (proj2_sig
                              (norm_union
                                 (u, proj1_sig (norm_union (v, snd p)
                                                           (th3' _ _ _ eq1)))
                                 (th4' _ _ _ eq1 (th3' _ _ _ eq1)
                                       (proj1_sig (norm_union (v, snd p)
                                                              (th3' _ _ _ eq1)))
                                       (proj2_sig (norm_union (v, snd p)
                                                              (th3' _ _ _ eq1)))))))
        end
    | arO _ d1 d2 =>
        match ar (snd p) with
        | arE _ eq2 => exist _ (fst p) (th11' _)
        | arU _ v w eq2 =>
            if eq_regex_dec (fst p) v then
              exist _ (Union v w) (th7' _ _ _ eq2)
            else if le_regex (fst p) v then
                   exist _ (Union (fst p) (Union v w)) (th8' _ _ _ eq2)
                 else exist _ (Union v (proj1_sig (norm_union (fst p, w)
                                                              (th9' _ _ _ eq2))))
                            (th10' _ _ _ eq2
                                   (proj1_sig (norm_union (fst p, w)
                                                          (th9' _ _ _ eq2)))
                                   (proj2_sig (norm_union (fst p, w)
                                                          (th9' _ _ _ eq2))))
        | arO _ d1 d2 =>
            if eq_regex_dec (fst p) (snd p) then
              exist _ (fst p) (th11' _)
            else if le_regex (fst p) (snd p) then
                   exist _ (Union (fst p) (snd p)) (th12' _)
                 else exist _ (Union (snd p) (fst p)) (th13' _)
        end
    end.

(*|
In this code, all output values are within an ``exist _`` context: not
only do we produce the output value, but we also show that the size of
this value is smaller than the combined size of the input pair of
values. More over, all recursive calls are within a ``proj1_sig``
context, so that we forget the size information at the moment of
constructing the output value. But also, all recursive calls, here
represented by calls to the function named ``norm_union`` also have a
proof that the input to the recursive call is indeed smaller than the
initial input. All the proofs are in `the complete development
<https://github.com/ybertot/norm_union_example>`__.

It would probably be possible to use tactics like ``refine`` to define
``norm_union_F``, you are invited to explore.

Then we define the truly recursive function ``norm_union_1``:

.. coq:: none
|*)

Require Import Wellfounded.

Lemma well_founded_order : well_founded order.
Proof.
  unfold order.
  apply (wf_inverse_image
           (regex * regex) {x : nat & nat}
           (lexprod nat (fun _ => nat) lt (fun _ => lt))
           (fun p => (existT _ (size_2regex p) (size_regex (fst p))))).
  apply wf_lexprod; intros; apply Nat.lt_wf_0.
Qed.

(*||*)

Definition norm_union_1 : forall p : regex * regex,
    {x | size_regex x <= size_2regex p} :=
  Fix well_founded_order (fun p => {x | size_regex x <= size_2regex p})
      norm_union_F.

(*|
Note that the output of ``norm_union_1`` has type ``{x | size_regex x
<= size_2regex p}``. This is not the type you asked for. So we define
a new function, which is really the one you want, simply by forgetting
the logical information that the output has a size smaller than the
input.
|*)

Definition norm_union u v : regex := proj1_sig (norm_union_1 (u, v)).

(*|
You might still doubt that this is the right function, the one you
asked for. To convince ourselves, we are going to prove a lemma that
expresses exactly what you would have said in a definition.

We first prove the corresponding lemma for ``norm_union_1``. This
relies on a theorem associated to the ``Fix`` function, name
``Fix_eq``. The proof that needs to be done is fairly routine (it
always is, it could be done automatically, but I never came around to
developing the automatic tool for that).

Then we finish with most interesting lemma, the one for
``norm_union``. Here is the statement:
|*)

Lemma norm_union_eqn u v :
  norm_union u v =
    match u, v with
    | Empty    , v         => v
    | u        , Empty     => u
    | Union u v, w         => norm_union u (norm_union v w)
    | u        , Union v w => if eq_regex_dec u v
                              then Union v w
                              else if le_regex u v
                                   then Union u (Union v w)
                                   else Union v (norm_union u w)
    | u        , v         => if eq_regex_dec u v
                              then u
                              else if le_regex u v
                                   then Union u v
                                   else Union v u
    end.

(*|
Please note that the right-hand-side of this equation is exactly the
code that you gave in your initial question (I simply copy-pasted it).
The proof of this final theorem is also fairly systematic.

Now, I made the effort of following exactly your request, but after
the fact I discovered that there is a simple implementation of the
same functionality, using three recursive functions. The first one
flattens binary trees of ``Union`` to make then look like list, and
the other two sort these union with respect to the order ``le_regex``
while removing duplicates as soon as they are uncovered. Such an
implementation would workaround the need for nested recursion.

If you still want to stick to nested recursion and need to refer to
the technique described here, it was first published in a paper by
Balaa and Bertot at TPHOLs2000. That paper is difficult to read
because it was written at a time when Coq was using a different
syntax.
|*)
