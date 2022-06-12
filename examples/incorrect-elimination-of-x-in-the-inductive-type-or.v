(*|
###########################################################
Incorrect elimination of ``X`` in the inductive type ``or``
###########################################################

:Link: https://stackoverflow.com/q/32261254
|*)

(*|
Question
********

I am trying to define a relatively simple function on Coq:
|*)

(* Preliminaries *)
Require Import Vector.
Definition Vnth {A : Type} {n} (v : Vector.t A n) : forall i, i < n -> A.
Admitted.

(* Problematic definition below *)
Fail Definition VnthIndexMapped {A : Type}
           {i o : nat}
           (x : Vector.t (option A) i)
           (f' : nat -> option nat)
           (f'_spec : forall x,
               x < o -> (forall z, f' x = Some z -> z < i) \/ f' x = None)
           (n : nat)
           (np : n < o) : option A :=
  match f' n as fn, f'_spec n np return f' n = fn -> option A with
  | None, _ => fun _ => None
  | Some z, or_introl zc1 => fun p => Vnth x z (zc1 z p)
  | Some z, or_intror _ => fun _ => None (* impossible case *)
  end. (* .unfold *)

(*|
I think I understand the reason for this limitation, but I am having
difficulty coming up with a workaround. How something like this could
be implemented? Basically I have a function ``f'`` for which I have a
separate proof that values less than ``o`` it either returns ``None``
or a ``Some z`` where ``z`` is less than ``i`` and I am trying to use
it in my definition.
|*)

(*|
Answer (Vinz)
*************

The issue is that you want to build a term by inspecting the content
of ``f'_spec``. This disjunction lives in ``Prop``, so it can only
build other ``Prop``. You want to build more, something in ``Type``.
Therefore you need a version of disjunction that lives at least in
``Set`` (more generally in ``Type``). I advise you replace your ``Foo
\/ Bar`` statement with the usage of ``sumbool``, which uses the
notation ``{Foo} + {Bar}``.

----

**Q:** What would be the other implications of using ``sumbool``
instead of ``\/``? Any potential problems?

**A:** Basically if I give you ``P : A \/ B``, you can't tell if it
``A`` or ``B`` that its true. You just know one of them is. With ``{A}
+ {B}``, you also get to know which one is true (because you can
destruct the term).
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

There are two approaches to a problem like this: the *easy way* and
the *hard way*.

The easy way is to think whether you're doing anything more
complicated than you have to. In this case, if you look carefully, you
will see that your ``f'_spec`` is equivalent to the following
statement, which avoids ``\/``:
|*)

Lemma f'_spec_equiv i o (f' : nat -> option nat) :
  (forall x, x < o -> (forall z, f' x = Some z -> z < i) \/ f' x = None)
  <-> (forall x, x < o -> forall z, f' x = Some z -> z < i).
Proof.
  split.
  - intros f'_spec x Hx z Hf.
    destruct (f'_spec _ Hx); eauto; congruence.
  - intros f'_spec x Hx.
    left. eauto.
Qed.

(*|
Thus, you could have rephrased the type of ``f'_spec`` in
``VnthIndexedMapped`` and used the proof directly.

Of course, sometimes there's no way of making things simpler. Then you
need to follow the hard way, and try to understand the nitty-gritty
details of Coq to make it accept what you want.

As Vinz pointed out, you *usually* (there are exceptions) can't
eliminate the proof of proposition to construct something
computational. However, you *can* eliminate a proof to construct
*another proof*, and maybe that proof gives you what need. For
instance, you can write this:
|*)

Definition VnthIndexMapped {A : Type}
           {i o : nat}
           (x : Vector.t (option A) i)
           (f' : nat -> option nat)
           (f'_spec : forall x,
               x < o -> (forall z, f' x = Some z -> z < i) \/ f' x = None)
           (n : nat)
           (np : n < o) : option A :=
  match f' n as fn return f' n = fn -> option A with
  | None => fun _ => None
  | Some z => fun p =>
                let p' := proj1 (f'_spec_equiv i o f') f'_spec n np z p in
                Vnth x z p'
  end eq_refl.

(*|
This definition uses the proof that both formulations of ``f'_spec``
are equivalent, but the same idea would apply if they weren't, and you
had some lemma allowing you to go from one to the other.

I personally don't like this style very much, as it is hard to use and
lends itself to programs that are complicated to read. But it can have
its uses...
|*)
