(*|
##################################################################
Confused about pattern matching in ``Record`` constructions in Coq
##################################################################

:Link: https://stackoverflow.com/q/36265021
|*)

(*|
Question
********

I've been using Coq for a very short time and I still bump into walls
with some things. I've defined a set with a ``Record`` construction.
Now I need to do some pattern matching to use it, but I'm having
issues properly using it. First, these are my elements.
|*)

Inductive element : Set :=
| empty : element
| fun_m : element -> element -> element
| n_fun : nat -> element -> element.

(*|
I pick the elements with certain characteristic to make a subset of
them the next way:
|*)

Inductive esp_char : element -> Prop :=
| esp1 : esp_char empty
| esp2 : forall (n : nat) (E : element), esp_char E -> esp_char (n_fun n E).

Record especial : Set := mk_esp {E : element; C : (esp_char E)}.

(*|
Now, I need to use definition and fix point on the ``especial``
elements, just the two that I picked. I have read the documentation on
Record and what I get is that I'd need to do something like this:
|*)

Fail Fixpoint Size (E : especial) : nat :=
  match E with
  |{| E := empty |}      => 0
  |{| E := n_fun n E0 |} => (Size E0) + 1
  |{| E := _ |}          => 0
  end. (* .fails *)

(*|
Of course this tells me that I'm missing everything on the inductive
part of elements so I add ``{| E := _ |} => 0``, or anything, just to
make the induction full. Even doing this, I then find this problem:
|*)

Fail Fixpoint Size (E : especial) : nat :=
  match E with
  |{| E := empty |}      => 0
  |{| E := n_fun n E0 |} => (Size E0) + 1
  |{| E := _ |}          => 0
  end. (* .unfold .messages *)

(*|
What I have been unable to do is fix that last thing, I have a lemma
proving that if ``n_fun n E0`` is ``especial`` then ``E0`` is
``especial``, but I can't build it as so inside the ``Fixpoint``. I
also defined the size for "all elements" and then just picked the
``especial`` ones in a definition, but I want to be able to do direct
pattern matching directly on the set ``especial``. Thank you for your
input.

EDIT: Forgot to mention that I also have a coercion to always send
``especial`` to ``elements``.

EDIT: This is the approach I had before posting:
|*)

Fixpoint ElementSize (E : element) : nat :=
  match E with
  | n_fun n E0 => (ElementSize E0) + 1
  | _  => 0
  end.

Fail Definition Size (E : especial) := ElementSize E. (* .fails *)

(*|
Answer (ejgallego)
******************

I'd have tried to do:
|*)

Lemma mk_especial_proof n E : esp_char (n_fun n E) -> esp_char E.
Proof. now intros U; inversion U. Qed.

Fail Fixpoint Size (E : especial) : nat :=
  match E with
  |{| E := empty              |} => 0
  |{| E := n_fun n E0; C := P |} =>
     (Size (mk_esp E0 (mk_especial_proof _ _ P))) + 1
  |{| E := fun_m E1 E2        |} => 0
  end. (* .fails *)

(*|
However this will fail the termination check. I'm not familiar with
how to overcome this problem with records. I'd definitively follow the
approach I mentioned in the comments (using a fixpoint over the base
datatype).

EDIT: Added single fixpoint solution.
|*)

Fixpoint size_e e :=
  match e with
  | empty       => 0
  | fun_m e1 e2 => 0
  | n_fun _   e => 1 + size_e e
  end.

Definition size_esp e := size_e (E e).

(*|
Answer (larsr)
**************

I reduced your example to this, but you can easily go back to your
definition. We have a set, and a subset defined by an inductive
predicate. Often one uses sigma types for this, with the notation ``{b
| Small b}``, but it is actually the same as the ``Record`` definition
used in your example, so never mind :-).
|*)

Reset Initial. (* .none *)
Inductive Big : Set :=          (* a big set *)
| A
| B (b0 b1 : Big)
| C (b : Big).

Inductive Small : Big -> Prop := (* a subset *)
| A' : Small A
| C' (b : Big) : Small b -> Small (C b).

Record small := mk_small { b : Big; P : Small b }.

(*| Here is a solution. |*)

Lemma Small_lemma : forall b, Small (C b) -> Small b.
Proof. intros b H. now inversion H. Qed.

Fixpoint size (b : Big) : Small b -> nat :=
  match b with
  | A => fun _ => 0
  | B _ _ => fun _ => 0
  | C b' => fun H => 1 + size b' (Small_lemma _ H)
  end.

Definition Size (s : small) : nat :=
  let (b, H) := s in size b H.

(*|
To be able to use the hypothesis ``H`` in the ``match``-branches, it
is sent into the branch as a function argument. Otherwise the
destruction of ``b`` is not performed on the ``H`` term, and Coq can't
prove that we do a structural recursion on ``H``.
|*)
