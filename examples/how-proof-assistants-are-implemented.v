(*|
#####################################
How proof assistants are implemented?
#####################################

:Link: https://stackoverflow.com/questions/58725547/how-proof-assistants-are-implemented
|*)

(*|
Question
********

What are the main blocks of a proof assistant?

I am just interested in knowing the internal logic of proof checking.
For example, topics about graphical user interfaces of such assistants
do not interest me.

A similar question to mine has been asked for compilers:
https://softwareengineering.stackexchange.com/questions/165543/how-to-write-a-very-basic-compiler

My concern is the same but for proof checking systems.
|*)

(*|
Answer (Manuel Eberl)
*********************

I'm hardly an expert on the matter (I'm only a user of these systems;
I don't worry too *much* about their internals) and this will probably
only be a vague partial answer, but the two main approaches that I
know of are:

- Dependently-typed systems (e.g. Coq, Lean, Agda) that use the
  Curry–Howard isomorphism. Statements are just types, and proofs are
  terms that have that type, so checking the validity of a proof is
  essentially just a special case of type checking a term. I don't
  want to say too much about this approach because I don't know too
  much about it and am afraid I'll get something wrong. Théo
  Winterhalter linked something in the comments above that may provide
  more context on this approach.
- LCF-style theorems provers (e.g. Isabelle, HOL Light, HOL 4). Here a
  theorem is (roughly speaking) an opaque value of type ``thm`` in the
  implementation language. Only the comparatively small 'proof kernel'
  can create these ``thm`` values and all other parts of the system
  interact with this proof kernel. The kernel offers an interface
  consisting of various small functions that implement small inference
  steps such as *modus ponens* (if you have a theorem ``A ⟹ B`` and a
  theorem ``A``, you can get the theorem ``B``) or ∀-introduction (if
  you have the theorem ``P x`` for a fixed variable ``x``, you can get
  the theorem ``∀x. P x``) etc. The kernel also offers an interface
  for defining new constants. In principle, as long as you can trust
  that these functions faithfully implement the basic inference steps
  of the underlying logic, you can trust that any ``thm`` value you
  can produce really corresponds to a theorem in your logic. For
  LCF-style provers, the answer of what the actual proof is is a bit
  more difficult to answer because they usually don't build proof
  terms (e.g. Isabelle has them, but they are disabled by default and
  not widely used). I think one could say that the history of how the
  kernel primitives are called constitute the proof, and if one were
  to record it, it could – *in principle* – be replayed and checked in
  another system.

In both cases the idea is that you have a kernel (the type checker in
the former case and the inference kernel in the latter) that you have
to trust, and then you have a large ecosystem of additional procedures
around this to provide more convenience layers. Since they have to
interact with the kernel in order to actually produce theorems,
however, you do not have to trust that code.

All these different systems have various trade-offs about what parts
of the system are in the kernel and what parts are not. In general, I
think it is fair to say that the dependently-typed systems tend to
have considerably larger kernels than the LCF-based ones (e.g. HOL
Light has a particularly small and simple kernel).

There are also other systems that I believe do not fit into these two
categories (e.g. Mizar, ACL2, PVS, Metamath, NuPRL) but I don't know
anything about how these are implemented.
|*)

(*|
Answer (Lawrence Paulson)
*************************

In the case of LCF, HOL and Isabelle, you'll find an extensive answer
to your question in the journal article "`From LCF to Isabelle/HOL
<https://link.springer.com/article/10.1007%2Fs00165-019-00492-1>`_".
(It's open access.)

Most dependently typed systems, such as Coq, are also LCF-style
theorem provers, as described in the article and in Eberl's answer.
One significant difference is that such calculi incorporate full proof
objects, so that one of the objectives of the LCF approach — to save
space by not storing proofs — is abandoned. However, the objective of
soundness is still met.
|*)
