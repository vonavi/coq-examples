(*|
#########################
"Verbose" ``auto`` in Coq
#########################

:Link: https://stackoverflow.com/q/14917318
|*)

(*|
Question
********

I'm learning Coq and the book I'm learning from, (`CPDT
<http://adam.chlipala.net/cpdt/html/toc.html>`__) makes heavy use of
``auto`` in proofs.

Since I'm learning I think it might be helpful for me to see exactly
what ``auto`` is doing under the hood (the less magic early on the
better). Is there any way to force it to display exactly what tactics
or techniques it's using to compute the proof?

If not, is there a place which details exactly what ``auto`` does?
|*)

(*|
Answer
******

There are multiple ways to get a glance at what is going on under the
hood.

TLDR: Put ``info`` before your tactic, or use ``Show Proof.`` before
and after calling the tactic and spot the differences.

----

To see what a particular tactic invocation has been doing, you can
prefix is with ``info``, so as to show the particular proof steps it
has taken.

(This might be broken with Coq 8.4, I see that they provide ``info_``
versions of some tactics, read the error message if you need to.)

This is probably what you want at a beginner level, it can already be
quite terse.

----

Another way to see what is currently going on within a proof is to use
the command ``Show Proof.``. It will show you the currently built term
with holes, and show you which hole each of your current goals is
supposed to fill.

This is probably more advanced, especially if you use tactic such as
``induction`` or ``inversion``, as the term being built is going to be
fairly involved, and will require you to understand the underlying
nature of induction schemes or dependent pattern-matching (which CPDT
should teach you soon enough).

----

Once you have finished a proof with ``Qed.`` (or ``Defined.``), you
can also ask to look at the term that was built by using ``Print
term.`` where ``term`` is the name of the theorem/term.

This will often be a big and ugly term, and it needs some training to
be able to read these for involved terms. In particular, if the term
has been built via the use of powerful tactics (such as ``omega``,
``crush``, etc.), it is probably going to be unreadable. You'd
basically only use that to scan at some particular place of the term
you're interested in. If it's more than 10 lines long, don't even
bother reading it in such a crude format! :)

----

With all of the previous, you can use ``Set Printing All.``
beforehand, so that Coq prints the unfolded, explicit versions of
everything. It is additionally verbose but can help when you wonder
what the values of implicit parameters are.

These are all the ones I can think of on the top of my head, there
might be more though.

----

As for what a tactic does, the usual best answer is found in the
documentation:

http://coq.inria.fr/distrib/V8.4/refman/Reference-Manual011.html#@tactic155

Basically, ``auto`` tries to use all the hints provided (depending on
the database you use), and to solve your goal combining them up to
some depth (that you can specify). By default, the database is
``core`` and the depth is ``5``.

More info on that can be found here:

http://coq.inria.fr/distrib/V8.4/refman/Reference-Manual011.html#Hints-databases

----

**A:** ``info_auto`` shows only the "path to success". To see what
exactly ``auto`` tries one can use ``debug auto.``: it shows all the
fails (!) and successes.
|*)
