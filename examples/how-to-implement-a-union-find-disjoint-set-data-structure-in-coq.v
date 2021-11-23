(*|
How to implement a union-find (disjoint set) data structure in Coq?
===================================================================

:Link: https://stackoverflow.com/questions/66630519/how-to-implement-a-union-find-disjoint-set-data-structure-in-coq
|*)

(*|
Question
--------

I am quite new to Coq, but for my project I have to use a union-find
data structure in Coq. Are there any implementations of the union-find
(disjoint set) data structure in Coq?

If not, can someone provide an implementation or some ideas? It
doesn't have to be very efficient. (no need to do path compression or
all the fancy optimizations) I just need a data structure that can
hold an arbitrary data type (or nat if it's too hard) and perform:
**union** and **find**.
|*)

(*|
Answer
------

If all you need is a mathematical model, with no concern for actual
performance, I would go for the most straightforward one: a functional
map (finite partial function) in which each element optionally links
to another element with which it has been merged.

- If an element links to nothing, then its canonical representative is
  itself.
- If an element links to another element, then its canonical
  representative is the canonical representative of that other
  element.

Note: in the remaining of this answer, as is standard with union-find,
I will assume that elements are simply natural numbers. If you want
another type of elements, simply have another map that binds all
elements to unique numbers.

Then you would define a function ``find : UnionFind -> nat -> nat``
that returns the canonical representative of a given element, by
following links as long as you can. Notice that the function would use
recursion, whose termination argument is not trivial. To make it
happen, I think that the easiest way is to maintain the invariant that
a number only links to a lesser number (i.e. if ``i`` links to ``j``,
then ``i > j``). Then the recursion terminates because, when following
links, the current element is a decreasing natural number.

Defining the function ``union : UnionFind -> nat -> nat -> UnionFind``
is easier: ``union m i j`` simply returns an updated map with ``max i'
j'`` linking to ``min i' j'``, where ``i' = find m i`` and ``j' = find
m j``.

[Side note on performance: maintaining the invariant means that you
cannot adequately choose which of a pair of partitions to merge into
the other, based on their ranks; however you can still implement path
compression if you want!]

As for which data structure exactly to use for the map: there are
several available. The `standard library
<https://coq.inria.fr/library/index.html>`_ (look under the title
**FSets**\ ) has several implementations (FMapList, FMapPositive and
so on) satisfying the interface `FMapInterface
<https://coq.inria.fr/library/Coq.FSets.FMapInterface.html>`_. The
stdpp libray has `gmap
<https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.gmap.html>`_.

Again if performance is not a concern, just pick the simplest encoding
or, more importantly, the one that makes your proofs the simplest. I
am thinking of just a list of natural numbers. The positions of the
list are the elements in *reverse order*. The values of the list are
*offsets*, i.e. the number of positions to skip forward in order to
reach the target of the link.

- For an element ``i`` linking to ``j`` (``i > j``), the offset is ``i
  − j``.
- For a canonical representative, the offset is zero.

With my best pseudo-ASCII-art skills, here is a map where the links
are { 6↦2, 4↦2, 3↦0, 2↦1 } and the canonical representatives are { 5,
1, 0 }:

.. code::

      6   5   4   3   2   1   0   element
      ↓  ↓  ↓  ↓  ↓  ↓  ↓
                   /‾‾‾‾‾‾‾‾‾↘
    [ 4 ; 0 ; 2 ; 3 ; 1 ; 0 ; 0 ] map
       \       \___↗↗ \_↗
        \___________/

The motivation is that the invariant discussed above is then enforced
*structurally*. Hence, there is hope that ``find`` could actually be
defined by structural induction (on the structure of the list), and
have termination for free.

----

A related paper is: `Sylvain Conchon and Jean-Christophe Filliâtre. A
Persistent Union-Find Data Structure. In ACM SIGPLAN Workshop on ML
<https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf>`_.

It describes the implementation of an efficient union-find data
structure in ML, that is persistent from the user perspective, but
uses mutation internally. What may be more interesting for you, is
that they prove it correct in Coq, which implies that they have a Coq
model for union-find. However, this model reflects the memory store
for the imperative program that they seek to prove correct. I’m not
sure how applicable it is to your problem.
|*)
