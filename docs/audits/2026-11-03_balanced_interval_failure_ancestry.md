# Guarded failure ancestry below one balanced root

For an arbitrary choice space, each choice determines one merge operation
of the existing balanced interval recursion. Fix any property of interval
spaces which holds for the full local space at every valid short leaf.
The new deterministic theorem proves that the root failure set is contained
in the union of guarded local failure sets over precisely the existing
balancedIntervalMergeList below that root.

A guarded local failure means that both actual midpoint children satisfy
the property but their actual parent does not. Every space is evaluated
using the same chosen operation. No successful-parent assumption, local
failure bound, probability law, measurability hypothesis or supplied failing
descendant is used. In particular the theorem supplies the deterministic
set inclusion needed before a separate probabilistic union bound.

## Proof and edge cases

Fix a choice and induct on the root length. A short root is the full local
space, so its assumed leaf property excludes failure. At a long root,
consider its actual two midpoint children. If either fails, the induction
locates a guarded failed descendant in that child's actual merge list,
which is a sublist of the root merge list. If both satisfy the property,
the failed parent itself gives the required witness and is the final entry
of the root list. The set inclusion follows by inserting this witness into
the indexed union.

The positive leaf width guarantees that both children of a long valid root
are strictly shorter. Weak endpoint cuts and intervals of length zero are
included. A zero-length root is a short leaf and therefore has empty failure
set under the leaf hypothesis. The proof needs no positive local dimension
or nonzero Hilbert space. The index list is the existing actual list, not a
new tree model and not all overlapping intervals. No distinctness of entries
is needed, so duplicates would not affect the union.

The source context is ALVV, arXiv:1602.08828v2, Figure fig:algo1 and the
probability estimate at lines 1777–1817. This is a separate deterministic
auxiliary, not a proof of the source's probability or running-time theorem.
Conditional local probability estimates and their later summation remain
separate. The existing count of the actual root list is unchanged.
