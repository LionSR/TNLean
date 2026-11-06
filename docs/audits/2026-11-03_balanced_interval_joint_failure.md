# Joint failure on the actual balanced root tree

The deterministic inclusion now covers simultaneous success at the actual
root and every interval in its existing root merge list. Its failure set is
contained in exactly the same union of guarded local failure sets as the
previous root-only theorem. The original root list and its length bound
are unchanged; no additional union over all overlapping intervals is taken.

## Statement and proof

The operation may depend arbitrarily on a choice from any type. A property
of interval spaces is assumed only at full short leaves. No probability
law, measurability, long-node success, independent replacement space or
failing-descendant witness is supplied.

Fix one choice omega. In the proof, strengthen the property locally to

    Q(a,b)(S) = P(a,b)(S) and
      every J in mergeList(a,b) satisfies P on its actual omega-space.

This is a predicate on the same actual spaces; it is not a new tree. It
captures the fixed omega only inside the pointwise argument. Its short-leaf
property holds because a short merge list is empty. Joint failure of P is
precisely root failure of Q, so the existing ancestry theorem locates a
guarded Q-failure in the original root list.

At that node, both actual children satisfy Q and hence P. If the parent
also satisfied P, all of its internal nodes would satisfy P: the two child
lists do so by the child Q statements, and the only remaining list entry is
the parent. This contradicts parent Q-failure. Thus the same node has
both children satisfying P and parent failing P, which is exactly the
original guarded P event. No recursive model, transitivity assumption or
new ancestry induction is introduced.

Valid endpoint cuts and intervals of length zero are included. A short
root has empty list and satisfies its leaf property, so joint failure is
empty there. Positive leaf width and valid-root bounds are exactly those
of the already-proved ancestry theorem. No positive Hilbert dimension is
needed.

The source context is ALVV, arXiv:1602.08828v2, Figure fig:algo1 and
lines 1777–1817. This is a deterministic auxiliary for a later joint-success
probability bound. The result itself supplies no local probability estimate
or source running-time conclusion.

The joint event concerns only the actual root subtree. In particular it
does not assert viability at all overlapping intervals. A later energy
assignment attached to this probability event must restrict its node
conclusions to that actual subtree; the earlier all-valid-interval energy
existence theorem is stronger in this respect and cannot be inferred from
the present joint event.
