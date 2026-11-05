# Borel actual adjacent-interval merges

The existing adjacentIntervalMerge now has a Borel actual orthogonal
projection whenever its two constructed child spaces have Borel actual
projections. Its true viability event is Borel for any real error and any
fixed original global target, using the same parent/exterior tensor
coordinates and retaining the whole complement of the parent interval.
The target need not be a product space. Empty child intervals and zero
spaces are permitted.

The proof reuses the actual regional tensor merge from QIC and then its
prescribed configuration relabeling. The true event follows from the
original tensor viability predicate, not a supplied measurable comparison
space or a selected hull. This is an auxiliary to ALVV,
arXiv:1602.08828v2, Lemma l:t, lines 500–523. It establishes no adaptive
success probability or runtime.

The source-only TN branch is based on 9ff185339e and requires QIC
4f151a064020e7b39634f6c8518e5e055df89d16, which extends 473d9766 and the a9ad4839 actual-trim stack.
The private actual-name module check used immutable TN9ff185339e / own
QIC6878435c, with explicit fresh companion overrides, full selected source
and object guards, root-input and prebuilt-Mathlib hashes, and transitive
changed-importer checks. It passed strict checking in 5.116 seconds with 55
protected source/object pairs. A combined nine-public imported foundation
inspection passed in 4.899 seconds with 91 pairs, using only propext,
Classical.choice and Quot.sound. Its temporary source was deleted.

Generated import registration, reader-facing prose, proof integrity and
whitespace checks passed. The source-only checkout has no .lake, so the
ordinary source blueprint check initially reports unresolved baseline
QIC/Mathlib declarations. Repeating that read-only source check with its
dependency resolver pointed at the exact verified provider source trees
passed, including both new declarations. This changed no repository,
dependency, cache, or source checker. The original diagnostic and the
provider-backed source report are preserved under /tmp. Canonical build
and compiled-book verification remain coordinated integration gates.

The tactic-pattern scan of the area-law sources was recorded under /tmp;
its reported repetitions are in unchanged source. The new proof reuses
the generic fixed-coordinate projection lemma rather than duplicating
coordinate calculations. The source-only worktree has no .lake. No build
artifact was copied and no Mathlib source was built.
