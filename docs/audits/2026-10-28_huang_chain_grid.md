# Explicit block and buffer geometry for propagation on a chain

`TNLean/MPS/AreaLaw/Huang/ChainGrid.lean` constructs the support layouts of the
two-layer propagation argument directly from $L,w,r$. Its source is
[Osborne, arXiv:quant-ph/0508031v2](https://arxiv.org/pdf/quant-ph/0508031v2), Figure 2,
with the finite propagator approximation used by
[Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4, Lemma 19.
It proves geometry only; operators, their evolution and the Hamiltonian decomposition
are separate contributions.

For $w>0$, the blocks are the clipped intervals $[jw,(j+1)w)$, with labels
$j< L/w+1$. The owner of site $x$ is the explicitly defined quotient $x/w$.
The module proves coverage, pairwise disjointness, width and cardinality at most $w$,
and at most $L+1$ block labels. The last labeled block may be empty.

Internal boundaries are $c_k=(k+1)w$ for $k<(L-1)/w$. They are all strictly between
zero and $L$, with at most $L$ labels. Their adjacent pairs are
$[c_k-1,c_k+1)=\{c_k-1,c_k\}$. The actual closed radius-$r$ neighborhood is proved
equal to the clipped interval $[c_k-1-r,c_k+r+1)$. Its nominal width and cardinality
are at most $2r+2$. When $2r+2\le w$, the buffers are pairwise disjoint.

Every nearest-neighbor edge lies in one block or crosses an enumerated boundary.
The two cases are proved mutually exclusive. At a boundary the edge is exactly
the designated adjacent pair. Thus the statement supplies the actual partition and
all crossing edges; it assumes neither a partition nor an edge classification.
It also includes the empty chain, where the boundary label type is empty.

The module passed actual separate-module compilation with the strict changed-module
flags and warnings treated as errors in 4.99 seconds. Its SHA-256 is
`ddae7082f952a446d3d773e58623ad57fa899c177109988a4c0a81a92229588d`.
The imported fixture `scripts/huang_chain_grid_regression.lean` passed separately
in 5.76 seconds, checking all 21 public declarations. Their dependencies contain
only `propext`, `Classical.choice` and `Quot.sound`. Source hashes remained
unchanged during the checks, with all outputs confined to private temporary artifacts.

The same-commit worktree seed subsequently completed successfully. After integration,
the geometry passed the guarded full-library build, strict imported foundation fixture
and compiled blueprint declaration check; see
[the integrated verification](2026-10-28_lvv_integrated_verification.md).
This module imports no circuit assembly; the circuit layer therefore retains its
independence from the MPS layer.
