# Actual finite Heisenberg action of supplied MPU standard form

Issues #7013 and #7040. Base current main:
`fef336fe11c51e82136111e58af90e22cfbaf9e6`. This is an isolated source
slice, not a new quasi-local/QCA object or an assumption of compatibility.

The scout found main already contains the closed positive-length periodic
circuit theorem, open three-block intertwiner, and arbitrary original-site
residual-word intertwiner. The missing next step is assembling those
coefficient identities into an actual full finite conjugation, rather
than duplicating gate cancellation or assuming a compatible action.

`TwoSiteFiniteHeisenberg.lean` provides explicit complete input and output
configuration equivalences for length 3+n of the supplied blocked tensor.
It reindexes the actual full periodic MPO using those equivalences. The
middle-pair input observable is the right Kronecker embedding, and the
output is the actual twoLinkOutputObservable with identity on every
exterior index and the whole arbitrary tail.

The existing open-trace intertwiner proves the full matrix intertwining
identity entrywise. Actual periodic MPO unitarity follows from the supplied
two-site standard form. Multiplying by its adjoint therefore yields the
actual finite Heisenberg formula, with no support/compatibility conclusion
supplied as a new premise. Every n≥0 is covered, and the periodic seam
remains inside the trace. The output coefficient is independent of n;
only the identity spectator's ambient dimension changes.

The source now also includes actual original-site finite conjugation for
N=p+6k+s>1 with arbitrary original prefix and suffix lengths p,s. The complete
middle coordinates use the actual direct two-site block equivalence and
original blocked configuration equivalence. Each full original-MPO entry
is the existing residual three-block coefficient; its open intertwiner
therefore lifts to the full operator. Original U.IsMPU supplies unitarity.
There is no whole-chain divisibility or residual-compatibility premise.
The same local output is obtained for every p,s, with identities on all
original exterior coordinates. This removes the complete-block ambient
length restriction for this local observable.

The source additionally defines the fixed original-site input and output
window matrices and proves `mpo_bufferedWindow_conjugation`: the actual
periodic MPO sends the identity-tensor inclusion of the fixed input to the
identity-tensor inclusion of the fixed output for every original prefix
and suffix. The coordinate proof splits equality of the complete exterior
index into equality of its residual-word and within-window parts. The
output matrix itself is independent of the ambient dimensions.

This is still not the full source stabilization theorem. It does not yet
assemble arbitrary buffered interval anchors or arbitrary supported
observables; no compatible-local-action datum,
induced QCA, radius 4D⁴, or MPU/QCA index comparison is claimed. The exact
scope and elimination plan are in
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.

Source: arXiv:1703.09188, StandardForm/SF lines603–622 and
finite-conjugation eq:appendix-1 lines2300–2306. The reusable current
local-circuit API has uniform physical dimensions and square bond gates;
the standard form passes through unequal ordered ℓ/r intermediate legs.
The present proof reuses the supplied rectangular open contraction and
therefore does not assume a homogeneous-intermediate circuit presentation.

Native source/import/prose/format/whitespace/integrity checks only.
No local Lean invocation/build/checkdecls or cache mutation. New Blueprint
entry remains notready pending hosted verification and integration.
