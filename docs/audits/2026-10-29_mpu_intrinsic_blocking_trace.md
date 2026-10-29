# Intrinsic blocked traces for #7111

Source: arXiv:1703.09188, `eq:sigma-from-trace`, lines 1595–1610, and
`prop:sigma1-and-sigma2-equal`, lines 1633–1733.

`TimeReversalTwistedTransfer.lean` derives an actual finite-dimensional
expression for the intrinsic trace of every physical block. It defines only
the normalized diagonal of the existing product tensor `mulTensor U U`,
reindexed to the two product bond coordinates. Thus its entries sum
`d⁻¹ ∑ i j, U i j ⊗ U j i`.

The existing normalized-diagonal power expansion and actual product-tensor
word contraction yield normalized sums of opposite open-word Kronecker
products. The existing QIC swap-trace identity contracts each summand to the
trace of the product of its two open words. Explicit physical decoding then
identifies this with the intrinsic trace of the actual blocked tensor.
No frequency multiplier, spectral datum, gate factor, local certificate,
canonical form, or symmetry witness is supplied as a premise. The identities
hold also at zero blocking length and in zero dimensions under the existing
algebraic inverse convention.

The same word expansion shows that the twisted transfer commutes with bond
exchange: swapping the factors exchanges the two physical summation words.

This is a prerequisite, not the source blocking-parity proposition. It does
not construct the printed blocked gates, prove their local relations, derive
the sequential unwinding equation, or identify a virtual sign with the first
intrinsic sign. A possible subsequent canonical argument compares the actual
twisted transfer with the normalized transfer via the existing even-family
adjoint gauge, then removes the nilpotent transient from a commuting weighted
trace. If that gives `σₖ = η^(k−1) σ₁`, the virtual sign `η` must remain distinct
from `σ₁` unless their equality is separately proved. No `σₖ = σ₁^k` claim is
made here. #7111 remains open.

Validation is source-only: pinned API review, existing-operation reuse,
generated imports, declaration coverage, theorem roles, reader-facing prose,
TeX formatting, tactic scan, width/integrity and diff checks. No local Lean/Lake
command was run. All six new public declarations remain `notready` pending
hosted verification. This draft is stacked on the independently verified
intrinsic-trace draft #10311; it does not depend on the local-criterion drafts.
