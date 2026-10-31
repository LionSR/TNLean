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
command was run; hosted CI is the compilation check. The Blueprint entries of
the new declarations are marked formalized. This draft is stacked on the independently verified
intrinsic-trace draft #10311; it does not depend on the local-criterion drafts.

## Commuting weighted nilpotent elimination

`Algebra/StabilizedWeightedTrace.lean` now proves the needed linear-algebra
step on the existing QIC `Matrix.StabilizedRankOneData`. For a stabilized
matrix `E`, each positive power minus `P = E^J` is nilpotent, since it is
`E^k * (1 - P)` and the complementary idempotent kills its `J`th power.
A weight commuting with `E` commutes with this transient; Mathlib's commuting
nilpotent-product theorem and nilpotent trace theorem then give
`trace (F * E^k) = trace (F * E^J)` for every positive `k`.

This is not an MPU statement with an assumed spectral witness. The actual
canonical comparison of the twisted transfer to the normalized transfer
still has to be derived before this generic algebra lemma can be used to
claim intrinsic parity. The existing green canonical necessity proof cancels
the even-family virtual phase before constructing its local sign; it does
not identify those signs. The constants must therefore remain separate in
the continuation. Source parity can use the first two intrinsic values if a
formula `τₖ = C η^k` with `η² = 1` is derived; it does not require or assert
`η = τ₁` or `C = 1`.

The two new algebra declarations have a scope-matching Blueprint entry;
there are now eight new public declarations in this draft. No local Lean/Lake
commands were run.
