# Inhomogeneous ordered mixing and normalized preparation

## Source and scope

The target is arXiv:2307.01696, “Inhomogeneous short-range correlated MPS,”
and the quantitative obligation recorded in
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`, “Sequence-level statement.”
The paper defines finite correlation by convergence of the pair error and
then states accuracy-dependent logarithmic preparation. Qualitative
convergence does not supply a uniform exponential rate.

The new theorem is a sufficient-condition result. It assumes actual ordered
transfer products on every positive nonwrapping interval in the chosen ring
ordering converge to one faithful trace-one reference state, with error
`K exp(-r length)` in the L² operator norm on the transfer matrices. `K,r`
are independent of the ring and interval. Separate eigenvalue bounds on
individual site maps are not substituted for this hypothesis.

The theorem also states that every positive-ring periodic target is nonzero.
This is required to interpret the paper's normalized quantum states; mixing
only excludes zero targets eventually and does not dispose of the short
rings by an implicit convention. Variable rectangular bonds, varying
reference states, and deriving the quantitative assumption from qualitative
finite correlation remain outside this result.

## Proof and constants

1. A bounded reshuffling of transfer-matrix entries gives the physical Gram
   error. The existing square-root Lipschitz bound at
   `σᵀ ⊗ I > 0` gives positive-polar error with a constant depending only on
   `D,σ`. No growing physical dimension enters that constant.
2. The mixed transfer map is linear in the positive factor. The existing
   ordered-product telescoping estimate around the fixed-point idempotent
   gives complex overlap error `C₀ M δ exp(C₀ M δ)`.
3. The actual whole-chain transfer trace equals the squared norm of the
   periodic state. Its distance from the rank-one transfer matrix bounds
   `|c_N² - 1|`. This is a separate whole-ring hypothesis, not a purported
   consequence of small block errors alone.
4. The existing vector normalization inequality combines those two errors.
   For `Mδ ≤ 1` the exponential is uniformly bounded; for `Mδ > 1`, error
   at most one suffices. The resulting bound is `C₁ M δ`.
5. The capstone chooses blocks `q ≤ length ≤ 2q`, so `M ≤ N`, obtains the
   supplied-rate interface with the *proved* bound `C₁ K N exp(-rq)`, and
   invokes the existing physical preparation theorem. The exact short-ring
   branch handles `q > N`. No block injectivity assumption is added.

The local overlap and normalization constants are quantified before the
physical dimension, tensor family, ring, partition, and error. The argument
keeps the first-order exponent `r`; it does not assert a quadratic rate.

## Reuse and import boundary

- Reuses the exact ordered transfer identity from `MPS.Chain.Transfer`.
- Reuses `CStarSqrtLipschitz`, `NormedRingTelescoping`, the fixed-point pair
  identities, and the vector normalization inequality.
- Reuses `InhomogeneousUniformRate` and its exact short-chain branch for
  physical circuit synthesis. There is no assumption of pair approximation
  in the new capstone's signature.
- `InhomogeneousApproximationError` explicitly imports `ApproximationError`
  for its vector inequality. This quantitative consumer does not reintroduce
  the rate-dependent import into the generic preparation modules isolated
  by the preparation import-boundary change.
- No new parallel state predicate or generic channel library is introduced.
  The three modules separate local ordered overlap, normalized chain error,
  and the physical preparation consequence. Existing lower-level results
  are not copied into production files.

## Diagrams and verification

The source-facing diagrams show the actual two-site contraction and polar
factorization, the unnormalized mixed-polar overlap with an entrywise
conjugated reference row, and physical isometries acting independently on
one normalized-reference ring. The surrounding equations identify the
normalization factor on the target, not on the unit pairs.

`test_tenkz_ordered_mixing.py` checks the declared contractions, all five
rendered panel boundaries, tensor/wire counts, reference-row conjugation,
and the absence of virtual bonds between independent physical isometries.
The full tenkz event audit reports no hard findings or advisories. The
standalone XeLaTeX PDF was rendered and visually inspected. An unintended
upper virtual ring in an early diagram was removed; the regression checks
that exact failure mode.

Local Lean verification is deliberately distinguished from full import
verification. The exact new declaration bodies and an exact-mixing
regression were checked together with the package's full linter options,
using source-copied dependencies and certified structural artifacts.
`Chain.Transfer` and `InhomogeneousUniformRate` were also compiled as actual
modules. The broad production imports are checked by exact-head pull-request
CI; the local declaration check is not described as a complete library build.
