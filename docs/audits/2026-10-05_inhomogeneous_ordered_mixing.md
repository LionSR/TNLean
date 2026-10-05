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

The all-positive-length theorem also assumes that every periodic target is nonzero.
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
  The modules separate local ordered overlap, normalized chain error,
  the ordered-mixing preparation consequence, and the concrete Choi consumer. Existing lower-level results
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

## Direct Choi-domination consumer

`InhomogeneousDoeblinPreparation` composes the already proved actual-site
Doeblin Gram bound with the inverse Gram reshuffling, obtaining transfer
error `K (1-η)^length` before the actual chain, length, and parameter are
chosen. It then supplies the ordered-mixing capstone directly from trace
preservation, the common faithful stationary density matrix, and uniform
normalized-Choi domination of every actual site map. No new contraction
argument is introduced. The intermediate transfer bound retains `η=0,1`;
the preparation consequence requires `0<η≤1` and weakens domination to
`η/2` to handle the maximal endpoint without `log 0`. The regression
exercises `η=1`. A subsequent normalization closure splits off the first
site as `E₀=ηRσ+Q` with Q completely positive. The remaining ordered
product S is completely positive and trace preserving, hence
`E₀S=ηRσ+QS`. Nonnegative CP supertrace gives `‖φ_N‖²≥η>0` at every
positive length. Thus the concrete Choi consumer derives nonvanishing
instead of assuming it; the general ordered-mixing capstone keeps its
explicit nonzero-target hypothesis.
The direct consumer and both regressions passed the strict exact-declaration
check, with warnings as errors. The actual broad import closure still awaits
remote CI for the resulting publication head.

The first exact-head blueprint job passed the new diagram regression,
formatting and lint, but its full web render rejected the native `tenkzeq`
wrapper. The source displays now use the repository-supported
`tenkzequation`; the standalone structural test translates only that
presentation wrapper into a native scoped equation for the additional hard
signature check. Tensor nodes, wires, physical indices, and normalization
are unchanged.

## Small physical blocks and deficient polar support

The rate statements for all `q` are algebraic statements about the
positive-part state and the unit reference pairs. They do not assert a
full-input block isometry for every small `q`. The physical consumer is
`InhomogeneousUniformRate`: its choice of `b` includes `3D+1`, and its
`h3Dq` proof supplies `3D≤q` before it calls
`exists_isPreparedInDepth_of_isPairApproximable`.

For `d≥2`, that theorem proves `D²≤d^(3D)` and uses actual isometric
extensions `W_j Π_j = V_j` on blocks of length at least `3D`. The positive
part is supported on `Π_j`, so the overlap is preserved even if the Gram
matrix is rank deficient. No injectivity witness is inferred from a large
error bound. For `d≤1`, the normalized target has at most one configuration
and is prepared directly in depth zero. If the selected `q>N`, exact
preparation is used: a whole-ring block when `N≥3D`, and bounded-dimensional
synthesis only for the finite set `N<3D` (with `N=1` separate).

As a dimensional sanity check, `d=3,D=2` permits `d^1=3<D²=4` in the
algebraic rate hypothesis, but preparation does not request a four-column
isometry into that one-site space: its ordinary circuit blocks have at
least six sites, or its exact short-ring branch is used. The usual AKLT
transfer matrix has residual eigenvalue `-1/3` on the three Pauli directions
(see `MPS/Examples/AKLTCorrelation.lean`), giving periodic squared norm
`1+3(-1/3)^N`. Its one-site periodic vector is zero, so the general theorem
correctly requires a nonzero finite-ring replacement before claiming an
all-positive-length normalized family. This paragraph is a mathematical
sanity check, not a new compiled AKLT application.

Strict faithful Choi domination at a microscopic site is stronger: it
forces Choi rank `D²`, while a site with physical dimension `d` has Kraus
rank at most `d`. Thus unblocked AKLT cannot meet the direct actual-site
corollary's hypotheses. Such domination can hold after fixed blocking;
this corollary does not claim it from unblocked normality or individual
sitewise spectral gaps. The general ordered-mixing result is the one that
permits rank-deficient microscopic physical matrices.

## Eventual preparation without changing the family

The uniform-rate proof is generalized to a ring cutoff N₀. Its existing
all-positive-N API is preserved as the N₀=0 specialization; no structural
preparation import is changed. The general ordered-mixing estimate yields
`|‖φ_N‖²−1| ≤ Kn K exp(-rN)`. Choosing the uniform cutoff before N and ε
makes this at most 1/2, hence the original family is nonzero on that tail.
The new eventual physical preparation theorem applies there, with no
nonzero premise on short rings and no auxiliary-family patch. The actual
cutoff UniformRate module and the combined exact-body proof check pass.
