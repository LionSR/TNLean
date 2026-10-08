# Rectangular preparation rates

## Source and scope

This extends the inhomogeneous paragraph of
[arXiv:2307.01696v2](https://arxiv.org/html/2307.01696v2) under an explicit
quantitative mixing assumption. The source's qualitative pair-error convergence
does not by itself imply an accuracy-dependent exponential rate. Supplemental
(S39) concerns the numerical open-boundary examples; (S42) reports numerical
exponential behavior for random inhomogeneous states.

The new physical theorem is
`MPSPreparation.exists_isPreparedInDepth_le_log_eventually_of_rectangular_mixing`.
Its inputs are actual `VaryingBondChain` tensors and density matrices on their
actual bond spaces. The density matrices can be singular. Their trace-one
condition excludes zero-dimensional bonds, and the existing chain structure
supplies the upper bound. The cutoff and depth constant precede accuracy and
ring length. No nonvanishing premise is imposed on the finitely many short rings.

## Norm and endpoints

For a map from `M_b` to `M_a`, `Matrix.linearMapMatrix` is its matrix in the
matrix-unit bases, with entry `T(E_kl)_ij` at row `(i,j)`, column `(k,l)`.
The explicitly scoped L2 operator norm is therefore the induced operator norm
for the unnormalized Hilbert–Schmidt norms on these matrix spaces.

The actual rectangular site maps compose in matrix-product order. For every
nonempty block, its padded product is exactly the product of its padded site
matrices. The empty rectangular product instead pads to a corner projection,
so the positive-length condition cannot be dropped.

If the actual interval reference is `X ↦ Tr(X) σ_a`, its padded reference is
`X ↦ Tr(P_b X) J_a σ_a J_a†`. Replacing this with a full-space trace reset is
incorrect. Its Gram reference is `(J_a σ_a J_a†)ᵀ ⊗ P_b`, and the positive
reference is `(J_a √σ_a J_a†)ᵀ ⊗ P_b`. Both endpoint corners are retained.

## Proof reuse

- The shared Gram/transfer comparison now accepts an exact entrywise
  reshuffling identity. The existing full-reset theorem remains a genuine
  specialization. The corner proof does not add a second reshuffling argument.
- One shared square-root Hölder argument covers the full and corner references.
- The existing ordered-product telescope is unchanged. Corner reset products
  collapse to their endpoint reference, whose norm is uniformly bounded.
- The mixed reference tensor remains the existing full fixed-point tensor.
  Thus the established cyclic pair identity is reused: the pair leaving a
  block uses the next block's reference.
- Existing coordinate-embedding and square-root identities moved, with proof
  bodies preserved, into the lightweight `BondEmbedding` module. There is no
  parallel padding functional-calculus development.
- Whole-ring transfer error controls the actual state's normalization.
  The normalized pair error feeds the existing `IsPairApproximable` consumer
  and physical preparation theorem. No new polar or circuit stack is introduced.
- Repeated singleton-partition and exponential-cutoff proofs were replaced by
  shared lemmas in `BlockSites` and `InjectivityCutoff`.

The constants in the intermediate comparison depend only on the common bond
bound. Consequently exponential actual-transfer error gives pair error bounded
by `C_D √K N exp(-rq/2)` and eventual physical depth `C log(N/ε)`.
The factor two in the exponent comes from the uniform square-root Hölder bound.

## Regression and locality scope

`TNLeanTest/RectangularPreparation.lean` uses a ring with bond dimensions
`1,2,1`. Its actual rectangular site maps are exact density resets. It checks
padding of a blocked tensor, a nonzero actual coefficient, and the failure of
the full reset on an unused input coordinate. The endpoint reference-product
identity is exercised with different corner dimensions.

Dimension-one bonds are allowed, but the physical circuit conclusion uses ring
adjacency. An open-line statement would require a separate proof that no gate
uses the wrap-around edge. No such conclusion is claimed here.

## Validation protocol

Changed declarations are checked with the repository's strict Lean options and
warnings as errors. Exact-body probes are provisional and are distinguished
from actual production-import checks. Warm artifacts are reused only after
source, toolchain, dependency and hash verification. Full exact-head CI remains
the final verification gate; no dependency library is cold-built locally.

The local strict checks cover the exact analytic declaration bodies, the
physical capstone, and the complete `1,2,1` regression through narrowed import
probes. The three new structural modules were also checked directly against
source-matched warm prerequisites. These are scoped checks, not a completed
build of the final production import graph. A bounded attempt to load the
larger analytic prerequisites was stopped after severe paging; no cold
Mathlib, QICLean, or Brouwer build was substituted.

Kernel dependency inspection of the capstone, rectangular padding estimate,
normalized pair bound, and actual-block padding identity found only
`propext`, `Classical.choice`, and `Quot.sound`. Source synchronization resolves
all blueprint references with no duplicated tags. The typed rectangular
blocking diagram was rendered and independently inspected. Full exact-head CI
must still check the final production imports and regression before merge.
