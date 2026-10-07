# Varying positive semidefinite references

## Result and source boundary

For fixed square bond dimension D, actual tensor families A_N, and arbitrary
site- and ring-dependent PSD trace-one references σ_(N,i), uniform actual
ordered-transfer error K exp(-r length) towards the reset at the interval's
first site gives eventual physical logarithmic-depth preparation of the
original family. Constants and cutoff precede N and accuracy. The theorem
has no common-reference, faithfulness, spectral-floor, transport, stationarity,
nonzero-target, or supplied pair-approximation premise.

This strengthens the explicitly quantitative sufficient condition developed
for arXiv:2307.01696, not the paper's qualitative definition. The source's
inhomogeneous paragraph allows varying nearest-neighbor pairs, but does not
supply a uniform exponential product bound. Rectangular bond spaces and the
qualitative-to-quantitative implication remain open scope items. The sharper
common faithful-reference statement is preserved unchanged.

## Proof and exact conventions

- Reuse existing `CFC.norm_sqrt_sub_sqrt_le` from CStarSqrtHolder. No square-root
  theorem is reintroduced. Gram reshuffling gives dimension-only polar error
  K_D sqrt(δ), including singular references.
- Bound reset matrices and mixed-transfer operator norms uniformly using
  compactness of all density matrices. The mixed map is made complex-linear
  in a matrix S by putting S-adjoint in its right tensor argument; evaluating
  at the Hermitian square root restores the actual reference tensor.
- Extend existing ordered telescoping to varying reference factors with all
  contiguous subproducts bounded. Existing constant-reference statements now
  specialize the general theorem without changing their signatures.
- Reset composition satisfies R_σ R_τ = R_σ whenever trace τ = 1. Every
  nonempty reference product therefore has trace one and a uniform norm bound.
- In the tensor convention F_j^(l,r)=sqrt(σ_j)|l><r|, cyclic contraction is
  the product of sqrt(σ_(j+1))_(r_j,l_(j+1)). The pair leaving j uses j+1.
  The exact heterogeneous mixed-overlap identity preserves complex conjugation.
- Whole-ring transfer trace independently controls target norm squared. In
  the small-error range M sqrt(δ) ≤ 1, δ ≤ sqrt(δ); in the complementary range
  normalized error ≤ 1. Thus pair error ≤ C_D M sqrt(δ).
- Balanced blocks give C_D sqrt(K) N exp(-rq/2). Reuse the existing cutoff
  uniform-rate physical consumer, its isometric support extensions, and its
  exact q>N fallback. Whole-ring convergence gives squared norm at least 1/2
  beyond a uniform cutoff; no tensor in the original family is patched.

## Concrete tests and diagrams

The regression uses distinct references diag(1,0) and diag(0,1), checks PSD,
trace one, zero determinant, singleton reset trace and pair normalization,
and a two-block coefficient equal to one. The incorrectly unshifted pair
coefficient is zero for the same physical configuration. This detects a
cyclic index error that equal references would hide.

The new two-block Tenkz equality exposes all four physical indices and the
single virtual ring. Its right side has independent square-root pair matrices
with the shifted labels. The existing structural test now audits seven panels,
including exact explicit wires and the shifted row/column labels. The full
event audit has no hard or advisory findings. A standalone XeLaTeX PDF was
rendered and visually inspected; it shows no extraneous contraction.

## Validation status

The actual generic algebra module passes the strict package options and its
empty/two-factor checks. The complete new tensor proof bodies, eventual
physical theorem, and all concrete regression declarations pass a combined
strict exact-source-body check with warnings as errors. This check uses
source-copied exact prerequisites and the certified source-consistent structural
overlay from the earlier preparation work; it is not a full production import
build. The existing #8682 dependency is kept on its unchanged publication head
while its full Lean CI runs. Separate extension publication and complete
actual-import CI remain pending.

The local probe was trimmed to omit unused heavy Choi/CP imports after slow
import-only experiments; no theorem hypothesis, proof option, or standard
linter was weakened to obtain the successful check.
