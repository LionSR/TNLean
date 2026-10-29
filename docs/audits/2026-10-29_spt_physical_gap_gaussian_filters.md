# Gaussian estimates from the physical SPT path

Issue #9879; parent tracker #2147. Baseline: main
`3af48c184`. Source: `Papers/1010.3732/paper_v3.tex:929–953`,
SPC11 Section II.F, and Appendix C, lines 2653–2717.

## Existing machinery and the remaining target

`ExactGroundPathTransferClass.lean` already obtains constant virtual class
from the exact physical path under a supplied strict uniform bound on
nonunit transfer eigenvalues of minimal unital injective representatives.
The compact sequence, support compression, periodic-ray limit and changing
minimal-dimension arguments are present. They do not require continuous
choices of those minimal representatives. Repeating these arguments or
assuming a clustering estimate would not derive the missing physical-gap
implication.

`FiniteRingLiebRobinson.lean` already proves the actual periodic dynamical
commutator estimate. QICLean's Gaussian filter modules derive Fourier
coefficients and dimension-free ground-vector decay under a projector gap.
TNLean's `Lattice/GaussianFilteredTerm.lean` and
`Lattice/GaussianFilteredGround.lean` already give the projected and centered
ground estimates directly from an eigenvalue gap, including an arbitrary
ground energy. `Lattice/GaussianFilteredLocality.lean` already performs the
short-time/tail integral splitting. The new work connects these existing
estimates to the actual physical path rather than reproducing them.

## Written physical consequences

`MPS/Preparation/FiniteRingGaussianFilter.lean` derives the Gaussian averaged
commutator estimate from the periodic nearest-neighbor bound and Gaussian
tail. There is no assumed short-time error parameter: the bound is the
explicit periodic expression with velocity `8 exp a`, support size `|X|`,
and cyclic support distance. The constants are independent of ring length
and local physical dimension. Hermiticity is derived from the cyclic sum;
zero ground energy, positivity and frustration freedom are not required.

The explicit choice `T = ℓ / (16 exp 1)`, `q = T Δ` for positive separation
`ℓ ≤ d(X,Y)` and `Δ > 0` gives
`‖[A_tilde,B]‖ ≤ 2‖A‖‖B‖ |X| exp(-ℓ/2)
+ 2‖A‖‖B‖ exp(-ℓ Δ/(32 exp 1))`.
The Gaussian spectral error at the same `q` is exactly the second
exponential. Thus the code writes the actual uniform exponential
short-time/tail balance, not just a formula with unspecified filter errors.

`MPS/Symmetry/ExactGroundPathGaussianFilter.lean` extracts one positive
physical gap constant `Δ` valid at every path parameter and ring length.
The least energies supplied by the independent gap and exact-ground-line
conditions are identified by their minimality. The exact MPS ground line
then identifies the entire ground eigenspace. This derives, for the actual
periodic vector `ψ`, both

- `‖(1-P) W_tilde ψ‖ ≤ ‖W‖ exp(-q/2) ‖ψ‖`, where `P` projects onto its line;
- `‖W_tilde ψ‖ ≤ Δ⁻¹ exp(-q/2) ‖[H,W] ψ‖` for centered `W`.

These statements are homogeneous in `ψ`; no continuous normalization or
phase is selected. Their hypotheses refer to the existing physical path,
the operator being estimated and its ordinary centering condition. No
transfer spectral bound, connected-correlation estimate, extra path
predicate or continuous canonical representative is introduced.

## Limits and next mathematical steps

`MPS/Preparation/TransferSpectrumFromCorrelations.lean` now writes the
conditional passage from an ordinary limiting-correlation rate `r > 0` to
the bound `|λ| ≤ r` for every nonunit transfer spectral value in a
trace-preserving gauge. It reuses the existing
`exists_limitCorrelator_eq_pow` observable construction: the chosen
correlator is exactly `λ^n`. The upper-bound prefactor and starting
separation may depend on the observable pair; neither needs a uniform
bound. If `|λ| > r`, then `(|λ|/r)^n` is unbounded, contradicting that
prefactor, also after the starting separation. This eliminates a genuine
asymptotic step without assuming the desired transfer bound.

A symmetric Gaussian low-pass filter suppresses both positive and negative
ground-transition frequencies. Its small commutator cannot by itself bound
an ordinary connected correlation: that argument needs a positive-frequency
separation or an equivalent spectral construction. The new code does not
claim exponential clustering. The remaining steps are:

1. Carry out that positive-frequency ground-state correlation calculation
   with the periodic dynamical estimate, obtaining exponential decay whose
   rate depends only on the uniform physical gap and interaction strength.
2. Pass the finite-ring connected bound to the existing limiting block
   contractions and transport it to a trace-preserving minimal gauge.
   The physical eigenvalue observers already exist, and the new rate lemma
   then removes all observable-dependent prefactors to give `q < 1`.
3. Apply the already implemented conditional exact-path class theorem.

The broader gap note
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex` remains accurate
about the outstanding clustering and transfer-bound obligations. These
Gaussian consequences are a necessary analytic slice, not completion of
the converse or its classification biconditional.

## Verification boundary

The user expressly requested source writing without Lean compilation or
builds. The new code is therefore an uncompiled proof candidate. Blueprint
entries remain `notready`, and #9879 remains open. Source/API inspection,
import generation, formatting and proof-integrity checks do not establish
kernel acceptance. No proof placeholders or persistent Lean fixtures are
introduced.
