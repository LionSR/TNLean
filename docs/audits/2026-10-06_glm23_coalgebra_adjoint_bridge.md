# GLM23 star-coalgebra adjoint bridge

## Source and scope

GLM23, arXiv:2203.12563v3, `REsubmission.tex` lines 1236–1320, works with
representations of C*-weak Hopf algebras. Its cited construction is Molnár et
al., [arXiv:2204.05940v1](https://arxiv.org/pdf/2204.05940v1), Section 4 and
Section 5.5. Definition 5.8 requires a conjugate-linear involution satisfying

\[
\Delta(x^*)=(*\otimes*)\Delta(x).
\]

This coproduct law preserves the order of the factors. Proposition 5.4 and
the discussion following it identify physical adjoints of represented MPOs;
the text on page 37 explicitly extends the identity to arbitrary boundaries.
The dual C*-algebra involution in equation (5.38) also uses the antipode. The
intrinsic involution used below is a different operation and is not claimed
to be that dual C*-algebra involution.

The bridge isolates exactly the standard coalgebra, star-module and
representation data needed for arbitrary-boundary adjoints. It does not
construct a C*-weak Hopf algebra or assume that one has already been built in
TNLean. It does not supply a realization of a particular mixed tensor.
Examples without the required physical star data do not contradict the
paper's C*-weak-Hopf statement.

The representation conventions are explicit in Section 4: a multiplicative
map that does not send the unit to the identity is not a representation
(page 14, preceding Definition 4.2), and the MPO construction chooses an
injective representation of the dual (immediately following Definition
4.2). Thus injectivity and unitality of the virtual representation here are
source hypotheses, including the unit law used for the empty-chain result.

## Mathematical construction

Let `H` be a complex coalgebra with a conjugate-linear involution satisfying
the displayed coproduct law. Let

\[
\phi:H\longrightarrow M_d(\mathbb C),\qquad
\psi:H^*\longrightarrow M_D(\mathbb C)
\]

be a star-preserving linear map and an injective unital algebra
representation of the convolution dual, respectively. For the physical
coefficients `fᵢⱼ(x) = φ(x)ᵢⱼ`, define the actual tensor by `Tᵢⱼ = ψ(fᵢⱼ)`.
No multiplicativity or injectivity of the physical map is required by this
step; those additional properties are available in the source construction.

1. Define `κ(f)(x) = conj(f(x*))` using Mathlib's intrinsic star on
   `WithConv (H →ₗ[ℂ] ℂ)`. Tensor induction and the coproduct law show that
   `κ(fg) = κ(f)κ(g)` in the same order. Involutivity supplies a multiplicative
   equivalence, which preserves the convolution unit. Thus the unit law is
   derived without adding a counit-star premise.
2. Physical star compatibility gives `κ(fᵢⱼ) = fⱼᵢ`. Ordered products of these
   coefficients therefore swap their physical indices without reversing the
   spatial order.
3. For a virtual boundary `X`, the functional
   `ℓₓ(f) = conj(tr(X ψ(κ(f))))` is complex linear. Injectivity of `ψ` lets it
   extend to a linear functional `θ` on all virtual matrices. Nondegeneracy of
   the matrix trace pairing supplies a matrix `Y` with `θ(M) = tr(YM)`.
4. Consequently `tr(Y ψ(f)) = conj(tr(X ψ(κ(f))))` for every dual element `f`.
   Apply this to each ordered coefficient product. The same `Y` gives
   `(Oⁿₓ)† = Oⁿᵧ` simultaneously at all lengths `n ≥ 0`.

The choice of `Y` occurs before the length quantifier. In the empty-word
case, preservation of the unit gives `tr(Y) = conj(tr(X))`.

## Implemented declarations

- `Coalgebra.dualStar_mul`
- `Coalgebra.dualStarMulEquiv`
- `Coalgebra.dualStar_one`
- `MPOTensor.dualCoefficient`
- `MPOTensor.ofDualRepresentation`
- `MPOTensor.star_dualCoefficient`
- `MPOTensor.evalWord_ofDualRepresentation`
- `MPOTensor.star_dualCoefficient_prod`
- `MPOTensor.exists_boundary_trace_dualStar`
- `MPOTensor.exists_adjointBoundary_of_dualRepresentation`
- `MPOTensor.isBoundaryAdjointClosed_of_dualRepresentation`
- `MPOTensor.IsBoundaryCompatible.parentInteractionES_commute_of_dualRepresentation`
- `MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_of_dualRepresentation`

The existing `MPOTensor.IsBoundaryAdjointClosed` definition has been moved
unchanged into `MPS/MPDO/BoundaryAdjointClosed.lean`, so neither sufficient
criterion needs to import the other. Its former defining module imports the
new foundation and retains all its other declarations.

The local canonical-parent corollary uses arbitrary-boundary compatibility
and derived adjoint closure. The periodic corollary additionally retains
`commutingBoundaryAlgebra`, needed for cyclic windows crossing the boundary.
Neither conclusion assumes parent commutation.

## Remaining work outside this bridge

- Construct the full source C*-weak-Hopf representation package.
- Prove that the specific mixed MPO tensor is realized by that package.
- Construct and normalize the canonical integral and its averaging operation.
- Relate the weak-Hopf average to the canonical ambient complementary
  projection, with the support-unit distinction retained.

No assertion here removes these remaining gaps or proves nonzeroness of the
uncompleted weak-Hopf average.
