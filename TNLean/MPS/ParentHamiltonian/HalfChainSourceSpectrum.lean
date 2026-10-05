/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.HalfChainCanonicalSpectrum
import TNLean.MPS.CanonicalForm.PGVWC07CanonicalForm

/-!
# Half-chain convergence from the source canonical hypotheses

The three one-block TI canonical conditions of PGVWC07 are unitality,
a faithful diagonal dual fixed point, and a scalar fixed-point space.
Together with Condition C2 and its spectral-radius-one normalization, these
imply normality of the original tensor.
Thus the half-chain spectrum theorem applies without assuming irreducibility
or a complementary spectral gap as additional hypotheses.

**Scope restriction (one canonical block):** this result assumes an explicit
one-block canonical tensor. Reduction of a general weighted canonical
representation under C2 to its dominant block remains separate; see
docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 4 (lines 742–759),
Condition C2 and its one-block context (lines 954–969), and Theorem 6
(lines 987–993). The dual fixed point is normalized to trace one.
-/

open Filter
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator Topology

namespace MPSTensor

variable {d D : ℕ}

/-- The one-block TI canonical hypotheses and Condition C2 imply normality.
Irreducibility follows from the faithful dual fixed point and the scalar
fixed-point clause, not from bare peripheral-eigenvalue uniqueness.
Source: PGVWC07, Theorem 4, lines 742–759, and Condition C2, lines 954–963. -/
theorem isNormalTensor_of_pgvwc07_canonical_c2
    (A : MPSTensor d D) (lam : Fin D → ℝ)
    (hlam : ∀ a, 0 < lam a) (htr : ∑ a, lam a = 1)
    (hU : ∑ i, A i * (A i)ᴴ = 1)
    (hfix : ∑ i, (A i)ᴴ * (Matrix.diagonal fun a => (lam a : ℂ)) * A i =
      Matrix.diagonal fun a => (lam a : ℂ))
    (hscalar : ∀ X, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1)
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 → μ = 1) :
    IsNormalTensor A := by
  have hD : D ≠ 0 := by
    intro h
    subst D
    simp at htr
  let : NeZero D := ⟨hD⟩
  have hOne : Kraus.transferMap A 1 = 1 := by
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hU
  have hΛ : (Matrix.diagonal fun a => (lam a : ℂ)).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun a => Complex.zero_lt_real.mpr (hlam a)
  have hΛfix : Kraus.transferMap (fun i => (A i)ᴴ)
      (Matrix.diagonal fun a => (lam a : ℂ)) = Matrix.diagonal fun a => (lam a : ℂ) := by
    simpa only [Kraus.transferMap_apply, Matrix.conjTranspose_conjTranspose] using hfix
  exact ⟨isIrreducibleFamily_of_unital_of_dualFixedPoint A hU hΛ hΛfix hscalar,
    hRadius,
    isPrimitive_of_unique_norm_one (Kraus.transferMap A) 1 hOne one_ne_zero hC2⟩

/-- Half-chain interpretation of the diagonal dual fixed point from the
source's explicit one-block canonical hypotheses and Condition C2. The reduced density
is that of the original tensor, normalized by its actual finite-ring norm;
ordered eigenvalues include multiplicities and trailing zero padding.
Source: PGVWC07, Theorem 6, lines 987–993, with the TI canonical conditions
of Theorem 4, lines 742–759, and Condition C2, lines 954–963. -/
theorem tendsto_halfChainEigenvalues_of_pgvwc07_canonical_c2
    (A : MPSTensor d D) (lam : Fin D → ℝ)
    (hlam : ∀ a, 0 < lam a) (htr : ∑ a, lam a = 1)
    (hU : ∑ i, A i * (A i)ᴴ = 1)
    (hfix : ∑ i, (A i)ᴴ * (Matrix.diagonal fun a => (lam a : ℂ)) * A i =
      Matrix.diagonal fun a => (lam a : ℂ))
    (hscalar : ∀ X, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1)
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 → μ = 1)
    (k : ℕ) :
    Tendsto (fun L => halfChainEigenvalues A L k) atTop
      (𝓝 ((posSemidef_halfChainSpectrumLimit lam
        (fun a => (hlam a).le)).isHermitian.paddedEigenvalues k)) :=
  tendsto_halfChainEigenvalues_unital A
    (isNormalTensor_of_pgvwc07_canonical_c2 A lam hlam htr hU hfix hscalar hRadius hC2)
    lam (fun a => (hlam a).le) htr hU hfix k

end MPSTensor
