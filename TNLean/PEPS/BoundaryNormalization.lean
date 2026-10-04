/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.BoundaryIsometry
import TNLean.Algebra.ComplexSqrt

/-!
# Normalization of physical boundary maps

A specified cut map with Gram matrix \(M^\dagger M=cP\), where \(c>0\) and \(P\) is the
invariant-boundary projector, becomes isometric on the invariant subspace after division
by \(\sqrt c\). Normalizing the maps on both sides of a cut therefore gives the physical
boundary state of entropy \((b-1)\log|G|\) for \(b\) regular bonds.

These statements assume the Gram identities of the specified cut maps. Their geometric
identification with contractions of PEPS blocks is separate. The normalization is the
positive scalar convention used for isometric tensors in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Definition 6.1 and Lemma 6.2; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. The boundary entropy step is
Theorem 6.9, proof (`Papers/1001.3807/paper_v3.tex`, lines 2043–2072).

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Divide a specified regular boundary map by the square root of its positive Gram factor. -/
noncomputable def normalizedRegularBoundaryMap {n : ℕ} (c : ℝ)
    (M : Matrix α (Fin (n + 1) → G) ℂ) : Matrix α (Fin (n + 1) → G) ℂ :=
  (Real.sqrt c : ℂ)⁻¹ • M

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
/-- The normalized Schmidt matrix is the cut coefficient matrix multiplied by the three
square-root normalization factors. -/
theorem physicalRegularBoundarySchmidtMatrix_normalizedRegularBoundaryMap (n : ℕ)
    (M : Matrix α (Fin (n + 1) → G) ℂ) (N : Matrix β (Fin (n + 1) → G) ℂ)
    (cA cB : ℝ) :
    physicalRegularBoundarySchmidtMatrix n (normalizedRegularBoundaryMap cA M)
        (normalizedRegularBoundaryMap cB N) =
      ((Real.sqrt cA : ℂ)⁻¹ * (Real.sqrt cB : ℂ)⁻¹ *
        (Real.sqrt (Fintype.card G ^ n : ℝ) : ℂ)⁻¹) •
          (M * regularBoundaryProjector (n + 1) * N.transpose) := by
  simp only [physicalRegularBoundarySchmidtMatrix, normalizedRegularBoundaryMap,
    regularBoundarySchmidtMatrix, transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  simp only [mul_comm, mul_left_comm, mul_assoc]

omit [DecidableEq α] in
/-- Positive scalar normalization makes the map isometric on the invariant-boundary subspace. -/
theorem normalizedRegularBoundaryMap_conjTranspose_mul (n : ℕ)
    (M : Matrix α (Fin (n + 1) → G) ℂ) {c : ℝ} (hc : 0 < c)
    (hM : M.conjTranspose * M = (c : ℂ) • regularBoundaryProjector (n + 1)) :
    (normalizedRegularBoundaryMap c M).conjTranspose * normalizedRegularBoundaryMap c M =
      regularBoundaryProjector (n + 1) := by
  simp only [normalizedRegularBoundaryMap, conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, hM, smul_smul]
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
    Complex.ofReal_sqrt_inv_mul_self c hc.le,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul]

omit [DecidableEq β] in
/-- After normalization, the physical state obtained from the two specified cut maps has
entropy \(n\log|G|\) for \(n+1\) regular boundary bonds. -/
theorem vonNeumannEntropy_normalizedRegularBoundaryState (n : ℕ)
    (M : Matrix α (Fin (n + 1) → G) ℂ) (N : Matrix β (Fin (n + 1) → G) ℂ)
    {cA cB : ℝ} (hcA : 0 < cA) (hcB : 0 < cB)
    (hM : M.conjTranspose * M = (cA : ℂ) • regularBoundaryProjector (n + 1))
    (hN : N.conjTranspose * N = (cB : ℂ) • regularBoundaryProjector (n + 1)) :
    let ψ := physicalRegularBoundaryState n (normalizedRegularBoundaryMap cA M)
      (normalizedRegularBoundaryMap cB N)
    vonNeumannEntropy (partialTraceRight (vecMulVec ψ (star ψ)))
        (posSemidef_vecMulVec_self_star ψ).partialTraceRight.isHermitian =
      (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  dsimp only
  have hA := normalizedRegularBoundaryMap_conjTranspose_mul n M hcA hM
  have hB := normalizedRegularBoundaryMap_conjTranspose_mul n N hcB hN
  exact (vonNeumannEntropy_congr
    (partialTrace_physicalRegularBoundaryState n
      (normalizedRegularBoundaryMap cA M) (normalizedRegularBoundaryMap cB N) hB)
    _ _).trans
      (vonNeumannEntropy_physicalRegularBoundaryDensity n
        (normalizedRegularBoundaryMap cA M) hA)

end TNLean.PEPS
