/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MixedSequentialFactorization
import QICLean.Algebra.OrthogonalProjection

/-!
# Mixed sequential preparation on the polar support

For a non-injective blocked tensor, the polar map is a partial isometry.
Choosing orthonormal coordinates on its actual support gives an isometry,
which can be prepared by two inward sweeps and a central isometry. This
implements the pseudoinverse and central-input variants together, without
assuming injectivity or a full-dimensional input.

## References

* Malz, Styliaris, Wei and Cirac, arXiv:2307.01696, footnotes 3 and 4 to equations (13)–(15).
-/

open scoped Matrix BigOperators Kronecker

namespace MPSPreparation

variable {d D : ℕ}

/-- Changing the input coordinates commutes with attaching the input at the centre. -/
theorem centralInputMatrix_mul {s t : ℕ} (A : MPSTensor d D)
    (G : Matrix (Fin (D * D)) (Fin s) ℂ) (J : Matrix (Fin s) (Fin t) ℂ) :
    centralInputMatrix A (G * J) = centralInputMatrix A G * J := by
  ext z x
  simp [centralInputMatrix, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- A change of input coordinates does not alter either outer sweep. -/
theorem mixedProductMap_mul {l r s t : ℕ} (L : MPSChainTensor d D l)
    (A : MPSTensor d D) (R : MPSChainTensor d D r)
    (G : Matrix (Fin (D * D)) (Fin s) ℂ) (J : Matrix (Fin s) (Fin t) ℂ) :
    mixedProductMap L A R (G * J) = mixedProductMap L A R G * J := by
  simp only [mixedProductMap, centralInputMatrix_mul, Matrix.mul_assoc]

/-- The polar partial isometry admits a central input factor even without injectivity. -/
theorem exists_mixedPolarIsoMatrix_eq_mixedProductMap {l r : ℕ}
    (L : MPSChainTensor d D l) (A : MPSTensor d D) (R : MPSChainTensor d D r) :
    ∃ G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ,
      mixedPolarIsoMatrix L A R = mixedProductMap L A R G := by
  obtain ⟨G, hG⟩ := MPSTensor.exists_polarIsoMatrix_eq_sum
    (MPSChainTensor.blockTensor (mixedChain L A R))
  refine ⟨G, ?_⟩
  ext σ x
  change MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor (mixedChain L A R))
      ((MPSTensor.decodeBlockEquiv d (l + (r + 1))).symm
        (mixedConfigurationEquiv d l r σ)) x = _
  rw [hG, mixedProductMap_apply]
  simp only [MPSChainTensor.blockTensor_decodeBlockEquiv_symm, eval_mixedChain]

/-- Splitting and reversing physical coordinates preserves the polar support Gram matrix. -/
theorem conjTranspose_mixedPolarIsoMatrix_mul {l r : ℕ}
    (L : MPSChainTensor d D l) (A : MPSTensor d D) (R : MPSChainTensor d D r) :
    (mixedPolarIsoMatrix L A R)ᴴ * mixedPolarIsoMatrix L A R =
      MPSTensor.polarSupportMatrix (MPSChainTensor.blockTensor (mixedChain L A R)) := by
  simp only [mixedPolarIsoMatrix, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv,
    MPSTensor.conjTranspose_polarIsoMatrix_mul_polarIsoMatrix]
  rfl

/-- Restricting the polar input to any orthonormal support coordinates gives a genuine
central isometry and isometric inward chains, with every bond bounded by `D²`. -/
theorem exists_mixed_sequential_polarIsoMatrix_on_support {l r s : ℕ} (hD : 0 < D)
    (L : MPSChainTensor d D l) (A : MPSTensor d D) (R : MPSChainTensor d D r)
    (J : Matrix (Fin (D * D)) (Fin s) ℂ) (hJ : J.IsIsometry)
    (hPJ : MPSTensor.polarSupportMatrix (MPSChainTensor.blockTensor (mixedChain L A R)) *
      J = J) :
    HasMixedSequentialFactorization hD (mixedPolarIsoMatrix L A R * J) := by
  have hV : (mixedPolarIsoMatrix L A R * J).IsIsometry := by
    change (mixedPolarIsoMatrix L A R * J)ᴴ * (mixedPolarIsoMatrix L A R * J) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (mixedPolarIsoMatrix L A R)ᴴ,
      conjTranspose_mixedPolarIsoMatrix_mul, hPJ]
    exact hJ
  obtain ⟨G, hG⟩ := exists_mixedPolarIsoMatrix_eq_mixedProductMap L A R
  rw [hG, ← mixedProductMap_mul] at hV ⊢
  exact exists_mixed_isometric_factorization hD L A R _ hV

/-- Every blocked tensor, including a non-injective one, has a mixed sequential
factorization on its actual polar support. The input has exactly that support,
and multiplication by its adjoint reconstructs the full polar partial isometry. -/
theorem exists_mixed_sequential_polar_support_of_split {l r : ℕ} (hD : 0 < D)
    (L : MPSChainTensor d D l) (A : MPSTensor d D) (R : MPSChainTensor d D r) :
    ∃ (s : ℕ) (J : Matrix (Fin (D * D)) (Fin s) ℂ),
      s ≤ D * D ∧ J.IsIsometry ∧
      J * Jᴴ = MPSTensor.polarSupportMatrix
        (MPSChainTensor.blockTensor (mixedChain L A R)) ∧
      HasMixedSequentialFactorization hD (mixedPolarIsoMatrix L A R * J) ∧
      (mixedPolarIsoMatrix L A R * J) * Jᴴ = mixedPolarIsoMatrix L A R := by
  let B := MPSChainTensor.blockTensor (mixedChain L A R)
  have hP : IsOrthogonalProjection (MPSTensor.polarSupportMatrix B) :=
    ⟨MPSTensor.isHermitian_polarSupportMatrix B, MPSTensor.polarSupportMatrix_mul_self B⟩
  obtain ⟨s, J, hJ, hRange⟩ := hP.exists_range_isometry
  have hs : s ≤ D * D := by
    calc
      s = Matrix.rank (Jᴴ * J) := by rw [hJ]; simp
      _ ≤ Matrix.rank Jᴴ := Matrix.rank_mul_le_left _ _
      _ ≤ D * D := by simpa using Matrix.rank_le_card_width Jᴴ
  have hPJ : MPSTensor.polarSupportMatrix B * J = J := by
    rw [← hRange, Matrix.mul_assoc, hJ, Matrix.mul_one]
  refine ⟨s, J, hs, hJ, hRange,
    exists_mixed_sequential_polarIsoMatrix_on_support hD L A R J hJ hPJ, ?_⟩
  rw [Matrix.mul_assoc, hRange]
  exact Matrix.mul_eq_self_of_conjTranspose_mul_self_eq
    (conjTranspose_mixedPolarIsoMatrix_mul L A R) hP.1 hP.2

/-- The polar partial isometry of any site-dependent chain can be prepared on its
actual support by inward isometric sweeps meeting at any chosen physical site.
Both endpoint choices are included; no injectivity or nonzero-rank hypothesis is needed. -/
theorem exists_mixed_sequential_polar_support {l r : ℕ} (hD : 0 < D)
    (A : MPSChainTensor d D (l + (r + 1))) :
    ∃ (s : ℕ) (J : Matrix (Fin (D * D)) (Fin s) ℂ),
      s ≤ D * D ∧ J.IsIsometry ∧
      J * Jᴴ = MPSTensor.polarSupportMatrix (MPSChainTensor.blockTensor A) ∧
      HasMixedSequentialFactorization hD
        ((Matrix.reindex ((MPSTensor.decodeBlockEquiv d (l + (r + 1))).trans
          (mixedConfigurationEquiv d l r).symm) (Equiv.refl _)
            (MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A))) * J) ∧
      (MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A) * J) * Jᴴ =
        MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A) := by
  obtain ⟨L, M, R, hA⟩ := exists_eq_mixedChain A
  obtain ⟨s, J, hs, hJ, hRange, hFac, _⟩ :=
    exists_mixed_sequential_polar_support_of_split hD L M R
  refine ⟨s, J, hs, hJ, by simpa only [hA] using hRange,
    by simpa only [mixedPolarIsoMatrix, hA] using hFac, ?_⟩
  rw [Matrix.mul_assoc, hRange, hA]
  exact Matrix.mul_eq_self_of_conjTranspose_mul_self_eq
    (MPSTensor.conjTranspose_polarIsoMatrix_mul_polarIsoMatrix _)
    (MPSTensor.isHermitian_polarSupportMatrix _)
    (MPSTensor.polarSupportMatrix_mul_self _)

end MPSPreparation
