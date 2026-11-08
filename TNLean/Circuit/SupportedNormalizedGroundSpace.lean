/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedGroundSpace
import QICLean.Analysis.SpectralFilter.PositiveReplacement
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Normalized simultaneous regional ground vectors

The common regional ground vector derived from disjoint supports can be
normalized without changing any shifted ground equation. The conclusion is
in raw matrix coordinates, with its squared norm written as a star dot
product, for the finite-dimensional ground-energy estimates.

Source: AKLV, arXiv:1301.1162v1, Section 6.1, the regional normalization
preceding Theorem 6.1.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder BigOperators

namespace QuantumCircuit

/-- Three supported Hermitian operators on disjoint regions have an actual
normalized common minimum-energy vector. The individual ground energies
are their derived minimum eigenvalues, and no common ground vector or
normalization witness is assumed. Source: AKLV, arXiv:1301.1162v1,
Section 6.1 normalization. -/
theorem exists_normalized_common_ground_of_disjoint
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero d]
    {S T R : Set ι} (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    {A B C : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hsA : A ∈ supportedOperators d S) (hsB : B ∈ supportedOperators d T)
    (hsC : C ∈ supportedOperators d R) :
    ∃ v : (ι → Fin d) → ℂ, star v ⬝ᵥ v = 1 ∧
      (A - (minEigenvalue hA : ℂ) • 1) *ᵥ v = 0 ∧
      (B - (minEigenvalue hB : ℂ) • 1) *ᵥ v = 0 ∧
      (C - (minEigenvalue hC : ℂ) • 1) *ᵥ v = 0 := by
  obtain ⟨v, hv, hAv, hBv, hCv⟩ :=
    exists_common_ground_of_disjoint hST hSR hTR hA hB hC hsA hsB hsC
  let vE : EuclideanSpace ℂ (ι → Fin d) := WithLp.toLp 2 v
  have hvE : vE ≠ 0 := by
    intro hzero
    apply hv
    simpa [vE] using congrArg WithLp.ofLp hzero
  let w := NormedSpace.normalize vE
  have hw : ‖w‖ = 1 := NormedSpace.norm_normalize hvE
  have hkill (M : Matrix (ι → Fin d) (ι → Fin d) ℂ) (hMv : M *ᵥ v = 0) :
      M *ᵥ WithLp.ofLp w = 0 := by
    change M *ᵥ WithLp.ofLp (‖vE‖⁻¹ • vE) = 0
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul]
    change ‖vE‖⁻¹ • (M *ᵥ v) = 0
    rw [hMv, smul_zero]
  exact ⟨WithLp.ofLp w, SpectralFilter.star_dotProduct_self_of_norm_eq_one hw,
    hkill _ hAv, hkill _ hBv, hkill _ hCv⟩

end QuantumCircuit
