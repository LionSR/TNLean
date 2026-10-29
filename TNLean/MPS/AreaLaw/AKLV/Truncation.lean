/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.GroundStateTail
import QICLean.Analysis.CommutingHermitian
import QICLean.Analysis.CfcConjugation

/-!
# Two-sided energy truncation

The truncation used by AKLV, arXiv:1301.1162v1, Sections 6.1 and 6.3,
clips the two exterior blocks separately, leaving the middle terms intact.
It agrees with the original Hamiltonian below the cutoff of the
disconnected Hamiltonian. The clipping operation is QICLean's
`Matrix.energyTruncation`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Positive semidefinite matrices give positive operators on the
Euclidean Hilbert space. This transports the quadratic order used
throughout AKLV, arXiv:1301.1162v1, Section 6.3. -/
theorem PosSemidef.isPositive_toEuclideanCLM {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (toEuclideanCLM (n := n) (𝕜 := ℂ) A).IsPositive :=
  (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
    (isPositive_toEuclideanLin_iff.mpr hA)

/-- Clipping a commuting operator below a larger operator does not change
its action on the larger operator's strict low-energy subspace. This is
the finite-dimensional spectral argument for AKLV, arXiv:1301.1162v1,
equation (8), Section 6.3. -/
theorem IsHermitian.energyTruncation_mul_lowProjection_eq {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B)
    (hle : A ≤ B) (t : ℝ) :
    energyTruncation A t * (1 - spectralProjectionGE B t) =
      A * (1 - spectralProjectionGE B t) := by
  classical
  obtain ⟨U, a, b, hUU, hUU', hAU, hBU⟩ :=
    exists_unitary_diagonal_of_commute hA hB hAB.eq
  let V : unitary (Matrix n n ℂ) := ⟨U, by
    rw [Unitary.mem_iff]
    exact ⟨hUU, hUU'⟩⟩
  have hdiag (f : n → ℝ) : (diagonal (fun i ↦ (f i : ℂ))).IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    ext i
    exact Complex.conj_ofReal _
  have hconj (f : n → ℝ) (g : ℝ → ℝ) :
      cfc g (U * diagonal (fun i ↦ (f i : ℂ)) * Uᴴ) =
        U * diagonal (fun i ↦ (g (f i) : ℂ)) * Uᴴ := by
    have h := cfc_conj_unitary (hdiag f) g V
    rw [cfc_diagonal f g ((Set.finite_range f).continuousOn g)] at h
    exact h
  have horder : ∀ i, a i ≤ b i := by
    have h := (Matrix.le_iff.mp hle).conjTranspose_mul_mul_same U
    have hsim : Uᴴ * (B - A) * U =
        diagonal (fun i ↦ ((b i - a i : ℝ) : ℂ)) := by
      rw [hAU, hBU, mul_sub, sub_mul]
      simp only [mul_assoc, ← mul_assoc Uᴴ U, hUU, one_mul, mul_one]
      simp only [Complex.ofReal_sub, diagonal_sub]
    rw [hsim] at h
    intro i
    have hi := h.diag_nonneg (i := i)
    simp only [diagonal_apply_eq] at hi
    have hi' : 0 ≤ b i - a i := by exact_mod_cast hi
    exact sub_nonneg.mp hi'
  have hclip : energyTruncation A t =
      U * diagonal (fun i ↦ ((min (a i) t : ℝ) : ℂ)) * Uᴴ := by
    rw [energyTruncation, hAU, hconj]
  have hlow : 1 - spectralProjectionGE B t =
      U * diagonal (fun i ↦ (1 - if t ≤ b i then 1 else 0 : ℂ)) * Uᴴ := by
    rw [spectralProjectionGE, hBU, hconj]
    have hI : (1 : Matrix n n ℂ) = U * 1 * Uᴴ := by simpa using hUU'.symm
    conv_lhs => lhs; rw [hI]
    rw [← sub_mul, ← mul_sub, ← diagonal_one]
    simp only [← diagonal_sub]
    congr 2
    ext i j
    simp only [Matrix.sub_apply, diagonal_apply]
    split_ifs <;> norm_num
  rw [hclip, hlow, hAU]
  simp only [mul_assoc, ← mul_assoc Uᴴ U, hUU, one_mul]
  congr 1
  rw [← mul_assoc, ← mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  ext i
  by_cases hi : t ≤ b i
  · simp [hi]
  · have hai : a i ≤ t := (horder i).trans (le_of_not_ge hi)
    simp [hi, min_eq_left hai]

end Matrix

namespace TNLean.MPS.AreaLaw.AKLV

/-- The two exterior blocks are clipped separately, while the middle is
unchanged. AKLV, arXiv:1301.1162v1, Section 6.1, definition of `H^(t)`.
Here `L = H_L + H_1`, `R = H_s + H_R`, and `M = H_2 + ⋯ + H_(s-1)`. -/
def twoSidedEnergyTruncation {n : Type*} [Fintype n] [DecidableEq n]
    (L M R : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  Matrix.energyTruncation L t + M + Matrix.energyTruncation R t

/-- The actual two-sided clipping is Hermitian, positive, below the
original operator, and bounded by the sum of the two cutoff budgets and
the middle budget. AKLV, arXiv:1301.1162v1, Section 6.1. -/
theorem twoSidedEnergyTruncation_bounds {n : Type*} [Fintype n] [DecidableEq n]
    (L M R : Matrix n n ℂ) (hL : L.PosSemidef) (hM : M.PosSemidef)
    (hR : R.PosSemidef) (t m : ℝ) (ht : 0 ≤ t)
    (hcap : M ≤ (m : ℂ) • 1) :
    (twoSidedEnergyTruncation L M R t).PosSemidef ∧
      twoSidedEnergyTruncation L M R t ≤ L + M + R ∧
      twoSidedEnergyTruncation L M R t ≤ ((2 * t + m : ℝ) : ℂ) • 1 := by
  have hlow (A : Matrix n n ℂ) (hA : A.PosSemidef) :
      0 ≤ Matrix.energyTruncation A t := by
    simpa only [Complex.ofReal_zero, zero_smul] using
      hA.isHermitian.smul_one_le_energyTruncation ht
        (fun r hr ↦ spectrum_nonneg_of_nonneg hA.nonneg hr)
  refine ⟨Matrix.nonneg_iff_posSemidef.mp
    (add_nonneg (add_nonneg (hlow L hL) hM.nonneg) (hlow R hR)), ?_, ?_⟩
  · change Matrix.energyTruncation L t + M + Matrix.energyTruncation R t ≤ _
    exact add_le_add (add_le_add (hL.isHermitian.energyTruncation_le t) (le_refl M))
      (hR.isHermitian.energyTruncation_le t)
  · have h := add_le_add
      (add_le_add (hL.isHermitian.energyTruncation_le_smul_one t) hcap)
      (hR.isHermitian.energyTruncation_le_smul_one t)
    change Matrix.energyTruncation L t + M + Matrix.energyTruncation R t ≤ _
    exact h.trans_eq (by
      rw [← add_smul, ← add_smul]
      congr 1
      push_cast
      ring)

/-- The clipped and original Hamiltonians have identical action on the
strict low-energy subspace of the disconnected Hamiltonian. This is
AKLV, arXiv:1301.1162v1, equation (8), Section 6.3. The middle term may
contain the two boundary couplings and need not commute with `B`. -/
theorem twoSidedEnergyTruncation_mul_lowProjection_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (L M R B : Matrix n n ℂ) (hL : L.IsHermitian) (hR : R.IsHermitian)
    (hB : B.IsHermitian) (hLB : Commute L B) (hRB : Commute R B)
    (hLle : L ≤ B) (hRle : R ≤ B) (t : ℝ) :
    twoSidedEnergyTruncation L M R t * (1 - Matrix.spectralProjectionGE B t) =
      (L + M + R) * (1 - Matrix.spectralProjectionGE B t) := by
  simp only [twoSidedEnergyTruncation, add_mul,
    hL.energyTruncation_mul_lowProjection_eq hB hLB hLle t,
    hR.energyTruncation_mul_lowProjection_eq hB hRB hRle t]

end TNLean.MPS.AreaLaw.AKLV
