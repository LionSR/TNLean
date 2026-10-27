/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RangeOneSupport
import QICLean.Analysis.OverlapEnergy

/-!
# Energy from overlap with a chain ground vector

A range-one Hamiltonian with interaction norms at most one has norm at most `2L`. Its
ground energy has modulus at most the same norm, so the shifted Hamiltonian has norm at
most `4L`. A unit vector with ground-state overlap at least `1 - δ` therefore has energy
excess at most `8Lδ`.

This is an auxiliary estimate for the first energy inference in the proof of LVV,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:within`, lines 509–515. The interaction model here
allows arbitrary Hermitian singleton and adjacent-pair terms, whereas the source assumes
positive adjacent-pair terms. This is the general norm estimate, not the full lemma.

**Local fix (witness energy):** The source omits a factor of two when converting its
unsquared overlap tolerance into an energy bound. The correction is recorded in
https://sirui-lu.com/QICLean/paper-gaps/lvv13_witness_energy.pdf. The subsequent trimming
argument and viable-set specialization are separate results.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {E₀ Δ δ c : ℝ} {Ω v : EuclideanSpace ℂ (Fin L → Fin q)}

/-- Ground-state overlap controls the energy of a unit vector for a range-one Hamiltonian
with interaction norms at most one. This is the general norm variant of the auxiliary
energy inference in LVV, arXiv:1307.5143v1, `algo53.tex`, proof of Lemma `l:within`,
lines 509–515. -/
theorem ChainHamiltonian.re_inner_sub_le_of_overlap_of_range_one
    (h : ChainHamiltonian L q 1 1) (hgs : IsGappedGroundState h.operator E₀ Ω Δ)
    (hv : ‖v‖ = 1) (hover : 1 - δ ≤ ‖⟪Ω, v⟫_ℂ‖) :
    (⟪v, toEuclideanLin h.operator v⟫_ℂ).re - E₀ ≤ 8 * L * δ := by
  let B := toEuclideanCLM (𝕜 := ℂ) h.operator
  have hB : ‖B‖ ≤ 2 * L := by
    simpa only [B, l2_opNorm_toEuclideanCLM, mul_one] using h.norm_operator_le_of_range_one
  have heig : B Ω = (E₀ : ℂ) • Ω := hgs.2.1
  have hE₀ : ‖(E₀ : ℂ)‖ ≤ ‖B‖ := by
    simpa only [heig, norm_smul, hgs.1, mul_one] using B.le_opNorm Ω
  have hshift : ‖B - (E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖ ≤ 4 * L := by
    calc
      ‖B - (E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖
          ≤ ‖B‖ + ‖(E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖ := norm_sub_le _ _
      _ ≤ ‖B‖ + ‖(E₀ : ℂ)‖ := by
        rw [norm_smul]
        exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin L → Fin q)))
          (norm_nonneg (E₀ : ℂ))).trans_eq (mul_one _))
      _ ≤ 4 * L := by linarith
  have hsymm : (toEuclideanLin h.operator).IsSymmetric :=
    (isSymmetric_toEuclideanLin_iff (A := h.operator)).mpr h.operator_isHermitian
  calc
    (⟪v, toEuclideanLin h.operator v⟫_ℂ).re - E₀ ≤ 2 * (4 * L) * δ :=
      hsymm.re_inner_sub_eigenvalue_le_of_overlap (B := B) (e := E₀)
        (M := 4 * L) (δ := δ) hgs.1 hv heig hshift hover
    _ = 8 * L * δ := by ring

/-- At overlap tolerance `c/L`, the preceding general norm estimate gives excess energy
at most `8c`. This is an auxiliary bound for LVV, arXiv:1307.5143v1, `algo53.tex`, proof of
Lemma `l:within`, lines 509–515. -/
theorem ChainHamiltonian.re_inner_le_of_overlap_div_of_range_one
    (h : ChainHamiltonian L q 1 1) (hgs : IsGappedGroundState h.operator E₀ Ω Δ)
    (hL : 0 < L) (hv : ‖v‖ = 1) (hover : 1 - c / L ≤ ‖⟪Ω, v⟫_ℂ‖) :
    (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + 8 * c := by
  have henergy := h.re_inner_sub_le_of_overlap_of_range_one hgs hv hover
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hcancel : (8 : ℝ) * L * (c / L) = 8 * c := by field_simp [hL0]
  rw [hcancel] at henergy
  linarith

end TNLean.MPS.AreaLaw
