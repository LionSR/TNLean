/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.PrefixColumn

/-!
# A unit vector in the retained prefix span

For a target extended by a fixed right basis configuration, one column of a
viable witness retains the full target pairing. The column has norm at most
one, so normalization improves the overlap and keeps the vector in the same
retained span.

Source: LVV13, arXiv:1307.5143v1, `def:viable`, lines 240--244, and final
induction, lines 652--678, applied to a product-ancilla extension.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A viable family for a target with fixed right configuration contains a
normalized prefix vector with at least the same ground overlap. The extracted
vector belongs to the actual retained span. Auxiliary to LVV13's final
induction, `algo53.tex`, lines 652--678, applied to a product-ancilla extension. -/
theorem IsViable.exists_prefix_of_rightBasisExtension {N q i : ℕ}
    {v : LeftBlockVector N q i}
    {b : (j : {j : Fin N // j ∉ leftBlock N i}) → Fin q}
    {delta : ℝ} (hdelta : delta < 1) {S : Set (LeftBlockVector N q i)}
    (h : IsViable (rightBasisExtension v b) delta S) :
    ∃ w ∈ Submodule.span ℂ S, ‖w‖ = 1 ∧ 1 - delta ≤ ‖⟪w, v⟫_ℂ‖ := by
  obtain ⟨φ, hφ, hoverlap, hsupport⟩ := h
  let w := cutColumn φ i b
  have hwspan : w ∈ Submodule.span ℂ S := hsupport b
  have hwnorm : ‖w‖ ≤ 1 := (norm_cutColumn_le φ b).trans_eq hφ
  have hoverlapw : 1 - delta ≤ ‖⟪w, v⟫_ℂ‖ := by
    simpa only [inner_rightBasisExtension] using hoverlap
  have hw0 : w ≠ 0 := by
    intro hz
    simp only [hz, inner_zero_left, norm_zero] at hoverlapw
    linarith
  have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let y := (‖w‖⁻¹ : ℂ) • w
  refine ⟨y, Submodule.smul_mem _ _ hwspan, norm_smul_inv_norm (𝕜 := ℂ) hw0, ?_⟩
  apply hoverlapw.trans
  calc
    ‖⟪w, v⟫_ℂ‖ ≤ ‖⟪w, v⟫_ℂ‖ / ‖w‖ := by
      apply (le_div_iff₀ hnormpos).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hwnorm (norm_nonneg ⟪w, v⟫_ℂ)
    _ = ‖⟪y, v⟫_ℂ‖ := by
      simp only [y, inner_smul_left, norm_mul, norm_inv, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, abs_norm, div_eq_mul_inv, mul_comm]

end TNLean.MPS.AreaLaw
