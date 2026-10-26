/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BoundaryGap
import TNLean.MPS.AreaLaw.OverlapEnergy
import TNLean.MPS.AreaLaw.RangeOneCut
import TNLean.MPS.AreaLaw.ViableSet.Basic
import TNLean.MPS.AreaLaw.ViableSet.TrimmedWitness
import TNLean.MPS.AreaLaw.ViableSet.TrimmingConstants

/-!
# A trimmed witness for a viable set

A viable set with overlap tolerance `c/L`, where `c = (Δ/169)²`, admits a unit chain vector
of energy at most `E₀ + 8c` whose left support lies in its span. Comparing this vector directly
with a trimmed ground vector gives a low-rank approximation with overlap at least `1 - 4c`.
Trimming preserves the viable left support and gives energy at most `E₀ + 6√c`.

This is an auxiliary version of Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`References/1307.5143/algo53.tex`, Lemma `l:within`, lines 509–515.

**Scope restriction (nontrivial chains and bond bound):** The result assumes `0 < L` and
`2 ≤ q` and uses `constantCutBond q 1 1 Δ c` from this library's area law. The source's
quantitative dependence `exp(O(Δ⁻¹ log³ q log(1/c)))` is not established here. See
`docs/paper-gaps/lvv13_constant_bond.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- A viable set admits a normalized trimmed witness with the library's constant bond
bound and energy excess at most `6√c`, where `c = (Δ/169)²`. This is the auxiliary form of
LVV13, `algo53.tex`, Lemma `l:within`, lines 509–515, under the scope of this module. -/
theorem ChainHamiltonian.exists_trimmed_witness_of_isViable
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {k : ℕ}
    {S : Set (LeftBlockVector L q k)}
    (hviable : IsViable Γ (((Δ / 169) ^ 2) / L) S) :
    ∃ w : EuclideanSpace ℂ (Fin L → Fin q),
      ‖w‖ = 1 ∧ w ∈ leftSupportSubmodule S ∧
      (cutMatrix w k).rank ≤ constantCutBond q 1 1 Δ ((Δ / 169) ^ 2) ∧
      (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2) := by
  classical
  let c : ℝ := (Δ / 169) ^ 2
  have hΔ4 : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  obtain ⟨hc0, hc, -⟩ := lvv_trimming_constant_bounds hΔ hΔ4
  change 0 < c at hc0
  change c ≤ 1 / 1600 at hc
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hcdiv : c / L ≤ c := div_le_self hc0.le hL1
  obtain ⟨ψ, hψ, hψΓ, hψS⟩ := hviable
  have hΓψ : 1 - c / L ≤ ‖⟪Γ, ψ⟫_ℂ‖ := by
    rw [norm_inner_symm]
    exact hψΓ
  have hE := h.re_inner_le_of_overlap_div_of_range_one hgs hL hψ hΓψ
  let D := constantCutBond q 1 1 Δ c
  obtain ⟨PΓ, hPΓ⟩ := exists_isTrimmingProjection
    (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) Γ) D
  let u := ‖chainTrim Γ k PΓ‖⁻¹ • chainTrim Γ k PΓ
  have hB := h.one_sub_le_re_inner_chainTrim (by omega : 1 ≤ q) (by norm_num)
    hΔ hgs hc0 k hPΓ
  have hu : ‖u‖ = 1 := norm_normalized_chainTrim_eq_one (by linarith : c < 1) hB
  have huD : (cutMatrix u k).rank ≤ D := rank_cutMatrix_normalized_chainTrim_le hPΓ
  have huΓ : 1 - c ≤ ‖⟪u, Γ⟫_ℂ‖ := hB.trans (Complex.re_le_norm _)
  have huψ : 1 - 4 * c ≤ ‖⟪u, ψ⟫_ℂ‖ := by
    have hov := one_sub_two_mul_add_le_norm_inner hu hψ hgs.1 hc0.le
      (by linarith : c ≤ 1) (div_nonneg hc0.le (by positivity))
      (hcdiv.trans (by linarith : c ≤ 1)) huΓ hψΓ
    linarith
  obtain ⟨HL, HR, K, hsplit, hHL, hHR, hK0, hK1⟩ :=
    h.exists_cut_decomposition_of_range_one hpos k
  have hblock : interval L 0 k = leftBlock L k := by
    ext i
    simp [interval, leftBlock]
  rw [hblock] at hHL hHR
  obtain ⟨w, m, W, x, hw, hwD, hwE, hwPV, -⟩ :=
    exists_trimmed_witness_chain hsplit hHL hHR hK0 hK1
      (hgs.posSemidef_sub_smul_one hΔ.le) hψ hE hu huD huψ
      (by linarith : 2 * (4 * c) < 1)
      ((spanProjection_mul_cutMatrix_eq_iff (S := S)).mpr hψS)
  refine ⟨w, hw, (spanProjection_mul_cutMatrix_eq_iff (S := S)).mp hwPV, hwD, ?_⟩
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt : √(2 * (4 * c)) = 2 * √(2 * c) := by
    rw [show 2 * (4 * c) = 4 * (2 * c) by ring, Real.sqrt_mul (by norm_num), hsqrt4]
  have hf : (8 * c + 2 * √(2 * (4 * c))) / (1 - 2 * (4 * c)) =
      (8 * c + 4 * √(2 * c)) / (1 - 8 * c) := by
    rw [hsqrt]
    ring
  rw [hf] at hwE
  exact hwE.trans (add_le_add le_rfl (trimming_energy_fraction_le_six_mul_sqrt hc0.le hc))

end TNLean.MPS.AreaLaw
