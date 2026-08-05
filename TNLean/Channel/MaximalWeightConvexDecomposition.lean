/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt

/-!
# Maximal weight in convex decomposition (Wolf Chapter 1)

This file proves Wolf's Proposition "Maximal weight in convex decomposition"
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, line 371): for
density operators `ρ`, `ρ₁` on the same space, there is a convex decomposition
`ρ = ∑ᵢ λᵢ ρᵢ` giving `ρ₁` a positive weight `λ₁` iff `ker(ρ) ⊆ ker(ρ₁)` and
`λ₁ ≤ ‖ρ^{-1/2} ρ₁ ρ^{-1/2}‖∞⁻¹`, the inverse taken on the range of `ρ`.

## Main definitions

* `Matrix.HasConvexDecompositionWith`: `ρ` decomposes as a finite convex
  combination of density operators with a distinguished index carrying a
  given weight on a given density operator.

## Main results

* `Matrix.hasConvexDecompositionWith_iff`: the proposition itself.

## References

* [M. Wolf, *Quantum Channels & Operations*, Ch. 1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {D : ℕ}

/-- **Convex decomposition of a density operator with a distinguished term**
(Wolf Ch. 1, "Maximal weight in convex decomposition",
`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, line 371). `ρ`
decomposes as `ρ = ∑ᵢ λᵢ ρᵢ` with every `ρᵢ` a density operator, every
`λᵢ ≥ 0`, `∑ᵢ λᵢ = 1`, and a distinguished index carrying weight `c` on `ρ₁`. -/
def HasConvexDecompositionWith (ρ ρ1 : Matrix (Fin D) (Fin D) ℂ) (c : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (rho : ι → Matrix (Fin D) (Fin D) ℂ) (i1 : ι),
    (∀ i, (rho i).PosSemidef) ∧ (∀ i, (rho i).trace = 1) ∧ (∀ i, 0 ≤ lam i) ∧
      (∑ i, lam i = 1) ∧ (∑ i, lam i • rho i = ρ) ∧ lam i1 = c ∧ rho i1 = ρ1

/-- The kernel-inclusion half of the necessity direction: if `ρ` has a convex
decomposition giving `ρ₁` a positive weight, then `ker(ρ) ⊆ ker(ρ₁)`. Adding
positive-semidefinite operators can never decrease the support. -/
theorem ker_subset_of_hasConvexDecompositionWith
    {ρ ρ1 : Matrix (Fin D) (Fin D) ℂ} {c : ℝ} (hc : 0 < c)
    (hdecomp : HasConvexDecompositionWith ρ ρ1 c) :
    ∀ v : Fin D → ℂ, ρ *ᵥ v = 0 → ρ1 *ᵥ v = 0 := by
  obtain ⟨ι, _, lam, rho, i1, hrhoPSD, _, hlamNonneg, _, hSum, hlam1, hrho1⟩ := hdecomp
  intro v hv
  have hρ1PSD : ρ1.PosSemidef := hrho1 ▸ hrhoPSD i1
  have hzero : star v ⬝ᵥ (ρ *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  have hexpand : star v ⬝ᵥ (ρ *ᵥ v) =
      ∑ i, (lam i : ℂ) * (star v ⬝ᵥ (rho i *ᵥ v)) := by
    rw [← hSum]
    simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
      Complex.real_smul]
  rw [hexpand] at hzero
  have hterm_nonneg (i : ι) : 0 ≤ (lam i : ℂ) * (star v ⬝ᵥ (rho i *ᵥ v)) := by
    have h1 : (0 : ℝ) ≤ lam i := hlamNonneg i
    have h2 := (hrhoPSD i).dotProduct_mulVec_nonneg v
    exact mul_nonneg (by exact_mod_cast h1) h2
  have hterm_zero : (lam i1 : ℂ) * (star v ⬝ᵥ (rho i1 *ᵥ v)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm_nonneg i).mp hzero i1 (Finset.mem_univ i1)
  rw [hlam1, hrho1] at hterm_zero
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hquad : star v ⬝ᵥ (ρ1 *ᵥ v) = 0 := (mul_eq_zero.mp hterm_zero).resolve_left hc'
  exact (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hρ1PSD v).mp hquad

/-- **Maximal weight in convex decomposition** (Wolf Ch. 1, line 371). For
density operators `ρ`, `ρ₁` on the same space, there is a convex decomposition
`ρ = ∑ᵢ λᵢρᵢ` giving `ρ₁` a positive weight `c` iff `ker(ρ) ⊆ ker(ρ₁)` and
`c ≤ ‖ρ^{-1/2}ρ₁ρ^{-1/2}‖∞⁻¹`, the inverse taken on the range of `ρ`. -/
theorem hasConvexDecompositionWith_iff
    {ρ ρ1 : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hρ1 : ρ1.PosSemidef)
    (hρtr : ρ.trace = 1) (hρ1tr : ρ1.trace = 1) {c : ℝ} (hc : 0 < c) :
    HasConvexDecompositionWith ρ ρ1 c ↔
      (∀ v : Fin D → ℂ, ρ *ᵥ v = 0 → ρ1 *ᵥ v = 0) ∧
        c * ‖hρ.supportInvSqrt * ρ1 * hρ.supportInvSqrt‖ ≤ 1 := by
  constructor
  · intro hdecomp
    have hker := ker_subset_of_hasConvexDecompositionWith hc hdecomp
    refine ⟨hker, ?_⟩
    classical
    obtain ⟨ι, _, lam, rho, i1, hrhoPSD, hrhoTr, hlamNonneg, hlamSum, hSum, hlam1, hrho1⟩ := hdecomp
    have hrest : ρ - c • ρ1 = ∑ i ∈ Finset.univ.erase i1, lam i • rho i := by
      have hadd := Finset.add_sum_erase Finset.univ (fun i => lam i • rho i)
        (Finset.mem_univ i1)
      rw [hSum, hlam1, hrho1] at hadd
      rw [← hadd, add_sub_cancel_left]
    have hpsd : (ρ - c • ρ1).PosSemidef := by
      rw [hrest]
      refine Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ => ?_)
      exact Matrix.nonneg_iff_posSemidef.mpr ((hrhoPSD i).smul (hlamNonneg i))
    exact (hρ.sub_smul_posSemidef_iff hρ1 hc hker).mp hpsd
  · rintro ⟨hker, hnorm⟩
    have hpsd : (ρ - c • ρ1).PosSemidef := (hρ.sub_smul_posSemidef_iff hρ1 hc hker).mpr hnorm
    have hctr : (ρ - c • ρ1).trace = ((1 - c : ℝ) : ℂ) := by
      rw [Matrix.trace_sub, Matrix.trace_smul, hρtr, hρ1tr, Complex.real_smul]
      push_cast; ring
    have hcle1 : c ≤ 1 := by
      have hnn := hpsd.trace_nonneg
      rw [hctr] at hnn
      have : (0 : ℝ) ≤ 1 - c := by exact_mod_cast hnn
      linarith
    rcases eq_or_lt_of_le hcle1 with heq | hlt
    · -- `c = 1`: `ρ - ρ1` has zero trace and is PSD, hence zero, so `ρ = ρ1`.
      have hzerotr : (ρ - c • ρ1).trace = 0 := by rw [hctr, heq]; simp
      have hρeq : ρ = c • ρ1 := by
        rw [← sub_eq_zero]; exact hpsd.trace_eq_zero_iff.mp hzerotr
      refine ⟨Fin 2, inferInstance, ![c, 1 - c], ![ρ1, ρ1], 0, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · intro i; fin_cases i <;> simpa using hρ1
      · intro i; fin_cases i <;> simpa using hρ1tr
      · intro i; fin_cases i <;> simp [hc.le, ← heq]
      · simp [Fin.sum_univ_two, ← heq]
      · simp [Fin.sum_univ_two, ← heq, hρeq]
    · -- `c < 1`: the leftover `(1 - c)⁻¹ • (ρ - c•ρ1)` is a genuine density operator.
      set σ := (1 - c)⁻¹ • (ρ - c • ρ1) with hσdef
      have h1c : (0 : ℝ) < 1 - c := by linarith
      have hσpsd : σ.PosSemidef := hpsd.smul (le_of_lt (inv_pos.mpr h1c))
      have hσtr : σ.trace = 1 := by
        have h1c' : (1 : ℂ) - (c : ℂ) ≠ 0 := by
          have : ((1 - c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1c.ne'
          rwa [Complex.ofReal_sub, Complex.ofReal_one] at this
        rw [hσdef, Matrix.trace_smul, hctr, Complex.real_smul]
        push_cast
        rw [inv_mul_cancel₀ h1c']
      refine ⟨Fin 2, inferInstance, ![c, 1 - c], ![ρ1, σ], 0, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · intro i; fin_cases i <;> simp [hρ1, hσpsd]
      · intro i; fin_cases i <;> simp [hρ1tr, hσtr]
      · intro i; fin_cases i <;> simp [hc.le, h1c.le]
      · simp [Fin.sum_univ_two]
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hσdef, smul_smul]
        have h1c' : ((1 - c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1c.ne'
        have hinv : (1 - c) * (1 - c)⁻¹ = 1 := mul_inv_cancel₀ h1c.ne'
        rw [hinv, one_smul, add_sub_cancel]

end Matrix
