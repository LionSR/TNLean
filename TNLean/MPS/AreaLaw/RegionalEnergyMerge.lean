/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.DisjointRegionalGround

/-!
# Ground energies when two disjoint regions are joined

The sum of the two regional minimum energies differs from the joined minimum
by at most one positive contraction. Two lower energy estimates with error at
most three therefore give a lower estimate for the joined region with error
at most seven. This supports ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1627–1632, and the energy-estimation argument in the proof of `t:alg1`,
lines 1805–1807. No gap or nondegeneracy assumption is imposed.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Original minima on disjoint supports are attained by one unit vector.
Adding a positive contraction raises their sum by at most one. Thus estimates
from below with error at most three on the children add to an estimate from
below with error at most seven on their union. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1627–1632. -/
theorem exists_disjoint_regional_energy_merge {L q : ℕ}
    (hq : 0 < q) (S T : Finset (Fin L)) (hST : Disjoint S T)
    (A B Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hAS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) A S)
    (hBT : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B T)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hY : Y.PosSemidef) (hY1 : Y ≤ 1) :
    ∃ (eA eB eP : ℝ) (x z : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (eA : ℂ) • x ∧ B *ᵥ x = (eB : ℂ) • x ∧
      (A - (eA : ℂ) • 1).PosSemidef ∧ (B - (eB : ℂ) • 1).PosSemidef ∧
      star z ⬝ᵥ z = 1 ∧ (A + B + Y) *ᵥ z = (eP : ℂ) • z ∧
      (A + B + Y - (eP : ℂ) • 1).PosSemidef ∧
      eA + eB ≤ eP ∧ eP ≤ eA + eB + 1 ∧
      ∀ pA pB : ℝ, eA - 3 ≤ pA → pA ≤ eA → eB - 3 ≤ pB → pB ≤ eB →
        eP - 7 ≤ pA + pB ∧ pA + pB ≤ eP := by
  classical
  have hcap (D : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (hD : D.PosSemidef) :
      D ≤ (⌈‖D‖⌉₊ : ℝ) • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap D (by positivity) hD.nonneg).mp (Nat.le_ceil ‖D‖)
  obtain ⟨e, x, hx, hxe, he, hclip⟩ :=
    exists_disjoint_regional_clipping_structure hq ![S, T] ![A, B] ![⌈‖A‖⌉₊, ⌈‖B‖⌉₊]
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm])
      (by intro i; fin_cases i <;> simpa using (by assumption))
      (by intro i; fin_cases i <;> simpa using (by assumption))
      (by
        intro i
        fin_cases i
        · exact hcap A hA
        · exact hcap B hB)
      Y 1 hY (by simpa using hY1)
  obtain ⟨_hX, _hxzero, _hcomm, _hhigh, _hcap, _hnorm, E, z, hz, hze, hE, hE0, hE1⟩ :=
    hclip 0 le_rfl ∅
  simp only [Finset.notMem_empty, ite_false, Fin.sum_univ_two, cons_val_zero,
    cons_val_one, Nat.cast_one] at hze hE hE1
  have hsplit : A - (e 0 : ℂ) • 1 + (B - (e 1 : ℂ) • 1) + Y =
      A + B + Y - ((e 0 + e 1 : ℝ) : ℂ) • 1 := by
    rw [Complex.ofReal_add, add_smul]
    abel
  refine ⟨e 0, e 1, E + e 0 + e 1, x, z, hx, hxe 0, hxe 1, he 0, he 1, hz,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit, sub_mulVec, smul_mulVec, one_mulVec] at hze
    simpa only [Complex.ofReal_add, add_smul, add_assoc] using (sub_eq_iff_eq_add.mp hze)
  · convert hE using 1
    simp only [Complex.ofReal_add, add_smul]
    abel
  · linarith only [hE0]
  · linarith only [hE1]
  · intro pA pB hpA hpAe hpB hpBe
    constructor <;> linarith only [hpA, hpAe, hpB, hpBe, hE0, hE1]

end TNLean.MPS.AreaLaw
