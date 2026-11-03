/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import QICLean.Analysis.EnergyTruncation
import TNLean.Lattice.DisjointRegionalGround
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import TNLean.MPS.AreaLaw.RegionalTruncationResidual

/-!
# Five-region clipping at an independent energy cutoff

For the five consecutive physical regions, the clipping threshold `t ≥ 0`
is independent of the window length. The original regional minima and a
common unit regional ground vector determine the centered Hamiltonians.
The three clipped bulks and two retained windows have norm budget
`3 * t + 4 * ell`. On every current low window of bandwidth `eta ≥ 0`
with `19 + eta ≤ t`, the residual relative to the original centered
Hamiltonian is bounded by `288 * exp (11/8) * exp (-(t-eta)/8)`.

This auxiliary uses the original nearest-neighbour interactions and does
not assume a spectral gap, a spectral decomposition or a residual estimate.
It supports ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 927–969,
and `c:goodagsphardtrunc`, lines 979–1005. The current coupled-cutoff
construction remains separate.
-/

namespace Real

/-- The fixed physical parameters yield a uniform single-region tail
constant when the connecting set has at most six bonds. The relative
low-energy cutoff is bounded using all five original regional minima.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024.
The three-region sum consequently has prefactor `288 * exp (11/8)`. -/
private theorem regional_tail_independent_physical_constants
    (ell eta e c : ℝ) (hell : 19 + eta ≤ ell)
    (he : e ≤ 6 + eta) (hc6 : c ≤ 6) :
    19 + eta ≤ ell ∧ 2 * c < (19 + eta) - e ∧
      (exp (-(1 / 8) * (ell - (19 + eta)) - 1) / (1 / 8)) *
        ((2 * c) / ((19 + eta) - e - 2 * c)) ≤
          96 * exp (11 / 8) * exp (-(ell - eta) / 8) := by
  have hden : 1 ≤ (19 + eta) - e - 2 * c := by linarith
  have hden0 : 0 < (19 + eta) - e - 2 * c := lt_of_lt_of_le zero_lt_one hden
  have hquot : (2 * c) / ((19 + eta) - e - 2 * c) ≤ 12 := by
    apply (div_le_iff₀ hden0).mpr
    linarith
  have hcoef : 0 ≤ exp (-(1 / 8) * (ell - (19 + eta)) - 1) / (1 / 8) :=
    div_nonneg (exp_nonneg _) (by norm_num)
  have hexp : -(1 / 8 : ℝ) * (ell - (19 + eta)) - 1 =
      11 / 8 + (-(ell - eta) / 8) := by ring
  refine ⟨hell, by linarith, ?_⟩
  calc
    _ ≤ (exp (-(1 / 8) * (ell - (19 + eta)) - 1) / (1 / 8)) * 12 :=
      mul_le_mul_of_nonneg_left hquot hcoef
    _ = 96 * exp (11 / 8) * exp (-(ell - eta) / 8) := by
      rw [hexp, exp_add]
      ring

end Real

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Actual three-bulk truncation residual for five consecutive regions.
The original regional minima, joint unit vector and centered original ground
energy are constructed internally. The real clipping threshold is independent
of the window length; the norm budget is `3*t + 4*ell`, and the residual
decays exponentially in `t`.
Every bandwidth `eta ≥ 0` with `19 + eta ≤ t` is allowed, without a gap
assumption. The same original cutoff is used for every current clipping subset.
Auxiliary to ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, `c:goodagsphardtrunc`, lines 979–1005,
and Theorem `t:ais`, lines 1010–1024. -/
theorem exists_five_region_independent_truncation_residual
    (L q a b ell : ℕ) (t : ℝ) (hq : 0 < q) (hell : 1 ≤ ell) (ht0 : 0 ≤ t)
    (hab : a + 2 * ell ≤ b + 1) (hbL : b + 2 * ell ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let I : Fin 5 → Finset (Fin (L - 1)) := fun j ↦
      Finset.univ.filter (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun j ↦ ∑ i ∈ I j, h i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ J, h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ),
      let S := ∑ j, e j
      let B : Finset (Fin 5) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        fun T ↦ (∑ j, ((if j ∈ T then
          cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      let K : Finset (Fin 5) := {0, 2, 4}
      let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      star x ⬝ᵥ x = 1 ∧
      (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B ∅ = (∑ i, h i) - (S : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      ∀ (T : Finset (Fin 5)) (eta : ℝ), 0 ≤ eta → 19 + eta ≤ t →
        ∀ (v : OrthonormalBasis (Fin L → Fin q) ℂ
          (EuclideanSpace ℂ (Fin L → Fin q))) (lam : (Fin L → Fin q) → ℝ),
        (∀ j, ι (B T) (v j) = (lam j : ℂ) • v j) →
        ‖(ι (B ∅ - B K)).domRestrict
            (Submodule.spectralSpanLE v lam (E0 + eta))‖ ≤
          (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8) := by
  intro k I A J Y
  have h12 : a + 1 ≤ a + 2 * ell := by omega
  have h34 : b + 1 ≤ b + 2 * ell := by omega
  obtain ⟨hk, hR, hAs, hAcap, hY, hYC, hJ, hH⟩ :=
    five_region_original_bond_data L q (a + 1) (a + 2 * ell) (b + 1)
      (b + 2 * ell) h12 hab h34 hbL h hs h0 h1
  let R : Fin 5 → Finset (Fin L) := fun j ↦ interval L (k j.castSucc) (k j.succ)
  obtain ⟨e, x, hxunit, hx, hlo, hclip⟩ :=
    Matrix.exists_disjoint_regional_clipping_structure hq R A
      (fun j ↦ (I j).card) hR hAs (fun j ↦ (hAcap j).1)
      (fun j ↦ (hAcap j).2) Y J.card hY hYC
  let S : ℝ := ∑ j, e j
  let B : Finset (Fin 5) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun T ↦
    (∑ j, ((if j ∈ T then cfc (fun r : ℝ ↦ min r (e j + t))
      (A j) else A j) - (e j : ℂ) • 1)) + Y
  let K : Finset (Fin 5) := {0, 2, 4}
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  have hsumc : (∑ j, (e j : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) = (S : ℂ) • 1 := by
    simp only [Complex.coe_smul, ← Finset.sum_smul, S]
  have hcenter : B ∅ = (∑ i, h i) - (S : ℂ) • 1 := by
    simp only [B, Finset.notMem_empty, ite_false, Finset.sum_sub_distrib, hsumc]
    rw [hH]
    abel
  obtain ⟨_, _, _, _, _, _, E0, z, hzunit, hz, hE0low, hE0ge, hE0le⟩ :=
    hclip t ht0 ∅
  have hE0le4 : E0 ≤ 4 := hE0le.trans (by exact_mod_cast hJ)
  have hc1 : (I 1).card ≤ 2 * ell - 2 := by
    have hc : (I 1).card ≤ (a + 2 * ell) - (a + 1) - 1 := by
      simpa [I, k] using card_internal_bonds_le L (a + 1) (a + 2 * ell)
    omega
  have hc3 : (I 3).card ≤ 2 * ell - 2 := by
    have hc : (I 3).card ≤ (b + 2 * ell) - (b + 1) - 1 := by
      simpa [I, k] using card_internal_bonds_le L (b + 1) (b + 2 * ell)
    omega
  have hFinalNorm : ‖B K‖ ≤ 3 * t + 4 * (ell : ℝ) := by
    obtain ⟨_, _, _, _, _, hnorm, _⟩ := hclip t ht0 K
    exact hnorm.trans (Real.five_region_final_clipping_budget_le
      ell J.card (fun j ↦ (I j).card) t hell hc1 hc3 hJ)
  refine ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0ge, hE0le4, hFinalNorm, ?_⟩
  intro T eta heta0 hcut v lam hEigen
  let G := Submodule.spectralSpanLE v lam (E0 + eta)
  have hc6 : (J.card : ℝ) ≤ 6 := by exact_mod_cast (hJ.trans (by decide : 4 ≤ 6))
  obtain ⟨hcut, hgap, hcoef⟩ := Real.regional_tail_independent_physical_constants
    t eta (E0 + eta) (J.card : ℝ) hcut (by linarith) hc6
  have hu : 0 ≤ 19 + eta := by linarith
  have he (j : Fin 5) : (e j : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A j :=
    Matrix.le_iff.mpr (hlo j)
  have hsingle (j : Fin 5) :
      ‖(ι (A j - cfc (fun r : ℝ ↦ min r (e j + t))
        (A j))).domRestrict G‖ ≤
          96 * Real.exp (11 / 8) * Real.exp (-(t - eta) / 8) := by
    have htail := norm_consecutive_regional_truncation_low_le k hk h hs h0 h1
      e T j J (19 + eta) (E0 + eta) (1 / 8) t
      (by norm_num) (by norm_num) hu hcut v lam he hEigen hgap
    exact htail.trans hcoef
  have hsum := Matrix.norm_centered_clipping_discrepancy_domRestrict_le_sum
    A (fun j ↦ cfc (fun r : ℝ ↦ min r (e j + t)) (A j))
    (fun j ↦ (e j : ℂ)) K G
  have hsumB : ‖(ι (B ∅ - B K)).domRestrict G‖ ≤
      ∑ j ∈ K, ‖(ι (A j - cfc (fun r : ℝ ↦ min r (e j + t))
        (A j))).domRestrict G‖ := by
    simpa only [B, Finset.notMem_empty, ite_false, add_sub_add_right_eq_sub]
      using hsum
  refine hsumB.trans ?_
  calc
    _ ≤ ∑ _j ∈ K,
        (96 * Real.exp (11 / 8) * Real.exp (-(t - eta) / 8)) :=
      Finset.sum_le_sum fun j _ ↦ hsingle j
    _ = (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8) := by
      (norm_num [K, Finset.sum_const, nsmul_eq_mul]; ring)

end TNLean.MPS.AreaLaw
