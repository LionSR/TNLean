/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.LowEnergyCluster
import QICLean.Analysis.LowEnergyPerturbation
import TNLean.Lattice.DisjointRegionalGround
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import TNLean.MPS.AreaLaw.PolynomialFilterParameters
import TNLean.MPS.AreaLaw.RegionalTruncationResidual

/-!
# The low spectral cluster after three-bulk truncation

For five consecutive regions, clip the three bulks at one scale and retain both windows.
Original regional minima and a common ground vector determine the centered Hamiltonian.
Residual estimates on the original low space and the current low space identify a full
spectral cluster close to the original ground space.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

section

section

section

namespace Real

/-- The fixed physical parameters yield a uniform single-region tail
constant when the connecting set has at most six bonds. The relative
low-energy cutoff is bounded using all five original regional minima.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024.
The three-region sum consequently has prefactor `288 * exp (11/8)`. -/
private theorem regional_tail_physical_constants
    (ell eta e c : ℝ) (hell : 21 ≤ ell) (heta : eta ≤ 1)
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
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    _ ≤ (exp (-(1 / 8) * (ell - (19 + eta)) - 1) / (1 / 8)) * 12 :=
      mul_le_mul_of_nonneg_left hquot hcoef
    _ = 96 * exp (11 / 8) * exp (-(ell - eta) / 8) := by
      rw [hexp, exp_add]
      ring
end Real
end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Actual three-bulk truncation residual for five consecutive regions.
The original regional minima, joint unit vector and centered original ground
energy are constructed internally. The same original cutoff is used for
every current clipping subset. Auxiliary to ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, `c:goodagsphardtrunc`, lines 979–1005,
and Theorem `t:ais`, lines 1010–1024. -/
private theorem exists_five_region_physical_truncation_residual
    (L q a b ell : ℕ) (hq : 0 < q) (hell : 21 ≤ ell)
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
          cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ))) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      let K : Finset (Fin 5) := {0, 2, 4}
      let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      star x ⬝ᵥ x = 1 ∧
      (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B ∅ = (∑ i, h i) - (S : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B K‖ ≤ 7 * (ell : ℝ) ∧
      ∀ (T : Finset (Fin 5)) (eta : ℝ), 0 ≤ eta → eta ≤ 1 →
        ∀ (v : OrthonormalBasis (Fin L → Fin q) ℂ
          (EuclideanSpace ℂ (Fin L → Fin q))) (lam : (Fin L → Fin q) → ℝ),
        (∀ j, ι (B T) (v j) = (lam j : ℂ) • v j) →
        ‖(ι (B ∅ - B K)).domRestrict
            (Submodule.spectralSpanLE v lam (E0 + eta))‖ ≤
          (288 * Real.exp (11 / 8)) * Real.exp (-((ell : ℝ) - eta) / 8) := by
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
    (∑ j, ((if j ∈ T then cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ)))
      (A j) else A j) - (e j : ℂ) • 1)) + Y
  let K : Finset (Fin 5) := {0, 2, 4}
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hell1 : 1 ≤ ell := by omega
  have hellR : 21 ≤ (ell : ℝ) := by exact_mod_cast hell
  have hsumc : (∑ j, (e j : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) = (S : ℂ) • 1 := by
    simp only [Complex.coe_smul, ← Finset.sum_smul, S]
  have hcenter : B ∅ = (∑ i, h i) - (S : ℂ) • 1 := by
    simp only [B, Finset.notMem_empty, ite_false, Finset.sum_sub_distrib, hsumc]
    rw [hH]
    abel
  obtain ⟨_, _, _, _, _, _, E0, z, hzunit, hz, hE0low, hE0ge, hE0le⟩ :=
    hclip (ell : ℝ) hell0 ∅
  have hE0le4 : E0 ≤ 4 := hE0le.trans (by exact_mod_cast hJ)
  have hc1 : (I 1).card ≤ 2 * ell - 2 := by
    have hc : (I 1).card ≤ (a + 2 * ell) - (a + 1) - 1 := by
      simpa [I, k] using card_internal_bonds_le L (a + 1) (a + 2 * ell)
    omega
  have hc3 : (I 3).card ≤ 2 * ell - 2 := by
    have hc : (I 3).card ≤ (b + 2 * ell) - (b + 1) - 1 := by
      simpa [I, k] using card_internal_bonds_le L (b + 1) (b + 2 * ell)
    omega
  have hFinalNorm : ‖B K‖ ≤ 7 * (ell : ℝ) := by
    obtain ⟨_, _, _, _, _, hnorm, _⟩ := hclip (ell : ℝ) hell0 K
    exact hnorm.trans (Real.five_region_final_clipping_budget_le
      ell J.card (fun j ↦ (I j).card) hell1 hc1 hc3 hJ)
  refine ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0ge, hE0le4, hFinalNorm, ?_⟩
  intro T eta heta0 heta1 v lam hEigen
  let G := Submodule.spectralSpanLE v lam (E0 + eta)
  have hc6 : (J.card : ℝ) ≤ 6 := by exact_mod_cast (hJ.trans (by decide : 4 ≤ 6))
  obtain ⟨hcut, hgap, hcoef⟩ := Real.regional_tail_physical_constants
    (ell : ℝ) eta (E0 + eta) (J.card : ℝ) hellR heta1 (by linarith) hc6
  have hu : 0 ≤ 19 + eta := by linarith
  have he (j : Fin 5) : (e j : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A j :=
    Matrix.le_iff.mpr (hlo j)
  have hsingle (j : Fin 5) :
      ‖(ι (A j - cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ)))
        (A j))).domRestrict G‖ ≤
          96 * Real.exp (11 / 8) * Real.exp (-((ell : ℝ) - eta) / 8) := by
    have htail := norm_consecutive_regional_truncation_low_le k hk h hs h0 h1
      e T j J (19 + eta) (E0 + eta) (1 / 8) (ell : ℝ)
      (by norm_num) (by norm_num) hu hcut v lam he hEigen hgap
    exact htail.trans hcoef
  have hsum := Matrix.norm_centered_clipping_discrepancy_domRestrict_le_sum
    A (fun j ↦ cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ))) (A j))
    (fun j ↦ (e j : ℂ)) K G
  have hsumB : ‖(ι (B ∅ - B K)).domRestrict G‖ ≤
      ∑ j ∈ K, ‖(ι (A j - cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ)))
        (A j))).domRestrict G‖ := by
    simpa only [B, Finset.notMem_empty, ite_false, add_sub_add_right_eq_sub]
      using hsum
  refine hsumB.trans ?_
  calc
    _ ≤ ∑ _j ∈ K,
        (96 * Real.exp (11 / 8) * Real.exp (-((ell : ℝ) - eta) / 8)) :=
      Finset.sum_le_sum fun j _ ↦ hsingle j
    _ = (288 * Real.exp (11 / 8)) * Real.exp (-((ell : ℝ) - eta) / 8) := by
      (norm_num [K, Finset.sum_const, nsmul_eq_mul]; ring)
end TNLean.MPS.AreaLaw
end

section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The actual three-bulk clipping has a low spectral cluster of the same
dimension as the full original ground space, with no simplicity assumption.
Auxiliary to ALVV, arXiv:1602.08828v2, Assumption (DG), lines 267–280,
and Theorem t:ais, lines 1010–1024. The explicit scalar tail condition is
an intermediate quantitative requirement for the later joint parameter
choice; no complete AGSP operator-family theorem is asserted here. -/
private theorem exists_five_region_physical_low_cluster
    (L q a b ell : ℕ) (hq : 0 < q) (hell : 21 ≤ ell)
    (hab : a + 2 * ell ≤ b + 1) (hbL : b + 2 * ell ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (mu g xi : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (htail : (288 * Real.exp (11 / 8)) *
      Real.exp (-((ell : ℝ) - g) / 8) ≤ xi)
    (hxi : xi ≤ g / 1000000) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    mu ∈ spectrum ℝ H →
    (∀ r ∈ spectrum ℝ H, r = mu ∨ mu + g ≤ r) →
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ),
      let S := ∑ j, e j
      let K : Finset (Fin 5) := {0, 2, 4}
      let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        (∑ j, ((if j ∈ K then
          cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ))) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + S = mu ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧ ‖B‖ ≤ 7 * (ell : ℝ) ∧
      ∃ (v : OrthonormalBasis (Fin L → Fin q) ℂ
          (EuclideanSpace ℂ (Fin L → Fin q))) (lam : (Fin L → Fin q) → ℝ),
        (∀ j, ι B (v j) = (lam j : ℂ) • v j) ∧
        let T := Submodule.spectralSpanLE v lam (E0 + g / 10)
        T = Submodule.spectralSpanLE v lam (E0 + 9 * g / 10) ∧
        (∀ tau : ℝ, E0 + g / 20 ≤ tau → tau ≤ E0 + 19 * g / 20 →
          Submodule.spectralSpanLE v lam tau = T) ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
        Submodule.IsCloseTo (1 / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (1 / 200 : ℝ) G T ∧
        ∀ j, lam j ≤ E0 + g / 10 ∨ E0 + 9 * g / 10 ≤ lam j := by
  intro H hH G hmu hgap k A J Y
  have : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0ge, hE0le, hnorm, hres⟩ :=
    exists_five_region_physical_truncation_residual L q a b ell hq hell hab hbL
      h hs h0 h1
  let S : ℝ := ∑ j, e j
  let K : Finset (Fin 5) := {0, 2, 4}
  let Bcur : Finset (Fin 5) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun T ↦
    (∑ j, ((if j ∈ T then cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ)))
      (A j) else A j) - (e j : ℂ) • 1)) + Y
  let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Bcur K
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  have hcenter' : Bcur ∅ = H - (S : ℂ) • 1 := hcenter
  have hzeigen : (H - (S : ℂ) • 1) *ᵥ z = (E0 : ℂ) • z := by
    rw [← hcenter']
    exact hz
  have hlow : ((H - (S : ℂ) • 1) - (E0 : ℂ) • 1).PosSemidef := by
    rw [← hcenter']
    exact hE0low
  obtain ⟨hmuE, hOldEigen, hOldGap⟩ := hH.original_basis_centered_gap_data
    mu g S E0 hmu hgap hg z hzunit hzeigen hlow
  let b0 := hH.eigenvectorBasis
  let a0 : (Fin L → Fin q) → ℝ := fun j ↦ hH.eigenvalues j - S
  have h0Eigen (j : Fin L → Fin q) :
      ι (Bcur ∅) (b0 j) = (a0 j : ℂ) • b0 j := by
    rw [hcenter']
    exact hOldEigen j
  have hA (j : Fin 5) : (A j).IsHermitian := by
    have hAj : 0 ≤ A j := Finset.sum_nonneg fun i _ ↦ h0 i
    exact (IsSelfAdjoint.of_nonneg hAj).isHermitian
  have he (j : Fin 5) : (e j : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A j :=
    Matrix.le_iff.mpr (hlo j)
  obtain ⟨hXpos, _hXzero⟩ :=
    Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e (ell : ℝ) K hA he x hx (Nat.cast_nonneg ell)
  have hYnonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ ↦ h0 i
  have hBpos : B.PosSemidef := hXpos.add (Matrix.nonneg_iff_posSemidef.mp hYnonneg)
  have hB : B.IsHermitian := hBpos.isHermitian
  let v := hB.eigenvectorBasis
  let lam := hB.eigenvalues
  have hBEigen (j : Fin L → Fin q) : ι B (v j) = (lam j : ℂ) • v j := by
    apply (WithLp.ofLp_injective 2)
    simpa only [ι, v, lam, ofLp_toEuclideanCLM, WithLp.ofLp_smul,
      Complex.coe_smul] using hB.mulVec_eigenvectorBasis j
  have hC : 0 ≤ (288 : ℝ) * Real.exp (11 / 8) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hxi0 : 0 ≤ xi :=
    (mul_nonneg hC (Real.exp_nonneg _)).trans htail
  have htailEta (eta : ℝ) (heta : eta ≤ g) :
      (288 * Real.exp (11 / 8)) * Real.exp (-((ell : ℝ) - eta) / 8) ≤ xi := by
    have hexp := Real.exp_mul_sub_le_exp_mul_sub
      (v := (1 / 8 : ℝ)) (x := eta) (T := g) (c := (ell : ℝ) / 8)
      (by norm_num) heta
    have harg (r : ℝ) : -((ell : ℝ) - r) / 8 =
        (1 / 8 : ℝ) * r - (ell : ℝ) / 8 := by ring
    rw [← harg eta, ← harg g] at hexp
    exact (mul_le_mul_of_nonneg_left hexp hC).trans htail
  have hsmall (Tcur : Finset (Fin 5)) (eta : ℝ) (heta0 : 0 ≤ eta) (heta : eta ≤ g)
      (w : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (d : (Fin L → Fin q) → ℝ)
      (hEigen : ∀ j, ι (Bcur Tcur) (w j) = (d j : ℂ) • w j) :
      ‖(ι (Bcur ∅) - ι B).domRestrict
        (Submodule.spectralSpanLE w d (E0 + eta))‖ ≤ xi := by
    have hr := (hres Tcur eta heta0 (heta.trans hg1) w d hEigen).trans
      (htailEta eta heta)
    simpa only [map_sub] using hr
  have hres0 := hsmall ∅ (g / 40) (by linarith) (by linarith) b0 a0 h0Eigen
  have hresK := hsmall K (19 * g / 20) (by linarith) (by linarith) v lam hBEigen
  obtain ⟨_hUV, hdim, hUG, hGU, hwindow, hNewGap⟩ :=
    Submodule.low_spectral_cluster_of_restricted_residuals
      (ι (Bcur ∅)) (ι B) b0 v a0 lam h0Eigen hBEigen E0 g xi hg hxi0 hxi
      hOldGap hres0 hresK
  let G0 := Submodule.spectralSpanLE b0 a0 E0
  have hG : G0 = G := by
    ext w
    change w ∈ Submodule.spectralSpanLE b0 a0 E0 ↔
      w ∈ Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    simp only [Submodule.mem_spectralSpanLE_iff]
    constructor
    · intro hw j hj
      apply hw j
      change E0 < hH.eigenvalues j - S
      linarith
    · intro hw j hj
      apply hw j
      change E0 < hH.eigenvalues j - S at hj
      linarith
  let U := Submodule.spectralSpanLE v lam (E0 + g / 20)
  let Tlow := Submodule.spectralSpanLE v lam (E0 + g / 10)
  have hTU : Tlow = U :=
    (hwindow (E0 + g / 10) (by linarith) (by linarith)).1
  have hupper : Submodule.spectralSpanLE v lam (E0 + 9 * g / 10) = U :=
    (hwindow (E0 + 9 * g / 10) (by linarith) (by linarith)).1
  refine ⟨e, E0, ⟨x, hxunit, hx, hlo⟩, hmuE.symm, hE0ge, hE0le, hnorm,
    v, lam, hBEigen, hTU.trans hupper.symm, ?_, ?_, ?_, ?_, hNewGap⟩
  · intro tau htaulo htauhi
    exact (hwindow tau htaulo htauhi).1.trans hTU.symm
  · change Module.finrank ℂ Tlow = Module.finrank ℂ G
    rw [hTU, ← hG]
    exact hdim
  · change Submodule.IsCloseTo (1 / 200 : ℝ) Tlow G
    rw [hTU, ← hG]
    exact hUG
  · change Submodule.IsCloseTo (1 / 200 : ℝ) G Tlow
    rw [hTU, ← hG]
    exact hGU
end TNLean.MPS.AreaLaw
end
end

section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- One universal scalar choice supplies the actual five-region low cluster,
its full cutoff band, the count budget, and the squared Chebyshev tradeoff.
The physical gap is normalized to `0 < g ≤ 1`; normalization of an arbitrary
original gap is a separate step. Auxiliary to ALVV, arXiv:1602.08828v2,
Assumption (DG), lines 267–280, and `t:ais`, lines 1010–1024.
No tail, error-scale, or scalar-compatibility hypothesis is supplied. -/
theorem exists_five_region_dg_cluster_parameters :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (q : ℕ) (g : ℝ), 2 ≤ q → 0 < g → g ≤ 1 →
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (q * ell ^ 2) ^ (22 * ell)
      let cA : ℝ := 6 + 2 * Real.log (A + 1)
      21 ≤ ell ∧ 2 ≤ D ∧
      Real.log (D : ℝ) ≤ 22 * (A + 1) * cA / g * u ^ 3 ∧
      ∀ (L a b : ℕ), a + 2 * ell ≤ b + 1 → b + 2 * ell ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      mu ∈ spectrum ℝ H →
      (∀ r ∈ spectrum ℝ H, r = mu ∨ mu + g ≤ r) →
      let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
      let Areg : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
        ∑ i ∈ Finset.univ.filter
          (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
      let J : Finset (Fin (L - 1)) := Finset.univ.filter
        (fun i ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y := ∑ i ∈ J, h i
      ∃ (e : Fin 5 → ℝ) (E0 : ℝ),
        let S := ∑ j, e j
        let K : Finset (Fin 5) := {0, 2, 4}
        let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          (∑ j, ((if j ∈ K then
            cfc (fun r : ℝ ↦ min r (e j + (ell : ℝ))) (Areg j) else Areg j) -
              (e j : ℂ) • 1)) + Y
        let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        let eta0 : ℝ := E0 + g / 10
        let eta1 : ℝ := E0 + 9 * g / 10
        let upper : ℝ := 7 * (ell : ℝ)
        let R : ℝ := upper - eta0
        let Delta : ℝ :=
          (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((eta1 - eta0) / R))) ^ 2
        (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
          (∀ j, Areg j *ᵥ x = (e j : ℂ) • x) ∧
          ∀ j, (Areg j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 + S = mu ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧ ‖B‖ ≤ upper ∧
        eta0 < eta1 ∧ eta1 ≤ upper ∧ 0 < R ∧ R ≤ 8 * (ell : ℝ) ∧
        0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∃ (v : OrthonormalBasis (Fin L → Fin q) ℂ
            (EuclideanSpace ℂ (Fin L → Fin q))) (lam : (Fin L → Fin q) → ℝ),
          (∀ j, ι B (v j) = (lam j : ℂ) • v j) ∧
          let T := Submodule.spectralSpanLE v lam eta0
          T = Submodule.spectralSpanLE v lam eta1 ∧
          (∀ tau : ℝ, E0 + g / 20 ≤ tau → tau ≤ E0 + 19 * g / 20 →
            Submodule.spectralSpanLE v lam tau = T) ∧
          Module.finrank ℂ T = Module.finrank ℂ G ∧
          Submodule.IsCloseTo (1 / 200 : ℝ) T G ∧
          Submodule.IsCloseTo (1 / 200 : ℝ) G T ∧
          ∀ j, lam j ≤ eta0 ∨ eta1 ≤ lam j := by
  obtain ⟨A, hA, hA21, _hAM, _hAlog, hall⟩ :=
    Real.exists_physical_dg_scalar_parameters
  refine ⟨A, hA, hA21, ?_⟩
  intro q g hq hg hg1 u ell D cA
  obtain ⟨hell, hD, _hlower, _hupper, _hscale, _hcount, hlogD, htrade, htail⟩ :=
    hall q g hq hg hg1
  refine ⟨hell, hD, hlogD, ?_⟩
  intro L a b hab hbL h hs h0 h1 mu H hH G hmu hgap k Areg J Y
  let xi : ℝ := g / 1000000
  obtain ⟨e, E0, hground, horigin, hE0, hE4, hnorm,
    v, lam, heigen, hclosed, hband, hdim, hTG, hGT, hnewgap⟩ :=
    exists_five_region_physical_low_cluster L q a b ell (by omega) hell hab hbL
      h hs h0 h1 mu g xi hg hg1 htail le_rfl hmu hgap
  refine ⟨e, E0, ?_⟩
  intro S K B ι eta0 eta1 upper R Delta
  obtain ⟨hsep, hendpoint, hR0, hR8, _hwidth, hsquare⟩ :=
    Real.physical_chebyshev_endpoints ell E0 g hell hE0 hE4 hg hg1
  have hDelta : Delta =
      4 * Real.exp (-4 * (ell : ℝ) ^ 2 * Real.sqrt ((4 * g / 5) / R)) := hsquare
  have hDelta0 : 0 < Delta := by
    change 0 <
      (2 * Real.exp (-2 * (ell : ℝ) ^ 2 * Real.sqrt ((eta1 - eta0) / R))) ^ 2
    exact sq_pos_of_pos (mul_pos (by norm_num) (Real.exp_pos _))
  have hsmall : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 := by
    rw [hDelta]
    simpa only [neg_mul] using htrade R hR0 hR8
  exact ⟨hground, horigin, hE0, hE4, hnorm, hsep, hendpoint, hR0, hR8,
    hDelta0, hsmall, v, lam, heigen, hclosed, hband, hdim, hTG, hGT, hnewgap⟩
end TNLean.MPS.AreaLaw
end
end
