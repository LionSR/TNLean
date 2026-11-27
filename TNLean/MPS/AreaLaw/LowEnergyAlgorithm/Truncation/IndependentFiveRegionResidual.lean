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
import QICLean.Spectral.Filter.EnergyTruncation
import QICLean.ManyBody.Hamiltonian.DisjointRegionalGround
import QICLean.ManyBody.Hamiltonian.Chain.RegionalTruncation
import QICLean.Spectral.Eigenvalue.MatrixSpectralDecomp
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import QICLean.Spectral.LowEnergy.Cluster
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Analysis.Real.ExplicitThresholds

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

## The physical low cluster with independent clipping and window scales

An independent real clipping threshold gives a full low spectral cluster
of the same dimension as the original physical ground space. The actual
original regional minima, centered energy and clipped Hamiltonian are
constructed from positive nearest-neighbour contractions. The only
additional quantitative premise is the displayed scalar tail bound.

The original full ground space may be degenerate. Its gap is positive
and at most one in this auxiliary; later physical applications may use
the capped gap. This supports ALVV, arXiv:1602.08828v2,
`c:goodagsphardtrunc`, lines 979–1005, and `t:ais`, lines 1010–1024.

**Local fix (closed spectral cutoffs):** The cluster retains the full
original ground space with the closed-cutoff convention documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
-/

section

open ManyBody (interval)

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

/-- Clipping three bulks at an independent real threshold `t` and retaining
two windows with at most `2*ell-2` original internal bonds gives a total
centered norm budget at most `3*t + 4*ell`, including all crossing bonds. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and the spectral
radius estimate in Theorem `t:ais`, lines 1010–1024.
No additional crossing-bond constant is added after this budget. -/
theorem five_region_final_clipping_budget_le
    (ell C : ℕ) (c : Fin 5 → ℕ) (t : ℝ) (hell : 1 ≤ ell)
    (hc1 : c 1 ≤ 2 * ell - 2) (hc3 : c 3 ≤ 2 * ell - 2) (hC : C ≤ 4) :
    (∑ i : Fin 5, if i ∈ ({0, 2, 4} : Finset (Fin 5)) then t
      else (c i : ℝ)) + (C : ℝ) ≤ 3 * t + 4 * (ell : ℝ) := by
  have hnat : c 1 + c 3 + C ≤ 4 * ell := by omega
  have hreal : (c 1 : ℝ) + (c 3 : ℝ) + (C : ℝ) ≤ 4 * (ell : ℝ) := by
    exact_mod_cast hnat
  simp only [Fin.sum_univ_five]
  norm_num
  linarith

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
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let I : Fin 5 → Finset (Fin (L - 1)) := fun j ↦
      Finset.univ.filter (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun j ↦ ∑ i ∈ I j, Φ.term i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ J, Φ.term i
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
      B ∅ = Φ.hamiltonian - (S : ℂ) • 1 ∧
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
    ManyBody.BondInteraction.five_region_original_bond_data L q (a + 1) (a + 2 * ell) (b + 1)
      (b + 2 * ell) h12 hab h34 hbL Φ h0 h1
  let R : Fin 5 → Finset (Fin L) := fun j ↦ interval L (k j.castSucc) (k j.succ)
  have : NeZero q := ⟨hq.ne'⟩
  obtain ⟨e, x, hxunit, hx, hlo, hclip⟩ :=
    ManyBody.exists_disjoint_regional_clipping_structure (X := fun _ ↦ Fin q) R A
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
  have hcenter : B ∅ = Φ.hamiltonian - (S : ℂ) • 1 := by
    simp only [B, Finset.notMem_empty, ite_false, Finset.sum_sub_distrib, hsumc]
    rw [hH]
    abel
  obtain ⟨_, _, _, _, _, _, E0, z, hzunit, hz, hE0low, hE0ge, hE0le⟩ :=
    hclip t ht0 ∅
  have hE0le4 : E0 ≤ 4 := hE0le.trans (by exact_mod_cast hJ)
  have hc1 : (I 1).card ≤ 2 * ell - 2 := by
    have hc : (I 1).card ≤ (a + 2 * ell) - (a + 1) - 1 := by
      simpa [I, k] using ManyBody.card_internal_bonds_le L (a + 1) (a + 2 * ell)
    omega
  have hc3 : (I 3).card ≤ 2 * ell - 2 := by
    have hc : (I 3).card ≤ (b + 2 * ell) - (b + 1) - 1 := by
      simpa [I, k] using ManyBody.card_internal_bonds_le L (b + 1) (b + 2 * ell)
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
    have htail := ManyBody.BondInteraction.norm_consecutive_regional_truncation_low_le k hk Φ h0 h1
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

end

section

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- An actual three-bulk clipping at an independent real threshold has an
accuracy-scaled low cluster. The
regional minima, clipped operator, spectral basis and restricted residuals
are derived from the original nearest-neighbour terms. Only the displayed
scalar tail condition is assumed in this intermediate lemma; the universal
accuracy parameter choice discharges it in the long-middle theorem.
Auxiliary to ALVV, arXiv:1602.08828v2, Corollary 4.6 (`c:goodagsphardtrunc`)
and the approximation conclusion of Theorem 4.9 (`thm:al-dg`).
No simple-ground-space assumption is made. -/
theorem exists_five_region_independent_scaled_low_cluster
    (L q a b ell : ℕ) (t : ℝ) (hq : 0 < q) (hell : 1 ≤ ell) (ht : 21 ≤ t)
    (hab : a + 2 * ell ≤ b + 1) (hbL : b + 2 * ell ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (mu g xi tau : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (htau : 0 < tau) (htau1 : tau ≤ 1)
    (htail : (288 * Real.exp (11 / 8)) *
      Real.exp (-(t - g) / 8) ≤ xi)
    (hxi : xi ≤ tau * g / 1000000) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    mu ∈ spectrum ℝ H →
    (∀ r ∈ spectrum ℝ H, r = mu ∨ mu + g ≤ r) →
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ J, Φ.term i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ),
      let S := ∑ j, e j
      let K : Finset (Fin 5) := {0, 2, 4}
      let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        (∑ j, ((if j ∈ K then
          cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + S = mu ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧ ‖B‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      ∃ (v : OrthonormalBasis (Fin L → Fin q) ℂ
          (EuclideanSpace ℂ (Fin L → Fin q))) (lam : (Fin L → Fin q) → ℝ),
        (∀ j, ι B (v j) = (lam j : ℂ) • v j) ∧
        let T := Submodule.spectralSpanLE v lam (E0 + g / 10)
        T = Submodule.spectralSpanLE v lam (E0 + 9 * g / 10) ∧
        (∀ tau : ℝ, E0 + g / 20 ≤ tau → tau ≤ E0 + 19 * g / 20 →
          Submodule.spectralSpanLE v lam tau = T) ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
        Submodule.IsCloseTo (tau / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (tau / 200 : ℝ) G T ∧
        ∀ j, lam j ≤ E0 + g / 10 ∨ E0 + 9 * g / 10 ≤ lam j := by
  intro H hH G hmu hgap k A J Y
  have : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0ge, hE0le, hnorm, hres⟩ :=
    exists_five_region_independent_truncation_residual L q a b ell t hq hell
      (by linarith only [ht]) hab hbL
      Φ h0 h1
  let S : ℝ := ∑ j, e j
  let K : Finset (Fin 5) := {0, 2, 4}
  let Bcur : Finset (Fin 5) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun T ↦
    (∑ j, ((if j ∈ T then cfc (fun r : ℝ ↦ min r (e j + t))
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
      A e t K hA he x hx (by linarith only [ht])
  have hYnonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ ↦ h0 i
  have hBpos : B.PosSemidef := hXpos.add (Matrix.nonneg_iff_posSemidef.mp hYnonneg)
  have hB : B.IsHermitian := hBpos.isHermitian
  let v := hB.eigenvectorBasis
  let lam := hB.eigenvalues
  have hBEigen (j : Fin L → Fin q) : ι B (v j) = (lam j : ℂ) • v j := by
    exact hB.toEuclideanCLM_eigenvectorBasis j
  have hC : 0 ≤ (288 : ℝ) * Real.exp (11 / 8) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hxi0 : 0 ≤ xi :=
    (mul_nonneg hC (Real.exp_nonneg _)).trans htail
  have htailEta (eta : ℝ) (heta : eta ≤ g) :
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8) ≤ xi := by
    have hexp := Real.exp_mul_sub_le_exp_mul_sub
      (v := (1 / 8 : ℝ)) (x := eta) (T := g) (c := t / 8)
      (by norm_num) heta
    have harg (r : ℝ) : -(t - r) / 8 =
        (1 / 8 : ℝ) * r - t / 8 := by ring
    rw [← harg eta, ← harg g] at hexp
    exact (mul_le_mul_of_nonneg_left hexp hC).trans htail
  have hsmall (Tcur : Finset (Fin 5)) (eta : ℝ) (heta0 : 0 ≤ eta) (heta : eta ≤ g)
      (w : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (d : (Fin L → Fin q) → ℝ)
      (hEigen : ∀ j, ι (Bcur Tcur) (w j) = (d j : ℂ) • w j) :
      ‖(ι (Bcur ∅) - ι B).domRestrict
        (Submodule.spectralSpanLE w d (E0 + eta))‖ ≤ xi := by
    have hr := (hres Tcur eta heta0 (by linarith only [heta, hg1, ht]) w d hEigen).trans
      (htailEta eta heta)
    simpa only [map_sub] using hr
  have hres0 := hsmall ∅ (g / 40) (by linarith) (by linarith) b0 a0 h0Eigen
  have hresK := hsmall K (19 * g / 20) (by linarith) (by linarith) v lam hBEigen
  obtain ⟨_hUV, hdim, hUG, hGU, hwindow, hNewGap⟩ :=
    Submodule.low_spectral_cluster_of_scaled_restricted_residuals
      (ι (Bcur ∅)) (ι B) b0 v a0 lam h0Eigen hBEigen E0 g xi tau hg htau htau1 hxi0 hxi
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
  · change Submodule.IsCloseTo (tau / 200 : ℝ) Tlow G
    rw [hTU, ← hG]
    exact hUG
  · change Submodule.IsCloseTo (tau / 200 : ℝ) G Tlow
    rw [hTU, ← hG]
    exact hGU

end TNLean.MPS.AreaLaw

end
