/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Module
import QICLean.Analysis.SoftTruncationCommutingFamily
import QICLean.Analysis.SoftTruncationOperatorBounds
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian

/-!
# Bounds for the complete five-region soft Hamiltonian

The three softened bulk regions retain their estimated scalar centers.
The two intervening windows and the crossing bonds remain unchanged.
The upper bound retains the logarithmic harmonic cap of each soft term.

Auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc` and
`t:aisefficient`, lines 1178–1185 and 1348–1392.
**Local fix (harmonic cap):** The upper bound retains `1 + log m`, rather
than the false printed `log m` cap. The estimated scalar centers and all
five original regional minima remain in the actual Hamiltonian. See
https://sirui-lu.com/QICLean/paper-gaps/alvv16_soft_truncation_log_bound.pdf
and `docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

private theorem three_bulk_soft_cap {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Fin 5 → Matrix σ σ ℂ) (e p : Fin 5 → ℝ)
    (Y : Matrix σ σ ℂ) (t a b c : ℝ) (m : ℕ)
    (he : ∀ j, 0 ≤ e j)
    (hpu : ∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), p j ≤ e j)
    (hX : ∀ j ∈ ({0, 2, 4} : Finset (Fin 5)),
      (A j - (p j : ℂ) • 1).PosSemidef)
    (ht : 0 < t) (hm : 1 ≤ m)
    (hA1 : A 1 ≤ a • 1) (hA3 : A 3 ≤ b • 1) (hY : Y ≤ c • 1) :
    (∑ j, ((if j ∈ ({0, 2, 4} : Finset (Fin 5)) then (p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)) + Y ≤
      (a + 3 * (t * (1 + Real.log (m : ℝ))) + b + c) • 1 := by
  let cap : ℝ := t * (1 + Real.log (m : ℝ))
  have hraw (j : Fin 5) (d : ℝ) (hd : A j ≤ d • 1) :
      A j - (e j : ℂ) • 1 ≤ d • 1 :=
    (sub_le_self (A j) (by
      simpa only [Complex.coe_smul] using
        smul_nonneg (he j) (zero_le_one : (0 : Matrix σ σ ℂ) ≤ 1))).trans hd
  have hsoft (j : Fin 5) (hj : j ∈ ({0, 2, 4} : Finset (Fin 5))) :
      (p j : ℂ) • (1 : Matrix σ σ ℂ) +
        cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) - (e j : ℂ) • 1 ≤ cap • 1 := by
    refine le_trans ?_ ((hX j hj).cfc_softTruncation_le_scalar t m ht hm)
    apply sub_le_iff_le_add.mpr
    simpa only [Complex.coe_smul, add_comm] using
      add_le_add_left
        (smul_le_smul_of_nonneg_right (hpu j hj)
          (zero_le_one : (0 : Matrix σ σ ℂ) ≤ 1))
        (cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1))
  have hpoint (j : Fin 5) :
      ((if j ∈ ({0, 2, 4} : Finset (Fin 5)) then (p j : ℂ) • 1 +
        cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) -
        (e j : ℂ) • 1) ≤ (![cap, a, cap, b, cap] j) • 1 := by
    fin_cases j
    · simpa using hsoft 0 (by decide)
    · simpa using hraw 1 a hA1
    · simpa using hsoft 2 (by decide)
    · simpa using hraw 3 b hA3
    · simpa using hsoft 4 (by decide)
  refine le_trans (_root_.add_le_add (Finset.sum_le_sum (fun j _ ↦ hpoint j)) hY) ?_
  apply le_of_eq
  simp only [cap, ← Finset.sum_smul, Fin.sum_univ_five]
  norm_num
  module

/-- The actual three-bulk soft Hamiltonian has a uniform norm ceiling
from the original bonds, their window widths, and the same supplied
attained regional minima. No spectral gap, residual, norm bound or second
choice of regional minima is assumed. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `t:aisefficient`,
lines 1178–1185 and 1348–1392. -/
theorem norm_five_region_soft_three_bulk_le {L q k1 k2 k3 k4 ell : ℕ}
    (h12 : k1 ≤ k2) (h23 : k2 ≤ k3) (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (hwindow1 : k2 - k1 ≤ 2 * ell) (hwindow3 : k4 - k3 ≤ 2 * ell)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ ∑ i ∈ I j, h i
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    ∀ (e : Fin 5 → ℝ) (x : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 →
      (∀ j, A j *ᵥ x = (e j : ℂ) • x) →
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) →
    ∀ (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
      (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), e j - 10 ≤ p j) →
      (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), p j ≤ e j) → 0 < t → 1 ≤ m →
      let B := ∑ j, ((if j ∈ ({0, 2, 4} : Finset (Fin 5)) then (p j : ℂ) • 1 +
        cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
      let G := B + Y
      ‖G‖ ≤ 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34 := by
  classical
  intro k I A J Y e x hx hxe he p t m hpl hpu ht hm B G
  obtain ⟨hk, _hR, _hAs, hA, hY, hYcap, hJ, _hsum⟩ :=
    five_region_original_bond_data L q k1 k2 k3 k4 h12 h23 h34 h4L h hs h0 h1
  have he0 (j : Fin 5) : 0 ≤ e j :=
    (hA j).1.nonneg_of_normalized_eigenvector (e j) x (hxe j) hx
  have hcomm : Pairwise fun i j : Fin 5 ↦ Commute (A i) (A j) :=
    pairwise_commute_sum_internal_consecutive_regions k hk h hs
  let S : Finset (Fin 5) := {0, 2, 4}
  obtain ⟨hBpos, _hBle, _hBA, _hproj⟩ := softTruncation_commuting_family_bounds
    A e p S (fun j ↦ (hA j).1.isHermitian) (fun j ↦ le_iff.mpr (he j))
    hpl hpu hcomm t m ht hm
  change (B + ((10 * (S.card : ℝ) : ℝ) : ℂ) • 1).PosSemidef at hBpos
  have hD : 10 * (S.card : ℝ) = 30 := by norm_num [S]
  have hBpos30 : (B + (30 : ℂ) • 1).PosSemidef := by
    simpa only [hD, Complex.ofReal_ofNat] using hBpos
  have hGshift : (G + (30 : ℂ) • 1).PosSemidef := by
    rw [show G + (30 : ℂ) • 1 = (B + (30 : ℂ) • 1) + Y by
      dsimp only [G]
      abel]
    exact hBpos30.add hY
  have hlower : -((30 : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) ≤ G :=
    neg_le_iff_add_nonneg.mpr (by
      rw [← Complex.coe_smul]
      simpa only [Complex.ofReal_ofNat, add_comm] using hGshift.nonneg)
  have hG : G.IsHermitian := by
    have hscalar : ((30 : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).IsHermitian :=
      isHermitian_one.smul (by simp [IsSelfAdjoint])
    simpa only [add_sub_cancel_right] using hGshift.isHermitian.sub hscalar
  have hX (j : Fin 5) (hj : j ∈ S) : (A j - (p j : ℂ) • 1).PosSemidef := by
    have hpe : (p j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤
        (e j : ℂ) • 1 := by
      simpa only [Complex.coe_smul] using smul_le_smul_of_nonneg_right (hpu j hj)
        (zero_le_one : (0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ 1)
    exact le_iff.mp (hpe.trans (le_iff.mpr (he j)))
  have hc1 : (I 1).card ≤ 2 * ell :=
    (card_internal_bonds_le L k1 k2).trans ((Nat.sub_le _ _).trans hwindow1)
  have hc3 : (I 3).card ≤ 2 * ell :=
    (card_internal_bonds_le L k3 k4).trans ((Nat.sub_le _ _).trans hwindow3)
  have hcap1 : A 1 ≤ (2 * (ell : ℝ)) • 1 :=
    (hA 1).2.trans (smul_le_smul_of_nonneg_right (by exact_mod_cast hc1) zero_le_one)
  have hcap3 : A 3 ≤ (2 * (ell : ℝ)) • 1 :=
    (hA 3).2.trans (smul_le_smul_of_nonneg_right (by exact_mod_cast hc3) zero_le_one)
  have hcapY : Y ≤ (4 : ℝ) • 1 :=
    hYcap.trans (smul_le_smul_of_nonneg_right (by exact_mod_cast hJ) zero_le_one)
  let cap := t * (1 + Real.log (m : ℝ))
  let upper := 3 * cap + 4 * (ell : ℝ) + 4
  have hupper : G ≤ upper • 1 := by
    have hcap := three_bulk_soft_cap A e p Y t (2 * (ell : ℝ)) (2 * (ell : ℝ)) 4 m
      he0 hpu hX ht hm hcap1 hcap3 hcapY
    have hcoeff : 2 * (ell : ℝ) + 3 * (t * (1 + Real.log (m : ℝ))) +
        2 * (ell : ℝ) + 4 = upper := by dsimp only [upper, cap]; ring
    simpa only [hcoeff] using hcap
  have hupper0 : 0 ≤ upper := by
    have hlog := Real.log_natCast_nonneg m
    dsimp only [upper, cap]
    positivity
  have : Nonempty (Fin L → Fin q) := by
    by_contra hne
    have : IsEmpty (Fin L → Fin q) := not_nonempty_iff.mp hne
    simp only [dotProduct, Fintype.sum_empty, zero_ne_one] at hx
  have hnorm : ‖G‖ ≤ max 30 upper := by
    have hmax := IsSelfAdjoint.norm_le_max_of_le_of_le hlower hupper hG.isSelfAdjoint
    simpa only [norm_neg, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hupper0, show |(30 : ℝ)| = 30 by norm_num] using hmax
  calc
    ‖G‖ ≤ max 30 upper := hnorm
    _ ≤ upper + 30 := max_le (by linarith only [hupper0]) (by linarith)
    _ = 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34 := by
      dsimp only [upper, cap]
      ring

end TNLean.MPS.AreaLaw.ALVV
