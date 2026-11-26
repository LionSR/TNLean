/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Parameter.SpectralWindowPrecision
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Module
import QICLean.Spectral.Filter.SoftTruncationHighProjection
import QICLean.Spectral.Filter.ShiftedSoftHardTruncation
import QICLean.ManyBody.Hamiltonian.Chain.ConsecutiveRegions
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.SoftTruncation.SoftFamilyResiduals
import QICLean.Analysis.Subspace.ViableSubspace

/-!
# Scalar budgets for physical soft clusters

A bound on the crossing bonds gives residual budgets independent of the
selected soft ground energy. A uniform norm ceiling then fixes the precision
of a Hermitian approximation before its actual spectral windows are known.
These are numerical auxiliaries for ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1420. The residual and perturbation estimates
retain the corrections in `docs/paper-gaps/alvv16_soft_regional_residuals.tex`
and `docs/paper-gaps/alvv16_cluster_approximation.tex`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.ALVV.norm_five_region_soft_three_bulk_le`: bounds for the complete five-region
  soft Hamiltonian.
* `TNLean.MPS.AreaLaw.ALVV.exists_five_region_soft_uniform_clusters`: physical soft clusters with
  uniform numerical precision.
-/

section SoftClusterPrecision

namespace TNLean.MPS.AreaLaw.ALVV

private theorem residual_budget_mono {C U V T t : ℝ} {m : ℕ}
    (hC4 : C ≤ 4) (hUV : U ≤ V) :
    3 * (8 * C * Real.exp (-(T - U) / 8) + (t / (m : ℝ)) * (T / t) ^ m) ≤
      3 * (32 * Real.exp (-(T - V) / 8) + (t / (m : ℝ)) * (T / t) ^ m) := by
  gcongr
  · linarith only [hC4]

/-- Coarse residual conditions imply the actual forward and reverse budgets,
without dependence on the selected soft ground energy. Numerical auxiliary
to ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420. -/
theorem soft_cluster_scalar_residual_budgets {C E mu g T0 T1 t tau : ℝ} {m : ℕ}
    (hC4 : C ≤ 4) (hEC : E ≤ C) (hmu : -30 ≤ mu) (hg : 0 < g)
    (hT0 : g / 40 + 24 ≤ T0) (ht : 156 + 2 * g ≤ t)
    (hT1 : 156 + 2 * g ≤ T1)
    (hO : 3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) +
      (t / (m : ℝ)) * (T0 / t) ^ m) ≤ tau * g / 1000000)
    (hR : 3 * (32 * Real.exp (-(T1 - 156 - 2 * g) / 8) +
      (t / (m : ℝ)) * (T1 / t) ^ m) ≤ tau * g / 1000000) :
    let U := 2 * (E - mu + 19 * g / 20 + 30 + 3 * C + 2)
    g / 40 + 3 * C + 12 ≤ T0 ∧ U ≤ t ∧ U ≤ T1 ∧
      3 * (8 * C * Real.exp (-(T0 - g / 40 - 3 * C - 12) / 8) +
        (t / (m : ℝ)) * (T0 / t) ^ m) ≤ tau * g / 1000000 ∧
      3 * (8 * C * Real.exp (-(T1 - U) / 8) +
        (t / (m : ℝ)) * (T1 / t) ^ m) ≤ tau * g / 1000000 := by
  intro U
  have hU : U ≤ 156 + 2 * g := by
    dsimp only [U]
    linarith only [hEC, hmu, hC4, hg]
  refine ⟨by linarith only [hC4, hT0], hU.trans ht, hU.trans hT1, ?_, ?_⟩
  · refine le_trans ?_ hO
    simpa only [sub_add_eq_sub_sub] using
      (residual_budget_mono (T := T0) (t := t) (m := m)
        (U := g / 40 + 3 * C + 12) (V := g / 40 + 24) hC4
        (by linarith only [hC4]))
  · refine le_trans ?_ hR
    simpa only [sub_add_eq_sub_sub] using
      (residual_budget_mono (T := T1) (t := t) (m := m)
        (U := U) (V := 156 + 2 * g) hC4 hU)

/-- One explicit precision controls both literal spectral-window counts,
using only a norm ceiling and the original centered energy interval.
Numerical auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1412–1420, with the corrected finite-window comparison. -/
theorem soft_cluster_actual_window_losses {A M E g tau : ℝ}
    (hA : 0 ≤ A) (hAM : A ≤ M) (hE0 : 0 ≤ E) (hE4 : E ≤ 4)
    (hg : 0 < g) (htau : 0 < tau) :
    let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
    let V := A + xi
    let nLo := ⌈((E + g / 20) - min (E + g / 20 - 1) (-V)) / (2 * xi)⌉₊
    let nHi := ⌈((E + 3 * g / 4) - min (E + 3 * g / 4 - 1) (-V)) / (2 * xi)⌉₊
    0 < xi ∧ xi ≤ 1 ∧
      (nLo : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2 ≤ tau / 400 ∧
      (nHi : ℝ) * (2 * xi) ^ 2 / (g / 5 + xi) ^ 2 ≤ tau / 400 := by
  intro xi V nLo nHi
  obtain ⟨hxi, hxi1, _hbudget, huniform⟩ :=
    Real.soft_cluster_window_precision_parameters (hA.trans hAM) hg htau
  refine ⟨hxi, hxi1, ?_, ?_⟩
  · exact (Real.finite_window_loss_le_envelope hA hAM
      (by positivity : 0 ≤ E + g / 20)
      (by linarith only [hE4, hg] : E + g / 20 ≤ 4 + g)
      hxi (by positivity : 0 < g / 5)).trans huniform
  · exact (Real.finite_window_loss_le_envelope hA hAM
      (by positivity : 0 ≤ E + 3 * g / 4)
      (by linarith only [hE4, hg] : E + 3 * g / 4 ≤ 4 + g)
      hxi (by positivity : 0 < g / 5)).trans huniform

end TNLean.MPS.AreaLaw.ALVV

end SoftClusterPrecision

section FiveRegionSoftNorm

/-!
## Bounds for the complete five-region soft Hamiltonian

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

open ManyBody (interval)

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
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ ∑ i ∈ I j, Φ.term i
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := ∑ i ∈ J, Φ.term i
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
    ManyBody.BondInteraction.five_region_original_bond_data L q k1 k2 k3 k4 h12 h23 h34 h4L Φ h0 h1
  have he0 (j : Fin 5) : 0 ≤ e j :=
    (hA j).1.nonneg_of_normalized_eigenvector (e j) x (hxe j) hx
  have hcomm : Pairwise fun i j : Fin 5 ↦ Commute (A i) (A j) :=
    ManyBody.BondInteraction.pairwise_commute_sum_internal_consecutive_regions k hk Φ
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
    (ManyBody.card_internal_bonds_le L k1 k2).trans ((Nat.sub_le _ _).trans hwindow1)
  have hc3 : (I 3).card ≤ 2 * ell :=
    (ManyBody.card_internal_bonds_le L k3 k4).trans ((Nat.sub_le _ _).trans hwindow3)
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

end FiveRegionSoftNorm

section FiveRegionSoftUniformClusters

/-!
## Physical soft clusters with uniform numerical precision

One construction of the original regional minima is retained throughout.
The three bulk regions are softened and the two windows remain unchanged.
The norm ceiling and residual budgets depend only on the prescribed scalar
parameters. They imply the two actual finite-window comparisons for every
Hermitian approximation at the displayed precision.

This is a corrected auxiliary for ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1420. **Scope restriction (numerical budgets):**
The soft order, scale and residual cutoffs satisfy explicit scalar inequalities.
Their existence and the final improving-family construction are separate
steps. No soft gap or subspace comparison is assumed. See
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- Uniform scalar residual conditions and an explicit norm precision give
an actual invariant low cluster of each Hermitian approximation, of the
original full ground-space dimension. The regional minima are selected once,
before every center and soft parameter. Auxiliary to ALVV,
arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420. -/
theorem exists_five_region_soft_uniform_clusters {L q k1 k2 k3 k4 ell : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (hwindow1 : k2 - k1 ≤ 2 * ell) (hwindow3 : k4 - k3 ≤ 2 * ell)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ Φ.partialHamiltonian (I j)
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := Φ.partialHamiltonian J
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      ∀ (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), e j - 10 ≤ p j) →
        (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), p j ≤ e j) → 0 < t → 2 ≤ m →
        let G := (∑ j, ((if j ∈ ({0, 2, 4} : Finset (Fin 5)) then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)) + Y
        let M := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
        G.IsHermitian ∧ ‖G‖ ≤ M ∧
        let Hraw := Φ.hamiltonian
        let hRaw : Hraw.IsHermitian :=
          (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
        ∀ mu0 g tau T0 T1 : ℝ, mu0 ∈ spectrum ℝ Hraw → 0 < g →
          0 < tau → tau ≤ 1 →
          (∀ z ∈ spectrum ℝ Hraw, z = mu0 ∨ mu0 + g ≤ z) →
          g / 40 + 24 ≤ T0 → 156 + 2 * g ≤ t → 156 + 2 * g ≤ T1 →
          3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) +
            (t / (m : ℝ)) * (T0 / t) ^ m) ≤ tau * g / 1000000 →
          3 * (32 * Real.exp (-(T1 - 156 - 2 * g) / 8) +
            (t / (m : ℝ)) * (T1 / t) ^ m) ≤ tau * g / 1000000 →
          let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
          let original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
          0 < xi ∧ xi ≤ 1 ∧ E + ∑ j, e j = mu0 ∧
          ∀ (Bhat : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
            (hBhat : Bhat.IsHermitian), ‖G - Bhat‖ ≤ xi →
            let target := Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
              (E + g / 4)
            target = Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues
                (E + 3 * g / 4) ∧
              Module.finrank ℂ target = Module.finrank ℂ original ∧
              Submodule.IsCloseTo (3 * tau / 200) target original ∧
              Submodule.IsCloseTo (3 * tau / 200) original target := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
    hH, bH, aH, hEigH, hfamily⟩ :=
    exists_five_region_soft_clusters hq h12 h23 h34 h4L Φ h0 h1
  refine ⟨hJ, e, x, E, hx, hxe, he, hE0, hEC, ?_⟩
  intro p t m hpl hpu ht hm G M
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse, hclusters⟩ :=
      hfamily {0, 2, 4} p t m hpl hpu ht hm
  change G.IsHermitian at hG
  have hnorm : ‖G‖ ≤ M := norm_five_region_soft_three_bulk_le
    h12 h23 h34 h4L hwindow1 hwindow3 Φ h0 h1
    e x hx hxe he p t m hpl hpu ht (by omega)
  refine ⟨hG, hnorm, ?_⟩
  intro Hraw hRaw mu0 g tau T0 T1 hmu0 hg htau htau1 hgap
    hT0 htt hT1 hO hR xi original
  have hC4 : (J.card : ℝ) ≤ 4 := by exact_mod_cast hJ
  have hmu30 : -30 ≤ mu := by
    norm_num at hmuD
    exact hmuD
  obtain ⟨hT0actual, htactual, hT1actual, hOactual, hRactual⟩ :=
    soft_cluster_scalar_residual_budgets hC4 hEC hmu30 hg hT0 htt hT1 hO hR
  have hS : ({0, 2, 4} : Finset (Fin 5)).card = 3 := by decide
  simp only [hS, Nat.cast_ofNat, show (10 : ℝ) * 3 = 30 by norm_num] at hclusters
  obtain ⟨hshift, _hsoft, _hdim, _hsoftRaw, _hrawSoft, happrox⟩ :=
    hclusters mu0 g tau T0 T1 hmu0 hg htau htau1 hgap
      hT0actual htactual hT1actual hOactual hRactual
  obtain ⟨hxi, hxi1, hLo, hHi⟩ := soft_cluster_actual_window_losses
    (norm_nonneg G) hnorm hE0 (hEC.trans hC4) hg htau
  refine ⟨hxi, hxi1, hshift, ?_⟩
  intro Bhat hBhat herr target
  obtain ⟨hclosed, hdim, htargetOriginal, horiginalTarget⟩ :=
    happrox Bhat hBhat xi hxi herr
      (hLo.trans_lt (by linarith only [htau1] : tau / 400 < 1))
      (hHi.trans_lt (by linarith only [htau1] : tau / 400 < 1))
  refine ⟨hclosed, hdim, ?_, ?_⟩
  · exact htargetOriginal.of_le (by linarith only [hLo])
  · exact horiginalTarget.of_le (by linarith only [hHi])

end TNLean.MPS.AreaLaw.ALVV

end FiveRegionSoftUniformClusters
