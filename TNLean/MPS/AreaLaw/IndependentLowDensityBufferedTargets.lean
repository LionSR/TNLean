/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IndependentFiveRegionResidual
import QICLean.Analysis.LowEnergyOrder
import QICLean.Analysis.EuclideanEigenvectorBasis
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Buffered original low-energy targets at an independent clipping threshold

The integer window length and the real clipping threshold are independent.
The original regional minima and centered ground energy are constructed
from the actual positive-contraction nearest-neighbour terms. One residual
budget on the fixed bandwidth gives both original-to-clipped comparisons,
with no spectral gap or invariance premise. The norm ceiling remains
`3*t + 4*ell`, retaining the two scales needed for sharp approximation.

This is a conditional physical auxiliary to ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041, using the hard-truncation comparison
at lines 927–1005. Its explicit numerical budget is to be discharged by the
accuracy-dependent scalar choice.

**Scope restriction (interior windows):** The five-region fit conditions and
buffer `6*w ≤ eta` are explicit; see
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The ceiling budget when the centered ground energy lies in `[0,4]`.
The constants are those of the physical five-region normalization.
ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968. -/
private theorem five_region_spectral_window_budget
    (E0 eta xi w delta : ℝ) (hE0 : 0 ≤ E0) (hE04 : E0 ≤ 4)
    (heta : 0 ≤ eta) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hw : 0 ≤ w) (hdelta : 0 ≤ delta)
    (hsmall : 2 * (6 + eta) * xi ≤ delta * w ^ 2) :
    (⌈(E0 + eta) / (2 * xi)⌉₊ : ℝ) * (xi + xi) ^ 2 ≤
      delta * (w + xi) ^ 2 := by
  have hc := (Nat.ceil_lt_add_one (div_nonneg (add_nonneg hE0 heta)
    (by positivity : 0 ≤ 2 * xi))).le
  calc
    _ ≤ ((E0 + eta) / (2 * xi) + 1) * (xi + xi) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = 2 * (E0 + eta) * xi + 4 * xi ^ 2 := by field_simp; ring
    _ ≤ 2 * (6 + eta) * xi := by
      nlinarith only [mul_nonneg hxi.le (sub_nonneg.mpr hxi1),
        mul_nonneg (sub_nonneg.mpr hE04) hxi.le]
    _ ≤ delta * w ^ 2 := hsmall
    _ ≤ delta * (w + xi) ^ 2 := by gcongr; linarith only [hxi]

/-- Actual buffered targets at an arbitrary nonnegative error under a common
explicit scalar residual budget. All spectral and ground data are derived
from the physical terms. The scalar hypotheses are discharged in the
fixed-bandwidth family theorem. This supports ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_five_region_independent_low_energy_targets_of_residual_budget_at_error
    (L q a b ell : ℕ) (t etaLD w delta : ℝ)
    (ht : 0 ≤ t) (hw : 0 < w) (hdelta : 0 ≤ delta)
    (hcut : 19 + etaLD ≤ t)
    (hxi1 : (288 * Real.exp (11 / 8)) *
      Real.exp (-(t - etaLD) / 8) ≤ 1)
    (hsmall : 2 * (6 + etaLD) * ((288 * Real.exp (11 / 8)) *
      Real.exp (-(t - etaLD) / 8)) ≤ delta * w ^ 2)
    (hq : 2 ≤ q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B : ℝ → (Fin 5 → ℝ) → Finset (Fin 5) →
        Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun t e T ↦
      (∑ j, ((if j ∈ T then
        cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
          (e j : ℂ) • 1)) + Y
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      lower ≤ higher ∧
      Submodule.IsCloseTo delta
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo delta lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) := by
  classical
  intro k A Cross Y K B
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, hres⟩ :=
    exists_five_region_independent_truncation_residual L q a b ell t
      (by omega) hell ht (hab.trans (Nat.le_succ b))
      (hbL.trans (Nat.sub_le L 1)) h hs h0 h1
  have hpos (T : Finset (Fin 5)) : (B t e T).PosSemidef :=
    (Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t T
      (fun j ↦ (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian)
      (fun j ↦ Matrix.le_iff.mpr (hlo j)) x hx ht).1.add
      (show Y.PosSemidef from Matrix.nonneg_iff_posSemidef.mp
        (Finset.sum_nonneg fun i _ ↦ h0 i))
  refine ⟨e, E0, x, z, (hpos ∅).isHermitian, (hpos K).isHermitian,
    hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, ?_⟩
  intro eta hbuffer hetaLD lower higher
  have heigen (T : Finset (Fin 5)) (j : Fin L → Fin q) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e T)
          ((hpos T).isHermitian.eigenvectorBasis j) =
        ((hpos T).isHermitian.eigenvalues j : ℂ) •
          (hpos T).isHermitian.eigenvectorBasis j :=
    (hpos T).isHermitian.toEuclideanCLM_eigenvectorBasis j
  have hresBound (T : Finset (Fin 5)) (c : ℝ) (hc : 0 < c) (hce : c ≤ etaLD) :
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (B t e ∅ - B t e K)).domRestrict
        (Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
          (hpos T).isHermitian.eigenvalues (E0 + c))‖ ≤
        (288 * Real.exp (11 / 8)) * Real.exp (-(t - etaLD) / 8) :=
    (hres T c hc.le (by linarith only [hcut, hce])
      (hpos T).isHermitian.eigenvectorBasis (hpos T).isHermitian.eigenvalues (heigen T)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hce]))
        (by positivity))
  have hpert (T : Finset (Fin 5)) (c : ℝ) (hc : 0 < c) (hce : c ≤ etaLD)
      (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : v ∈ Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
        (hpos T).isHermitian.eigenvalues (E0 + c)) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e ∅) v -
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e K) v‖ ≤
        ((288 * Real.exp (11 / 8)) * Real.exp (-(t - etaLD) / 8)) * ‖v‖ := by
    simpa only [map_sub, ContinuousLinearMap.coe_domRestrict, Set.domRestrict_apply,
      _root_.sub_apply, ← Submodule.norm_coe] using
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (B t e ∅ - B t e K)).domRestrict
          (Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
            (hpos T).isHermitian.eigenvalues (E0 + c))).le_of_opNorm_le
              (hresBound T c hc hce) ⟨v, hv⟩
  have hclose (c : ℝ) (hc : 0 < c) (hce : c ≤ etaLD) :
      Submodule.IsCloseTo delta
          (Submodule.spectralSpanLE (hpos K).isHermitian.eigenvectorBasis
            (hpos K).isHermitian.eigenvalues (E0 + c + w))
          (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
            (hpos ∅).isHermitian.eigenvalues (E0 + c)) ∧
        Submodule.IsCloseTo delta
          (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
            (hpos ∅).isHermitian.eigenvalues (E0 + c + w))
          (Submodule.spectralSpanLE (hpos K).isHermitian.eigenvectorBasis
            (hpos K).isHermitian.eigenvalues (E0 + c)) := by
    let xi := (288 * Real.exp (11 / 8)) * Real.exp (-(t - etaLD) / 8)
    have hxi : 0 < xi := by positivity
    have hsmallc : 2 * (6 + c) * xi ≤ delta * w ^ 2 :=
      (mul_le_mul_of_nonneg_right (by linarith only [hce]) hxi.le).trans hsmall
    have hbudget := five_region_spectral_window_budget E0 c xi w delta hE0 hE04
      hc.le hxi hxi1 hw.le hdelta hsmallc
    refine ⟨Submodule.isCloseTo_spectralSpanLE_of_perturbation
      (hpos ∅).isHermitian.eigenvectorBasis (hpos K).isHermitian.eigenvectorBasis
      (hpos ∅).isHermitian.eigenvalues (hpos K).isHermitian.eigenvalues
      (heigen ∅) (heigen K) (hpert ∅ c hc hce) hxi
      (fun j _ ↦ (hpos ∅).eigenvalues_nonneg j) (by linarith only [hE0, hc])
      (by linarith only [hw])
      (by simpa only [sub_zero, add_sub_cancel_left] using hbudget), ?_⟩
    exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      (hpos K).isHermitian.eigenvectorBasis (hpos ∅).isHermitian.eigenvectorBasis
      (hpos K).isHermitian.eigenvalues (hpos ∅).isHermitian.eigenvalues
      (heigen K) (heigen ∅)
      (fun v hv ↦ (norm_sub_rev _ _).trans_le (hpert K c hc hce v hv)) hxi
      (fun j _ ↦ (hpos K).eigenvalues_nonneg j) (by linarith only [hE0, hc])
      (by linarith only [hw])
      (by simpa only [sub_zero, add_sub_cancel_left] using hbudget)
  have hupperClose : Submodule.IsCloseTo delta
      (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
        (hpos ∅).isHermitian.eigenvalues (E0 + eta)) higher := by
    simpa only [higher,
      show E0 + (eta - w) = E0 + eta - w by ring,
      show E0 + eta - w + w = E0 + eta by ring] using
      (hclose (eta - w) (by linarith only [hbuffer, hw]) (by linarith only [hw, hetaLD])).2
  have hlowerClose : Submodule.IsCloseTo delta lower
      (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
        (hpos ∅).isHermitian.eigenvalues (E0 + eta - 3 * w)) := by
    simpa only [lower,
      show E0 + (eta - 3 * w) = E0 + eta - 3 * w by ring,
      show E0 + eta - 3 * w + w = E0 + eta - 2 * w by ring] using
      (hclose (eta - 3 * w) (by linarith only [hbuffer, hw]) (by linarith only [hw, hetaLD])).1
  have hnest : lower ≤ higher := Submodule.spectralSpanLE_mono_cutoff
    (hpos K).isHermitian.eigenvectorBasis (hpos K).isHermitian.eigenvalues
    (by linarith only [hw])
  exact ⟨hnest, hupperClose, hlowerClose⟩

end TNLean.MPS.AreaLaw
