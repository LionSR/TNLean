/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.LowEnergy.ChebyshevViability
import QICLean.Spectral.Eigenvalue.MatrixSpectralDecomp
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.PhysicalPolynomialTensorFamily
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.PhysicalLowEnergyCloseness

import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.IndependentFiveRegionResidual
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.ImprovingFamily.ChebyshevNestedViability

/-!
# Buffered physical low-energy targets

A single clipping threshold, chosen before the window, controls the residual of one
physical three-bulk truncation at every cutoff below the prescribed bandwidth. It
supplies the buffered spectral targets of the physical low-energy families in
`TNLean.MPS.AreaLaw.PhysicalLowEnergyFamily`. This supports ALVV, arXiv:1602.08828v2,
`lem:hard-trunc`, lines 955–968, and Theorem `t:aisgapless`, lines 1027–1041.

**Scope restriction (buffers and geometry):** The targets use `3*w < eta` and the
stated interior five-region geometry; see
`docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

**Local fix (closed cutoffs):** The spectral estimates use closed cutoffs; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
-/

open ManyBody (interval)

open Matrix

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator
  ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw


/-- One threshold controls every cutoff below the prescribed bandwidth.
ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968, and
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_common_low_energy_residual_threshold
    (eta w delta : ℝ) (heta : 0 ≤ eta) (hw : 0 < w) (hdelta : 0 < delta) :
    ∃ t : ℝ, t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (delta * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      let xi := (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)
      xi ≤ 1 ∧ 2 * (6 + eta) * xi ≤ delta * w ^ 2 := by
  let C := 288 * Real.exp (11 / 8)
  let z := min 1 (delta * w ^ 2 / (2 * (6 + eta)))
  have hden : 0 < 2 * (6 + eta) := by linarith only [heta]
  have hz : 0 < z := lt_min (by norm_num) (div_pos (by positivity) hden)
  have hz1 : z ≤ 1 := min_le_left _ _
  have hC1 : 1 ≤ C := by
    have he : 1 ≤ Real.exp (11 / 8) := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp only [C]
    linarith only [he]
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hquot : 1 ≤ C / z := (one_le_div hz).mpr (hz1.trans hC1)
  have hlog : 0 ≤ Real.log (C / z) := Real.log_nonneg hquot
  let t := 21 + eta + 8 * Real.log (C / z)
  have harg : -(t - eta) / 8 = -21 / 8 - Real.log (C / z) := by
    dsimp only [t]
    ring
  have htail : C * Real.exp (-(t - eta) / 8) ≤ z := by
    rw [harg, Real.exp_sub, Real.exp_log (div_pos hC hz)]
    have he : Real.exp (-21 / 8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have heq : C * (Real.exp (-21 / 8) / (C / z)) = Real.exp (-21 / 8) * z := by
      field_simp
    rw [heq]
    exact (mul_le_mul_of_nonneg_right he hz.le).trans_eq (one_mul z)
  refine ⟨t, rfl, by dsimp only [t]; linarith only [heta, hlog],
    by dsimp only [t]; linarith only [hlog], htail.trans hz1, ?_⟩
  have hsmall := (le_div_iff₀ hden).mp (min_le_right 1 (delta * w ^ 2 / (2 * (6 + eta))))
  exact (mul_le_mul_of_nonneg_left htail hden.le).trans (by nlinarith only [hsmall])

/-- A single physical clipping threshold supplies both buffered spectral
comparisons. ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041. The bandwidths remain strictly positive. -/
theorem exists_five_region_physical_buffered_targets
    (L q a b ell : ℕ) (eta w epsilon : ℝ)
    (hbuffer : 3 * w < eta) (hw : 0 < w) (hepsilon : 0 < epsilon)
    (hq : 2 ≤ q) (hell : 1 ≤ ell)
    (hab : a + 2 * ell ≤ b) (hbL : b + 2 * ell ≤ L - 1)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
    let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, Φ.term i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B : ℝ → (Fin 5 → ℝ) → Finset (Fin 5) →
        Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun t e T ↦
      (∑ j, ((if j ∈ T then
        cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
          (e j : ℂ) • 1)) + Y
    ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B t e ∅).IsHermitian) (hC : (B t e K).IsHermitian),
      t = 21 + eta + 8 * Real.log
        ((288 * Real.exp (11 / 8)) / min 1 (epsilon * w ^ 2 / (2 * (6 + eta)))) ∧
      21 ≤ t ∧ 19 + eta ≤ t ∧
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B t e ∅ = Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      lower ≤ higher ∧
      Submodule.IsCloseTo epsilon
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo epsilon lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) := by
  classical
  intro k A Cross Y K B
  obtain ⟨t, htformula, ht, hcut, hxi1, hsmall⟩ :=
    exists_common_low_energy_residual_threshold eta w epsilon
      (by linarith only [hw, hbuffer]) hw hepsilon
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, hres⟩ :=
    exists_five_region_independent_truncation_residual L q a b ell t
      (by omega) hell (by linarith only [ht]) (hab.trans (Nat.le_succ b))
      (hbL.trans (Nat.sub_le L 1)) Φ h0 h1
  have hpos (T : Finset (Fin 5)) : (B t e T).PosSemidef :=
    (Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t T
      (fun j ↦ (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian)
      (fun j ↦ Matrix.le_iff.mpr (hlo j)) x hx (by linarith only [ht])).1.add
      (show Y.PosSemidef from Matrix.nonneg_iff_posSemidef.mp
        (Finset.sum_nonneg fun i _ ↦ h0 i))
  refine ⟨t, e, E0, x, z, (hpos ∅).isHermitian, (hpos K).isHermitian,
    htformula, ht, hcut, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, ?_⟩
  intro lower higher
  have heigen (T : Finset (Fin 5)) (j : Fin L → Fin q) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e T)
          ((hpos T).isHermitian.eigenvectorBasis j) =
        ((hpos T).isHermitian.eigenvalues j : ℂ) •
          (hpos T).isHermitian.eigenvectorBasis j :=
    (hpos T).isHermitian.toEuclideanCLM_eigenvectorBasis j
  have hresBound (T : Finset (Fin 5)) (c : ℝ) (hc : 0 < c) (hce : c ≤ eta) :
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (B t e ∅ - B t e K)).domRestrict
        (Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
          (hpos T).isHermitian.eigenvalues (E0 + c))‖ ≤
        (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8) :=
    (hres T c hc.le (by linarith only [hcut, hce])
      (hpos T).isHermitian.eigenvectorBasis (hpos T).isHermitian.eigenvalues (heigen T)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hce]))
        (by positivity))
  have hpert (T : Finset (Fin 5)) (c : ℝ) (hc : 0 < c) (hce : c ≤ eta)
      (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : v ∈ Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
        (hpos T).isHermitian.eigenvalues (E0 + c)) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e ∅) v -
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (B t e K) v‖ ≤
        ((288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)) * ‖v‖ := by
    simpa only [map_sub, ContinuousLinearMap.coe_domRestrict, Set.domRestrict_apply,
      _root_.sub_apply, ← Submodule.norm_coe] using
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (B t e ∅ - B t e K)).domRestrict
          (Submodule.spectralSpanLE (hpos T).isHermitian.eigenvectorBasis
            (hpos T).isHermitian.eigenvalues (E0 + c))).le_of_opNorm_le
              (hresBound T c hc hce) ⟨v, hv⟩
  have hclose (c : ℝ) (hc : 0 < c) (hce : c ≤ eta) :
      Submodule.IsCloseTo epsilon
          (Submodule.spectralSpanLE (hpos K).isHermitian.eigenvectorBasis
            (hpos K).isHermitian.eigenvalues (E0 + c + w))
          (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
            (hpos ∅).isHermitian.eigenvalues (E0 + c)) ∧
        Submodule.IsCloseTo epsilon
          (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
            (hpos ∅).isHermitian.eigenvalues (E0 + c + w))
          (Submodule.spectralSpanLE (hpos K).isHermitian.eigenvectorBasis
            (hpos K).isHermitian.eigenvalues (E0 + c)) := by
    let xi := (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8)
    have hxi : 0 < xi := by positivity
    have hsmallc : 2 * (6 + c) * xi ≤ epsilon * w ^ 2 :=
      (mul_le_mul_of_nonneg_right (by linarith only [hce]) hxi.le).trans hsmall
    have hbudget := Real.spectral_window_budget_bound E0 c xi w epsilon hE0 hE04
      hc.le hxi hxi1 hw.le hepsilon.le hsmallc
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
  have hupperClose : Submodule.IsCloseTo epsilon
      (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
        (hpos ∅).isHermitian.eigenvalues (E0 + eta)) higher := by
    simpa only [higher,
      show E0 + (eta - w) = E0 + eta - w by ring,
      show E0 + eta - w + w = E0 + eta by ring] using
      (hclose (eta - w) (by linarith only [hbuffer, hw]) (by linarith only [hw])).2
  have hlowerClose : Submodule.IsCloseTo epsilon lower
      (Submodule.spectralSpanLE (hpos ∅).isHermitian.eigenvectorBasis
        (hpos ∅).isHermitian.eigenvalues (E0 + eta - 3 * w)) := by
    simpa only [lower,
      show E0 + (eta - 3 * w) = E0 + eta - 3 * w by ring,
      show E0 + eta - 3 * w + w = E0 + eta - 2 * w by ring] using
      (hclose (eta - 3 * w) (sub_pos.mpr hbuffer) (by linarith only [hw])).1
  have hnest : lower ≤ higher := Submodule.span_mono
    (Set.image_mono (fun j hj ↦ hj.trans
      (show E0 + eta - 2 * w ≤ E0 + eta - w by linarith only [hw])))
  exact ⟨hnest, hupperClose, hlowerClose⟩

end TNLean.MPS.AreaLaw
