/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftTruncationOriginalResidual
import TNLean.MPS.AreaLaw.RegionalBarrierResidual
import QICLean.Analysis.SoftTruncationHighProjection

/-!
# Actual low-soft-energy regional residuals

The original interactions determine the soft Hamiltonian, its ground energy and its
boundary. The reverse estimate uses a derived high-energy floor, not an assumed reverse
residual or spectral gap. This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255. Independent scale and order are retained.

**Scope restriction (attained energy centers):** the centers are constructed exact regional
minimum energies. Uniformity over every estimated center in the source's interval of width
ten is a separate step, recorded in `docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
The corrected reverse estimate retains its explicit scale and threshold conditions and
does not assert the printed uniform energy estimate or the full efficient-filter theorem.
-/

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The actual three-region soft sum is positive, commutes with the original middle
regional sum away from its crossing bonds, and obeys the derived high-projection order.
Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
private theorem three_region_soft_order {L q l r : ℕ} (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (e : Fin 3 → ℝ)
    (he : ∀ j, (aklvRegionalHamiltonians l r h j - (e j : ℂ) • 1).PosSemidef)
    (t : ℝ) (m : ℕ) (ht : 0 < t) (hm : 1 ≤ m) :
    let A := aklvRegionalHamiltonians l r h
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
    let X := A 1 - (e 1 : ℂ) • 1
    let B := (A 0 - (e 0 : ℂ) • 1) + cfc (Real.softTruncation t m) X +
      (A 2 - (e 2 : ℂ) • 1)
    let G := H - X + cfc (Real.softTruncation t m) X
    J.card ≤ 2 ∧ G = B + Y ∧ B.PosSemidef ∧ G.PosSemidef ∧ G ≤ H ∧
      (A 1).IsHermitian ∧ Commute B (A 1) ∧
      ∀ R : ℝ, 0 ≤ R →
        (R - (t / (m : ℝ)) * (R / t) ^ m) • spectralProjectionGE (A 1) (e 1 + R) ≤ B := by
  intro A J Y H X B G
  let k : Fin 4 → ℕ := ![0, l, r, L]
  have hk : Monotone k := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [k] <;> omega
  have hcomm : Pairwise fun i j : Fin 3 ↦ Commute (A i) (A j) :=
    pairwise_commute_sum_internal_consecutive_regions k hk h hs
  have hX : X.PosSemidef := he 1
  have hA1 : (A 1).IsHermitian := by
    dsimp only [A, aklvRegionalHamiltonians]
    exact (posSemidef_sum _ (fun i _ ↦ (h0 i).posSemidef)).isHermitian
  have hf0 : 0 ≤ cfc (Real.softTruncation t m) X :=
    cfc_nonneg fun u hu ↦ (Real.softTruncation_bounds t m u ht hm
      (spectrum_nonneg_of_nonneg hX.nonneg hu)).1
  have hfX : cfc (Real.softTruncation t m) X ≤ X := by
    conv_rhs => rw [← cfc_id' ℝ X hX.isHermitian.isSelfAdjoint]
    exact cfc_mono (fun u hu ↦ (Real.softTruncation_bounds t m u ht hm
      (spectrum_nonneg_of_nonneg hX.nonneg hu)).2.1)
      (X.finite_real_spectrum.continuousOn _) (X.finite_real_spectrum.continuousOn _)
  have hB : B.PosSemidef := ((he 0).add hf0.posSemidef).add (he 2)
  have hY : Y.PosSemidef := posSemidef_sum _ (fun i _ ↦ (h0 i).posSemidef)
  have hsum : (∑ i, h i) = (∑ j, A j) + Y := sum_three_regions_add_crossings hlr h
  have hGY : G = B + Y := by
    dsimp only [G, H, B, X]
    rw [hsum]
    simp only [Fin.sum_univ_three, Complex.ofReal_add, add_smul]
    abel
  have hGH : G ≤ H := by
    have hd : G = H + (cfc (Real.softTruncation t m) X - X) := by
      dsimp only [G]
      abel
    rw [hd]
    exact add_le_of_nonpos_right (sub_nonpos.mpr hfX)
  have hfc : Commute (cfc (Real.softTruncation t m) X) (A 1) := by
    change Commute (cfc (Real.softTruncation t m) (A 1 - (e 1 : ℂ) • 1)) (A 1)
    rw [hA1.cfc_sub_smul_one (Real.softTruncation t m) (e 1)]
    exact (Commute.refl (A 1)).cfc_real (fun u : ℝ ↦ Real.softTruncation t m (u - e 1))
  have h0c : Commute (A 0 - (e 0 : ℂ) • 1) (A 1) :=
    (hcomm (by decide : (0 : Fin 3) ≠ 1)).sub_left ((Commute.one_left (A 1)).smul_left _)
  have h2c : Commute (A 2 - (e 2 : ℂ) • 1) (A 1) :=
    (hcomm (by decide : (2 : Fin 3) ≠ 1)).sub_left ((Commute.one_left (A 1)).smul_left _)
  refine ⟨card_two_cut_crossing_le L l r, hGY, hB, hGY.symm ▸ hB.add hY,
    hGH, hA1, (h0c.add_left hfc).add_left h2c, ?_⟩
  intro R hR
  have hproj := hA1.smul_spectralProjectionGE_le_softTruncation (e 1) t R m
    (le_iff.mpr (he 1)) ht hm hR
  have hfB : cfc (Real.softTruncation t m) X ≤ B := by
    change cfc (Real.softTruncation t m) X ≤
      (A 0 - (e 0 : ℂ) • 1) + cfc (Real.softTruncation t m) X + (A 2 - (e 2 : ℂ) • 1)
    exact (le_add_of_nonneg_left (he 0).nonneg).trans
      (le_add_of_nonneg_right (he 2).nonneg)
  exact hproj.trans hfB

/-- The actual two-boundary budget and a derived denominator at least two give the
sixteen-unit exponential coefficient. Auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255. -/
private theorem reverse_tail_coefficient_le {c d T U : ℝ} (hc : c ≤ 2) (hd : 2 ≤ d) :
    (Real.exp (-(1 / 8) * (T - U) - 1) / (1 / 8)) * ((2 * c) / d) ≤
      16 * Real.exp (-(T - U) / 8) := by
  have hratio : (2 * c) / d ≤ 2 := by
    apply (div_le_iff₀ (by linarith only [hd] : 0 < d)).mpr
    linarith only [hc, hd]
  calc
    _ ≤ (Real.exp (-(1 / 8) * (T - U) - 1) / (1 / 8)) * 2 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 16 * Real.exp (-(T - U) / 8) * Real.exp (-1) := by
      rw [show -(1 / 8 : ℝ) * (T - U) - 1 = -(T - U) / 8 + -1 by ring, Real.exp_add]
      ring
    _ ≤ 16 * Real.exp (-(T - U) / 8) * 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by norm_num)) (by positivity)
    _ = _ := mul_one _

open Classical in
/-- The same actual soft replacement has its original-side residual and its reverse
low-soft-energy residual. Regional energies precede the scale and order; the soft ground
energy precedes every width and auxiliary tail cutoff. The original bonds supply the
boundary count, commutation, projection floor and every restricted norm estimate.
This corrected auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255,
retains order at least two and the explicit reverse scale margin. -/
theorem exists_single_region_soft_truncation_residuals {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, aklvRegionalHamiltonians l r h j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (aklvRegionalHamiltonians l r h j - (e j : ℂ) • 1).PosSemidef) ∧
      (∀ j, 0 ≤ e j) ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 2 ∧
      ∃ hH : H.IsHermitian,
        ∀ t : ℝ, ∀ m : ℕ, 0 < t → 2 ≤ m →
          let X := aklvRegionalHamiltonians l r h 1 - (e 1 : ℂ) • 1
          let G := H - X + cfc (Real.softTruncation t m) X
          ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ) (hG : G.IsHermitian),
            G.PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧ G *ᵥ w = (mu : ℂ) • w ∧
            (G - (mu : ℂ) • 1).PosSemidef ∧ 0 ≤ mu ∧ mu ≤ E ∧ mu ≤ 2 ∧
            (∀ eta T : ℝ, 0 < eta → eta + 7 ≤ T →
              ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
                  (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) G).domRestrict
                (Submodule.spectralSpanLE
                  ((isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
                    finrank_euclideanSpace) hH.eigenvalues₀ (E + eta))‖ ≤
                32 * Real.exp (-(T - eta) / 8) + (t / (m : ℝ)) * (T / t) ^ m) ∧
            (∀ eta T : ℝ, 0 ≤ eta → 2 * (eta + 8) ≤ t → 2 * (eta + 8) ≤ T →
              ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
                  (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) G).domRestrict
                (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (mu + eta))‖ ≤
                16 * Real.exp (-(T - 2 * (eta + 8)) / 8) +
                  (t / (m : ℝ)) * (T / t) ^ m) := by
  obtain ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hE, hE0, hE2, hH, hforward⟩ :=
    exists_single_region_original_soft_truncation_residual hq hlr hrL h hs h0 h1
  let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
  refine ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hE, hE0, hE2, hH, ?_⟩
  intro t m ht hm X G
  have hm' : 1 ≤ m := by omega
  let A := aklvRegionalHamiltonians l r h
  let J := Finset.univ.filter
    (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
  let Y := ∑ i ∈ J, h i
  let B := (A 0 - (e 0 : ℂ) • 1) + cfc (Real.softTruncation t m) X +
    (A 2 - (e 2 : ℂ) • 1)
  obtain ⟨hJ, hGY, hBpos, hGpos, hGH, hA1, hBA, hproj⟩ :=
    three_region_soft_order hlr hrL h hs h0 e he t m ht hm'
  change G = B + Y at hGY
  change G.PosSemidef at hGpos
  change G ≤ H at hGH
  change J.card ≤ 2 at hJ
  let hG := hGpos.isHermitian
  have : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨mu, w, hGw, hw, hGlow⟩ := hG.exists_unit_eigenvector_le
  have hmu0 : 0 ≤ mu := hGpos.nonneg_of_normalized_eigenvector mu w hGw hw
  have hmuE : mu ≤ E := by
    have hpos : (H - (mu : ℂ) • 1).PosSemidef := by
      have hp := hGlow.add (le_iff.mp hGH)
      convert hp using 1
      abel
    have hv : (H - (mu : ℂ) • 1) *ᵥ z = ((E - mu : ℝ) : ℂ) • z := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, hHz, Complex.ofReal_sub, sub_smul]
    exact sub_nonneg.mp (hpos.nonneg_of_normalized_eigenvector (E - mu) z hv hz)
  have hmu2 : mu ≤ 2 := hmuE.trans hE2
  refine ⟨mu, w, hG, hGpos, hGH, hw, hGw, hGlow, hmu0, hmuE, hmu2, ?_, ?_⟩
  · intro eta T heta hT
    obtain ⟨_hG, _horder, hres⟩ := hforward eta T t m heta hT ht hm'
    exact hres
  · intro eta T heta hscale hT
    let U := 2 * (eta + 8)
    let b0 := U - (t / (m : ℝ)) * (U / t) ^ m
    let S := Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues (mu + eta)
    let I := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r)
    have hmid : A 1 = ∑ i ∈ I, h i := rfl
    have hmargin := Real.softTruncation_reverse_barrier_margin t m eta mu J.card
      hm heta hmu2 hJ hscale
    have hU0 : 0 ≤ U := hmargin.1
    have hdenom : 2 ≤ b0 - (mu + eta) - 2 * (J.card : ℝ) := hmargin.2.2.2
    have hgap : 2 * (J.card : ℝ) < b0 - (mu + eta) := by linarith only [hdenom]
    have hUT : U ≤ T := hT
    have hT0 : 0 ≤ T := hU0.trans hUT
    have hEigen (v : Fin L → Fin q) :
        toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (B + ∑ i ∈ J, h i) (hG.eigenvectorBasis v) =
          (hG.eigenvalues v : ℂ) • hG.eigenvectorBasis v := by
      change toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (B + Y) (hG.eigenvectorBasis v) = _
      rw [← hGY]
      exact hG.toEuclideanCLM_eigenvectorBasis v
    have hBA' : Commute B (∑ i ∈ I, h i) := by
      rw [← hmid]
      exact hBA
    have hproj' : b0 • spectralProjectionGE (∑ i ∈ I, h i) (e 1 + U) ≤ B := by
      rw [← hmid]
      exact hproj U hU0
    have htail := norm_hard_residual_low_of_barrier I J h
      (fun i _ ↦ hs i) (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) B
      (e 1 + U) b0 (mu + eta) (1 / 8) (e 1 + T)
      (by norm_num) (by norm_num) (_root_.add_le_add (le_refl (e 1)) hUT)
      hBA' hproj' hG.eigenvectorBasis hG.eigenvalues hEigen hgap
    change ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (A 1 - energyTruncation (A 1) (e 1 + T))).domRestrict S‖ ≤
      (Real.exp (-(1 / 8) * ((e 1 + T) - (e 1 + U)) - 1) / (1 / 8)) *
        ((2 * (J.card : ℝ)) / (b0 - (mu + eta) - 2 * (J.card : ℝ))) at htail
    rw [show (e 1 + T) - (e 1 + U) = T - U by ring] at htail
    have hJreal : (J.card : ℝ) ≤ 2 := by exact_mod_cast hJ
    have hhard := htail.trans (reverse_tail_coefficient_le hJreal hdenom)
    have hclip : X - energyTruncation X T = A 1 - energyTruncation (A 1) (e 1 + T) := by
      change A 1 - (e 1 : ℂ) • 1 - energyTruncation (A 1 - (e 1 : ℂ) • 1) T = _
      rw [hA1.energyTruncation_sub_smul_one (e 1) T]
      abel
    have hdsoft : H - G = X - cfc (Real.softTruncation t m) X := by
      dsimp only [G, H]
      abel
    have hcmp := (he 1).norm_softTruncation_residual_domRestrict_le t m T ht hm' hT0 S
    rw [← hdsoft, hclip] at hcmp
    change ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H -
      toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G).domRestrict S‖ ≤
      16 * Real.exp (-(T - U) / 8) + (t / (m : ℝ)) * (T / t) ^ m
    simp only [map_sub] at hcmp hhard
    linarith only [hcmp, hhard]

end TNLean.MPS.AreaLaw.ALVV
