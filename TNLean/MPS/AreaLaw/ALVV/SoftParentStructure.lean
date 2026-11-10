/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalBondRestriction
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftResiduals
import QICLean.Analysis.SoftTruncationOperatorBounds
import QICLean.Analysis.GroundEnergyResidual

/-!
# The actual central soft replacement inside a parent interval

The original parent bonds determine the central soft term, unchanged
collars, actual ground energies and a uniform reverse residual. Estimated
centers retain their ten-unit correction and the logarithmic harmonic cap.
This is an auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:generate`,
lines 1348–1392. The source energy-estimation target remains separate.

**Scope restriction (estimated center and centered norm):** The estimate
lies below the actual middle minimum by at most ten. The proved norm bound
is after subtracting the attained soft minimum. These conditions are not
identified with the broader absolute-error input or uncentered norm in the
printed efficient-generation theorem. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`. The harmonic cap is
corrected as documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_soft_truncation_log_bound.pdf.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

private theorem middle_soft_parent_cap {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Fin 5 → Matrix σ σ ℂ) (e : Fin 5 → ℝ)
    (Y : Matrix σ σ ℂ) (p t a b : ℝ) (m : ℕ)
    (he : ∀ j, 0 ≤ e j) (hpu : p ≤ e 2)
    (hX : (A 2 - (p : ℂ) • 1).PosSemidef) (ht : 0 < t) (hm : 1 ≤ m)
    (hA0 : A 0 = 0) (hA4 : A 4 = 0)
    (hA1 : A 1 ≤ a • 1) (hA3 : A 3 ≤ b • 1) (hY : Y ≤ (4 : ℝ) • 1) :
    (∑ j, ((if j = 2 then (p : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) else A j) - (e j : ℂ) • 1)) + Y ≤
      (a + t * (1 + Real.log (m : ℝ)) + b + 4) • 1 := by
  classical
  let cap := t * (1 + Real.log (m : ℝ))
  let c : Fin 5 → ℝ := ![0, a, cap, b, 0]
  let F := fun j : Fin 5 ↦ (if j = 2 then (p : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) else A j) - (e j : ℂ) • 1
  have hraw (j : Fin 5) (d : ℝ) (hd : A j ≤ d • 1) : A j - (e j : ℂ) • 1 ≤ d • 1 := by
    apply (sub_le_self (A j) ?_).trans hd
    rw [Complex.coe_smul]
    exact smul_nonneg (he j) zero_le_one
  have hsoft : (p : ℂ) • (1 : Matrix σ σ ℂ) +
      cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) - (e 2 : ℂ) • 1 ≤ cap • 1 := by
    calc
      _ ≤ (e 2 : ℂ) • 1 + cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) -
          (e 2 : ℂ) • 1 := by
        apply sub_le_sub_right
        apply _root_.add_le_add _ (le_refl _)
        simpa only [Complex.coe_smul] using
          smul_le_smul_of_nonneg_right hpu (zero_le_one : (0 : Matrix σ σ ℂ) ≤ 1)
      _ = cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) := by abel
      _ ≤ cap • 1 := hX.cfc_softTruncation_le_scalar t m ht hm
  have hFc (j : Fin 5) : F j ≤ c j • 1 := by
    fin_cases j
    · simpa [F, c, hA0] using hraw 0 0 (by simp [hA0])
    · simpa [F, c] using hraw 1 a hA1
    · simpa [F, c] using hsoft
    · simpa [F, c] using hraw 3 b hA3
    · simpa [F, c, hA4] using hraw 4 0 (by simp [hA4])
  have hsum : (∑ j, F j) + Y ≤ (∑ j, c j • (1 : Matrix σ σ ℂ)) + (4 : ℝ) • 1 :=
    add_le_add (Finset.sum_le_sum (fun j _ ↦ hFc j)) hY
  change (∑ j, F j) + Y ≤ (a + cap + b + 4) • 1
  calc
    _ ≤ (∑ j, c j • (1 : Matrix σ σ ℂ)) + (4 : ℝ) • 1 := hsum
    _ = (a + cap + b + 4) • 1 := by
      simp only [← Finset.sum_smul, Fin.sum_univ_five]
      norm_num [c]
      module

/-- Actual original parent bonds construct the central estimated-center
soft replacement and its true ground energy. The unchanged collars give
an explicit norm bound, and the actual reverse residual bounds the
minimum shift. All ground data precede the auxiliary tail cutoff.
This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:generate`, lines 1348–1392; no efficient-generation claim is made. -/
theorem exists_soft_parent_structure {L q l u v r ell : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let hp := intervalBondRestriction l r h
    let k : Fin 6 → ℕ := ![0, l, u, v, r, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ ∑ i ∈ I j, hp i
    let P := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r), h i
    ∃ (e : Fin 5 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ (∀ j, 0 ≤ e j) ∧
      let s := ∑ j, e j
      let C := P - (s : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ C *ᵥ z = (E : ℂ) • z ∧
      (C - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 4 ∧
      ∀ (p t : ℝ) (m : ℕ), e 2 - 10 ≤ p → p ≤ e 2 → 0 < t → 2 ≤ m →
        let B := P - A 2 + (p : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) - (s : ℂ) • 1
        ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ), B.IsHermitian ∧
          (B + (10 : ℂ) • 1).PosSemidef ∧ B ≤ C ∧
          star w ⬝ᵥ w = 1 ∧ B *ᵥ w = (mu : ℂ) • w ∧
          (B - (mu : ℂ) • 1).PosSemidef ∧ -10 ≤ mu ∧ mu ≤ E ∧
          ‖B - (mu : ℂ) • 1‖ ≤ t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 14 ∧
          ∀ T : ℝ, 48 ≤ t → 48 ≤ T →
            0 ≤ E - mu ∧ E - mu ≤
              32 * Real.exp (-(T - 48) / 8) + (t / (m : ℝ)) * (T / t) ^ m := by
  classical
  intro hp k I A P
  let Cross := Finset.univ.filter
    (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, u, v, r} : Finset ℕ))
  let Y := ∑ i ∈ Cross, hp i
  have hps (i) := intervalBondRestriction_supported l r h hs i
  have hp0 (i) := (intervalBondRestriction_bounds l r h h0 h1 i).1
  have hp1 (i) := (intervalBondRestriction_bounds l r h h0 h1 i).2
  obtain ⟨hCross, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
      _hH, _bH, _aH, _hEigH, hfamily⟩ :=
    exists_five_region_soft_residuals hq hlu huv hvr hrL hp hps hp0 hp1
  obtain ⟨_hk, _hR, _hsA, hA, hYpos, hYcap, _hCross', hsum0⟩ :=
    five_region_original_bond_data L q l u v r hlu huv hvr hrL hp hps hp0 hp1
  have he0 (j : Fin 5) : 0 ≤ e j :=
    (hA j).1.nonneg_of_normalized_eigenvector (e j) x (hxe j) hx
  have hP : ∑ i, hp i = P := sum_intervalBondRestriction l r h
  have hsum : P = (∑ j, A j) + Y := hP.symm.trans hsum0
  let s := ∑ j, e j
  let C := P - (s : ℂ) • 1
  have hHz' : C *ᵥ z = (E : ℂ) • z := by simpa only [hP] using hHz
  have hE' : (C - (E : ℂ) • 1).PosSemidef := by simpa only [hP] using hE
  have hE4 : E ≤ 4 := hEC.trans (by exact_mod_cast hCross)
  refine ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz', hE', hE0, hE4, ?_⟩
  intro p t m hpl hpu ht hm B
  let S : Finset (Fin 5) := {2}
  let pvec := Function.update e (2 : Fin 5) p
  have hpL : ∀ j ∈ S, e j - 10 ≤ pvec j := by
    intro j hj
    have hj' : j = 2 := Finset.mem_singleton.mp hj
    subst j
    simpa only [pvec, Function.update_self] using hpl
  have hpU : ∀ j ∈ S, pvec j ≤ e j := by
    intro j hj
    have hj' : j = 2 := Finset.mem_singleton.mp hj
    subst j
    simpa only [pvec, Function.update_self] using hpu
  let F := fun j : Fin 5 ↦ (pvec j : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A j - (pvec j : ℂ) • 1)
  let B0 := (∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) + Y
  obtain ⟨mu, w, hB0, hBpos0, hBC0, hw, hBw0, hBlow0, hmuD, hmuE, _hmuC,
      bG, aG, hEigG, _hforward, hreverse⟩ := hfamily S pvec t m hpL hpU ht hm
  have hF2 : F 2 = (p : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) := by
    simp only [F, pvec, Function.update_self]
  have hcenter : (∑ j, (A j - (e j : ℂ) • 1)) + Y = C := by
    dsimp only [C, s]
    rw [hsum, Finset.sum_sub_distrib]
    push_cast
    rw [Finset.sum_smul]
    abel
  have hB0eq : B0 = B := by
    have hdiff := sum_centered_sub_partially_replaced_eq A F
      (fun j ↦ (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) S
    simp only [S, Finset.sum_singleton] at hdiff
    calc
      B0 = (∑ j, (A j - (e j : ℂ) • 1)) + Y - (A 2 - F 2) := by
        rw [← hdiff]
        dsimp only [B0]
        abel
      _ = B := by rw [hcenter, hF2]; dsimp only [B, C]; abel
  have hB : B.IsHermitian := hB0eq ▸ hB0
  have hBpos : (B + (10 : ℂ) • 1).PosSemidef := by
    change ((∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) +
      (((10 * (S.card : ℝ)) : ℝ) : ℂ) • 1).PosSemidef at hBpos0
    have hfull := hBpos0.add hYpos
    have heq : ((∑ j, ((if j ∈ S then F j else A j) - (e j : ℂ) • 1)) +
        (((10 * (S.card : ℝ)) : ℝ) : ℂ) • 1) + Y = B + (10 : ℂ) • 1 := by
      have hD : (((10 * (S.card : ℝ)) : ℝ) : ℂ) = 10 := by norm_num [S]
      rw [hD, ← hB0eq]
      dsimp only [B0]
      abel
    exact heq ▸ hfull
  have hBC : B ≤ C := by
    change B0 ≤ (∑ i, hp i) - (s : ℂ) • 1 at hBC0
    rw [hB0eq, hP] at hBC0
    exact hBC0
  have hBw : B *ᵥ w = (mu : ℂ) • w := hB0eq ▸ hBw0
  have hBlow : (B - (mu : ℂ) • 1).PosSemidef := hB0eq ▸ hBlow0
  have hmu10 : -10 ≤ mu := by
    simpa only [S, Finset.card_singleton, Nat.cast_one, mul_one] using hmuD
  refine ⟨mu, w, hB, hBpos, hBC, hw, hBw, hBlow, hmu10, hmuE, ?_, ?_⟩
  · have hA0 : A 0 = 0 := (sum_exterior_intervalBondRestriction l r h).1
    have hA4 : A 4 = 0 := (sum_exterior_intervalBondRestriction l r h).2
    have hcard1 : (I 1).card ≤ 2 * ell :=
      (card_internal_bonds_le L l u).trans (by omega)
    have hcard3 : (I 3).card ≤ 2 * ell :=
      (card_internal_bonds_le L v r).trans (by omega)
    have hcap1 : A 1 ≤ (2 * (ell : ℝ)) • 1 :=
      (hA 1).2.trans (smul_le_smul_of_nonneg_right (by exact_mod_cast hcard1) zero_le_one)
    have hcap3 : A 3 ≤ (2 * (ell : ℝ)) • 1 :=
      (hA 3).2.trans (smul_le_smul_of_nonneg_right (by exact_mod_cast hcard3) zero_le_one)
    have hcapY : Y ≤ (4 : ℝ) • 1 := hYcap.trans
      (smul_le_smul_of_nonneg_right (by exact_mod_cast hCross) zero_le_one)
    have hpe : (p : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤
        (e 2 : ℂ) • 1 := by
      simpa only [Complex.coe_smul] using
        smul_le_smul_of_nonneg_right hpu
          (zero_le_one : (0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ 1)
    have hX : (A 2 - (p : ℂ) • 1).PosSemidef :=
      le_iff.mp (hpe.trans (le_iff.mpr (he 2)))
    have hform : B0 = (∑ j : Fin 5, ((if j = 2 then
        (p : ℂ) • 1 + cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) else A j) -
          (e j : ℂ) • 1)) + Y := by
      dsimp only [B0]
      congr 1
    have hcap0 := middle_soft_parent_cap A e Y p t (2 * (ell : ℝ))
      (2 * (ell : ℝ)) m he0 hpu hX ht (by omega) hA0 hA4 hcap1 hcap3 hcapY
    let cap := t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 4
    have hBcap : B ≤ cap • 1 := by
      rw [← hB0eq, hform]
      convert hcap0 using 1
      dsimp only [cap]
      congr 1
      ring
    have hCcap : B - (mu : ℂ) • 1 ≤ (cap + 10) • 1 := by
      rw [Complex.coe_smul]
      calc
        _ ≤ cap • 1 - mu • 1 := sub_le_sub_right hBcap _
        _ = (cap - mu) • 1 := (sub_smul cap mu 1).symm
        _ ≤ (cap + 10) • 1 := smul_le_smul_of_nonneg_right (by linarith only [hmu10]) zero_le_one
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hnorm := (CStarAlgebra.norm_le_iff_le_algebraMap (B - (mu : ℂ) • 1)
      (by dsimp only [cap]; positivity : 0 ≤ cap + 10) hBlow.nonneg).mpr
        (by simpa only [Algebra.algebraMap_eq_smul_one] using hCcap)
    dsimp only [cap] at hnorm
    linarith only [hnorm]
  · intro T ht48 hT48
    let U0 := 2 * (10 + 3 * (Cross.card : ℝ) + 2)
    have hcardC : (Cross.card : ℝ) ≤ 4 := by exact_mod_cast hCross
    have hU0 : U0 ≤ 48 := by dsimp only [U0]; linarith only [hcardC]
    have hscale : 2 * (0 + 10 * (S.card : ℝ) + 3 * (Cross.card : ℝ) + 2) ≤ t := by
      simpa only [U0, S, Finset.card_singleton, Nat.cast_one, _root_.mul_one,
        _root_.zero_add] using hU0.trans ht48
    have hcut : 2 * (0 + 10 * (S.card : ℝ) + 3 * (Cross.card : ℝ) + 2) ≤ T := by
      simpa only [U0, S, Finset.card_singleton, Nat.cast_one, _root_.mul_one,
        _root_.zero_add] using hU0.trans hT48
    have hrev0 := hreverse 0 T le_rfl hscale hcut
    change ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        ((∑ i, hp i) - (s : ℂ) • 1 - B0)).domRestrict
        (Submodule.spectralSpanLE bG aG (mu + 0))‖ ≤
      (S.card : ℝ) * (8 * (Cross.card : ℝ) * Real.exp
        (-(T - 2 * (0 + 10 * (S.card : ℝ) + 3 * (Cross.card : ℝ) + 2)) / 8) +
          (t / (m : ℝ)) * (T / t) ^ m) at hrev0
    have hScard : (S.card : ℝ) = 1 := by simp [S]
    rw [hP, hScard] at hrev0
    have hres : ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (C - B0)).domRestrict
        (Submodule.spectralSpanLE bG aG (mu + 0))‖ ≤
          8 * (Cross.card : ℝ) * Real.exp (-(T - U0) / 8) + (t / (m : ℝ)) * (T / t) ^ m := by
      simpa only [_root_.mul_one, _root_.one_mul, _root_.zero_add] using hrev0
    let wE : EuclideanSpace ℂ (Fin L → Fin q) :=
      (EuclideanSpace.equiv (Fin L → Fin q) ℂ).symm w
    have hwnorm : ‖wE‖ = 1 := by
      have hsquare := re_star_dotProduct_self_eq_norm_sq w
      rw [hw] at hsquare
      change (1 : ℝ) = ‖wE‖ ^ 2 at hsquare
      nlinarith only [hsquare, norm_nonneg wE]
    have hwEigen : toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B0 wE =
        (mu : ℂ) • wE := by
      change (EuclideanSpace.equiv (Fin L → Fin q) ℂ).symm (B0 *ᵥ w) = _
      have hBw' : B0 *ᵥ w = (mu : ℂ) • w := hBw0
      rw [hBw', map_smul]
    have hEig : ∀ j, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) B0 (bG j) =
        (aG j : ℂ) • bG j := hEigG
    have hshift := energy_sub_eigenvalue_le_norm_spectral_residual C B0 E mu (mu + 0)
      hE' bG aG hEig wE hwnorm hwEigen (by simp only [_root_.add_zero]; exact le_rfl)
    refine ⟨sub_nonneg.mpr hmuE, (hshift.trans hres).trans ?_⟩
    apply _root_.add_le_add _ (le_refl _)
    apply mul_le_mul
    · linarith only [hcardC]
    · exact Real.exp_le_exp.mpr (by linarith only [hU0])
    · exact Real.exp_nonneg _
    · norm_num

end TNLean.MPS.AreaLaw.ALVV
