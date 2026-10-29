/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.RelativeLowEnergyCloseness
import TNLean.MPS.AreaLaw.ALVV.HardTruncationResidual

/-!
# Physical hard truncation: ordered energies and relative low-energy spaces

Original positive-contraction nearest-neighbour bonds determine the middle
regional clipping and both physical restricted errors. These errors give ordered
eigenvalue comparison, actual ground-energy displacement, and closeness in both
directions relative to each operator's own actual ground energy. The matrices
use the same derived sum of regional minima as a scalar shift.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3, Proposition 4.4 and Lemma 4.5,
`local_alg_arxiv_v2.tex`, lines 873–968.

**Local fix (cutoff and window count):** The physical cutoff is the explicit
sufficient `t ≥ η + 7`, rather than the printed unrestricted `t > η`. The
relative enlargement includes the actual ceiling window count and ground shift.
See https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf
and the pending revision and prerequisite gates recorded in
`docs/audits/2026-10-29_physical_hard_truncation_capstone.md`.
-/

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ALVV

private theorem canonical_last_eq_minEigenvalue {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) :
    let jmin : Fin (Fintype.card n) :=
      ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩
    hM.eigenvalues₀ jmin = minEigenvalue hM := by
  intro jmin
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  apply le_antisymm
  · obtain ⟨i, hi⟩ := minEigenvalue_achieved hM
    have hle : e.symm i ≤ jmin := by
      change (e.symm i).val ≤ Fintype.card n - 1
      omega
    have h := hM.eigenvalues₀_antitone hle
    change hM.eigenvalues₀ (e.symm i) = minEigenvalue hM at hi
    exact h.trans_eq hi
  · simpa only [IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
      minEigenvalue_le hM (e jmin)

open Classical in
/-- Actual single-region hard truncation with both physical residuals, ordered
energy comparison and two relative-ground-energy spectral-space comparisons.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3, Proposition 4.4 and Lemma 4.5,
lines 873–968, with the explicit sufficient cutoff and ceiling window count
recorded in the module's companion-note reference. No residual, regional
minimum, eigenbasis or spectral gap is an input. The displayed spectral spaces
belong to the actual operators with their common derived scalar shift. -/
theorem exists_single_region_hard_truncation_spectral_comparison {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let A := aklvRegionalHamiltonians l r h
    let J := Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ (∀ j, 0 ≤ e j) ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 2 ∧
      ∀ η t : ℝ, 0 < η → η + 7 ≤ t →
        let F := energyTruncation (A 1) (e 1 + t) + A 0 + A 2 + Y -
          (((∑ j, e j) : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian)
          (E' : ℝ) (z' : (Fin L → Fin q) → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • 1).PosSemidef ∧ 0 ≤ E' ∧ E' ≤ 2 ∧
          let ξ := 32 * Real.exp (-(t - η) / 8)
          let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
            finrank_euclideanSpace
          let bF := (isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
            finrank_euclideanSpace
          ‖(toEuclideanCLM H - toEuclideanCLM F).domRestrict
            (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η))‖ ≤
              ξ ∧
          ‖(toEuclideanCLM H - toEuclideanCLM F).domRestrict
            (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η))‖ ≤
              ξ ∧
          (∀ i : Fin (Fintype.card (Fin L → Fin q)), hF.eigenvalues₀ i ≤ E + η →
            hF.eigenvalues₀ i ≤ hH.eigenvalues₀ i ∧
              hH.eigenvalues₀ i ≤ hF.eigenvalues₀ i + ξ) ∧
          E' ≤ E ∧ E ≤ E' + ξ ∧
          ∀ δ : ℝ, 0 < δ →
            let η' := η + ξ + 2 * ξ * Real.sqrt ((⌈η / (2 * ξ)⌉₊ : ℝ) / δ)
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η'))
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η)) ∧
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η'))
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η)) := by
  intro A J Y
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hElow, hE0, hE2, hclip⟩ :=
    exists_single_region_hard_truncation_residuals hq hlr hrL h hs h0 h1
  refine ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hElow, hE0, hE2, ?_⟩
  intro η t hη ht F
  obtain ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'2, hresH, hresF⟩ :=
    hclip η t hη ht
  let ξ := 32 * Real.exp (-(t - η) / 8)
  have hξ : 0 < ξ := by dsimp only [ξ]; positivity
  let jmin : Fin (Fintype.card (Fin L → Fin q)) :=
    ⟨Fintype.card (Fin L → Fin q) - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩
  have hminH : minEigenvalue hH = E := by
    simpa using hH.minEigenvalue_eq_add_of_centered_ground 0 E z hz
      (by simpa using hHz) (by simpa using hElow)
  have hminF : minEigenvalue hF = E' := by
    simpa using hF.minEigenvalue_eq_add_of_centered_ground 0 E' z' hz'
      (by simpa using hFz') (by simpa using hE'low)
  have hlastH : hH.eigenvalues₀ jmin = E := (canonical_last_eq_minEigenvalue hH).trans hminH
  have hlastF : hF.eigenvalues₀ jmin = E' := (canonical_last_eq_minEigenvalue hF).trans hminF
  have hcompare (δ : ℝ) (hδ : 0 < δ) :=
    hH.groundEnergy_compare_and_isCloseTo_spectralSpanLE_of_norm_domRestrict_le
      hF hFH η ξ δ hη hξ hδ
  have hresult (δ : ℝ) (hδ : 0 < δ) := by
    have h := hcompare δ hδ
    dsimp only at h
    rw [hlastH, hlastF] at h
    exact h hresH hresF
  obtain ⟨hgroundLower, hgroundUpper, _hcloseH, _hcloseF⟩ := hresult 1 zero_lt_one
  refine ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'2,
    hresH, hresF, ?_, hgroundLower, hgroundUpper, ?_⟩
  · intro i hi
    exact ⟨hF.eigenvalues₀_mono hH hFH i,
      hH.eigenvalues₀_le_add_of_norm_domRestrict_low_le hF (E + η) ξ hresF i hi⟩
  · intro δ hδ
    exact ⟨(hresult δ hδ).2.2.1, (hresult δ hδ).2.2.2⟩

end TNLean.MPS.AreaLaw.ALVV
