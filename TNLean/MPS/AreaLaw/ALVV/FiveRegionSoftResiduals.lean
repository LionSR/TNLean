/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftStructure
import TNLean.MPS.AreaLaw.ALVV.SoftFamilyResiduals

/-!
# Two physical residuals for simultaneous estimated-center soft replacements

The original nearest-neighbour chain determines all five regional minima, the original
low-energy space and the actual simultaneous soft Hamiltonian. The estimated centers may
range throughout the source's ten-unit lower interval. The threshold retains the actual
number of crossing bonds and selected replacements.

These are corrected auxiliary bounds for ALVV, arXiv:1602.08828v2, `def:soft-trunc`,
`lem:exp-approx` and `t:aisefficient`, lines 1178–1255 and 1373–1392. They do not assert
the false printed uniform energy estimate, the printed cluster estimate or the complete
efficient-filter parameter theorem. See `docs/paper-gaps/alvv16_soft_regional_residuals.tex`
and `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The same actual simultaneous soft Hamiltonian has original-side and reverse residual
bounds, uniformly over estimated regional centers in their full ten-unit lower intervals.
Regional minima and original ground data precede every soft choice; the constructed soft
ground data precede every spectral width and tail cutoff. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc`, `lem:exp-approx` and `t:aisefficient`,
lines 1178–1255 and 1373–1392. No successful approximation, gap or denominator is assumed. -/
theorem exists_five_region_soft_residuals {L q k1 k2 k3 k4 : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
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
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      H.IsHermitian ∧
      ∃ (bH : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
        (aH : (Fin L → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧ ∀ (S : Finset (Fin 5)) (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ S, e j - 10 ≤ p j) → (∀ j ∈ S, p j ≤ e j) → 0 < t → 2 ≤ m →
        let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
        let D := 10 * (S.card : ℝ)
        let G := B + Y
        ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ), G.IsHermitian ∧
          (B + (D : ℂ) • 1).PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧
          G *ᵥ w = (mu : ℂ) • w ∧ (G - (mu : ℂ) • 1).PosSemidef ∧
          -D ≤ mu ∧ mu ≤ E ∧ mu ≤ (J.card : ℝ) ∧
          ∃ (bG : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
            (aG : (Fin L → Fin q) → ℝ),
            (∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) G (bG v) =
              (aG v : ℂ) • bG v) ∧
          (∀ eta T : ℝ, 0 ≤ eta → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bH aH (E + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) *
                Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T : ℝ, 0 ≤ eta →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T →
            ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bG aG (mu + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hHY, _hBraw, hz, hHz,
      hE, hE0, hEC, hH, hfamily⟩ :=
    exists_five_region_soft_structure hq h12 h23 h34 h4L h hs h0 h1
  refine ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC, hH,
    hH.eigenvectorBasis, hH.eigenvalues, hH.toEuclideanCLM_eigenvectorBasis, ?_⟩
  intro S p t m hpl hpu ht hm B D G
  have hm' : 1 ≤ m := by omega
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC, _hBA, _hproj⟩ :=
    hfamily S p t m hpl hpu ht hm'
  have hk : Monotone k := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [k] <;> omega
  refine ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    hG.eigenvectorBasis, hG.eigenvalues, hG.toEuclideanCLM_eigenvectorBasis, ?_, ?_⟩
  · intro eta T heta hT
    have hEigenH (v : Fin L → Fin q) :
        toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          ((∑ j, (A j - (e j : ℂ) • 1)) + Y) (hH.eigenvectorBasis v) =
          (hH.eigenvalues v : ℂ) • hH.eigenvectorBasis v := by
      rw [← hHY]
      exact hH.toEuclideanCLM_eigenvectorBasis v
    have hres := norm_simultaneous_soft_original_residual k hk J h hs h0 h1
      e p S t m ht hm' hpl hpu he hH.eigenvectorBasis hH.eigenvalues hEigenH
        E eta T hEC heta hT
    have hdiff : ((∑ j, (A j - (e j : ℂ) • 1)) + Y) - G =
        ((∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1) - G := by
      rw [← hHY]
    rw [hdiff] at hres
    exact hres
  · intro eta T heta U hscale hT
    have hres := norm_simultaneous_soft_reverse_residual k hk J h hs h0 h1
      e p S t m ht hm hpl hpu he hG.eigenvectorBasis hG.eigenvalues
        hG.toEuclideanCLM_eigenvectorBasis mu eta T hmuC heta hscale hT
    have hdiff : ((∑ j, (A j - (e j : ℂ) • 1)) + Y) - G =
        ((∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1) - G := by
      rw [← hHY]
    rw [hdiff] at hres
    exact hres

end TNLean.MPS.AreaLaw.ALVV
