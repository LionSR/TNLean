/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalScaledSoftTruncationReverse

/-!
# Two residuals with the same regional and ground energies

The original-window and soft-window constructions have the same attained
regional minima. Equality follows from their normalized ground witnesses;
the corresponding centered original ground energies then agree as well.
Thus both estimates apply to one literal soft Hamiltonian, with its own
actual eigenbasis and ground energy.

**Scope restriction (one interval and independent bounded scale):** The positive scale
is at most four times the positive order. This is a
corrected auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc` and
`lem:exp-approx`, lines 1178–1255. The reverse estimate retains its explicit
scale condition. The false printed uniform energy estimate is discussed in
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Both actual residuals can be obtained with the same original regional
minima and the same original ground energy. The returned ground energies are
identified with the canonical minima of the actual centered matrices.
Supporting ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem exists_interval_physical_scaled_soft_residuals
    (L q p r : ℕ) (hq : 0 < q) (hpr : p ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let k : Fin 6 → ℕ := ![0, p, r, r, r, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x : (Fin L → Fin q) → ℂ),
      let H := ∑ i, h i
      let Hc := H - (((∑ j, e j) : ℝ) : ℂ) • 1
      ∃ hHc : Hc.IsHermitian,
        star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 = minEigenvalue hHc ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
        ∀ (eps : ℝ) (m : ℕ) (t : ℝ), e 1 - 10 ≤ eps → eps ≤ e 1 → 0 < m → 0 < t → t ≤ 4 * m →
          10 ≤ t / 2 →
          let alpha := t / 2 * (1 / 2 : ℝ) ^ m
          let Hsoft := H - A 1 + (eps : ℂ) • 1 +
            cfc (Real.softTruncation t m) (A 1 - (eps : ℂ) • 1)
          let Hsc := Hsoft - (((∑ j, e j) : ℝ) : ℂ) • 1
          ∃ (Es : ℝ) (hHsc : Hsc.IsHermitian),
            Es = minEigenvalue hHsc ∧ Hsoft ≤ H ∧ -alpha ≤ Es ∧ Es ≤ E0 ∧
            ∀ eta : ℝ, 0 ≤ eta → 17 + eta + alpha ≤ t / 2 →
              ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (H - Hsoft)).domRestrict (Submodule.spectralSpanLE hHc.eigenvectorBasis
                  hHc.eigenvalues (E0 + eta))‖ ≤
                    80 * Real.exp ((17 + eta) / 8 - t / 16) ∧
              ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (H - Hsoft)).domRestrict (Submodule.spectralSpanLE hHsc.eigenvectorBasis
                  hHsc.eigenvalues (Es + eta))‖ ≤
                    80 * Real.exp ((17 + eta + alpha) / 8 - t / 16) := by
  classical
  intro _inst k A
  obtain ⟨e, E0, x, z, hO, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, hforward⟩ :=
    exists_interval_physical_scaled_soft_truncation_residual L q p r hq hpr hrL h hs h0 h1
  obtain ⟨er, Er, xr, zr, hOr, hxrunit, hxr, her, hzrunit, hzr, hErlow,
    _hEr0, _hEr2, hreverse⟩ :=
    exists_interval_physical_scaled_soft_reverse_residual L q p r hq hpr hrL h hs h0 h1
  have heq : er = e := by
    funext j
    exact Matrix.groundEnergy_eq_of_normalized_eigenvectors (A j) (er j) (e j)
      xr x (hxr j) hxrunit (hx j) hxunit (her j) (he j)
  subst er
  have hEq : Er = E0 := Matrix.groundEnergy_eq_of_normalized_eigenvectors
    ((∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1) Er E0 zr z
      hzr hzrunit hz hzunit hErlow hElow
  subst Er
  refine ⟨e, E0, x, ?_⟩
  intro H Hc
  refine ⟨hO, hxunit, hx, he, ?_, hE0, hE2, ?_⟩
  · have hc := hO.minEigenvalue_eq_add_of_centered_ground 0 E0 z hzunit
      (by simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hz)
      (by simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hElow)
    simpa only [add_zero] using hc.symm
  intro eps m t hepslo hepshi hm ht htm htau alpha Hsoft Hsc
  obtain ⟨Es, zs, hS, hsoftH, hzsunit, hzs, hEslow, hElowsoft, hEs0, hres⟩ :=
    hreverse eps m t hepslo hepshi hm ht htm htau
  refine ⟨Es, hS, ?_, hsoftH, hElowsoft, hEs0, ?_⟩
  · have hc := hS.minEigenvalue_eq_add_of_centered_ground 0 Es zs hzsunit
      (by simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hzs)
      (by simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hEslow)
    simpa only [add_zero] using hc.symm
  intro eta heta hscale
  exact ⟨(hforward eps eta m t hepslo hepshi heta hm ht htm).2.2, hres eta heta hscale⟩

end TNLean.MPS.AreaLaw
