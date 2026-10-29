/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalScaledSoftTruncationResiduals

/-!
# Two residuals with the same regional and ground energies

The original-window and soft-window constructions have the same attained
regional minima. Equality follows from their normalized ground witnesses;
the corresponding centered original ground energies then agree as well.
Thus both estimates apply to one literal soft Hamiltonian, with its own
actual eigenbasis and ground energy.

**Scope restriction (one interval and equal scale and order):** This is a
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
theorem exists_interval_physical_soft_residuals
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
        ∀ (eps : ℝ) (m : ℕ), e 1 - 10 ≤ eps → eps ≤ e 1 → 0 < m →
          10 ≤ (m : ℝ) / 2 →
          let alpha := (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m
          let Hsoft := H - A 1 + (eps : ℂ) • 1 +
            cfc (Real.softTruncation (m : ℝ) m) (A 1 - (eps : ℂ) • 1)
          let Hsc := Hsoft - (((∑ j, e j) : ℝ) : ℂ) • 1
          ∃ (Es : ℝ) (hHsc : Hsc.IsHermitian),
            Es = minEigenvalue hHsc ∧ Hsoft ≤ H ∧ -alpha ≤ Es ∧ Es ≤ E0 ∧
            ∀ eta : ℝ, 0 ≤ eta → 17 + eta + alpha ≤ (m : ℝ) / 2 →
              ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (H - Hsoft)).domRestrict (Submodule.spectralSpanLE hHc.eigenvectorBasis
                  hHc.eigenvalues (E0 + eta))‖ ≤
                    80 * Real.exp ((17 + eta) / 8 - (m : ℝ) / 16) ∧
              ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (H - Hsoft)).domRestrict (Submodule.spectralSpanLE hHsc.eigenvectorBasis
                  hHsc.eigenvalues (Es + eta))‖ ≤
                    80 * Real.exp ((17 + eta + alpha) / 8 - (m : ℝ) / 16) := by
  intro _inst k A
  obtain ⟨e, E0, x, hHc, hxunit, hx, he, hEcan, hE0, hE2, hres⟩ :=
    exists_interval_physical_scaled_soft_residuals L q p r hq hpr hrL h hs h0 h1
  refine ⟨e, E0, x, hHc, hxunit, hx, he, hEcan, hE0, hE2, ?_⟩
  intro eps m hepslo hepshi hm htau
  exact hres eps m (m : ℝ) hepslo hepshi hm (Nat.cast_pos.mpr hm)
    (le_mul_of_one_le_left (Nat.cast_nonneg m) (by norm_num)) htau

end TNLean.MPS.AreaLaw
