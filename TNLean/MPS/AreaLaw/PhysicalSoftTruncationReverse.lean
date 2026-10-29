/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalScaledSoftTruncationReverse

/-!
# The physical soft-truncation residual on the soft spectral window

The actual soft Hamiltonian is compared with a hard truncation only in matrix
order. The resulting high-projection coercivity controls an exponential moment
on its own low-energy space. The scalar remainder then bounds the difference
from the original Hamiltonian on that same space.

**Scope restriction (one interval and equal scale and order):** The order and
scale are one positive integer, and the explicit condition
`m / 2 ≥ 17 + eta + alpha`, with `alpha = (m / 2) * 2 ^ (-m)`, is retained.
This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc`
and `lem:exp-approx`, lines 1178–1255. It does not assert the printed first
uniform energy estimate or a spectral-subspace comparison. See
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual soft Hamiltonian has an attained ground energy and an
exponentially small residual on its own low-energy window. Original regional
minima are chosen before the approximate regional energy and order; the soft
ground data are chosen before the bandwidth. No moment, residual, gap or
ground-space-rank hypothesis is supplied. Corrected auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`, lines 1178–1255. -/
theorem exists_interval_physical_soft_reverse_residual
    (L q p r : ℕ) (hq : 0 < q) (hpr : p ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, p, r, r, r, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ),
      let H := ∑ i, h i
      let Hc := H - (((∑ j, e j) : ℝ) : ℂ) • 1
      ∃ _hHc : Hc.IsHermitian,
        star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        star z ⬝ᵥ z = 1 ∧ Hc *ᵥ z = (E0 : ℂ) • z ∧
        (Hc - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
        ∀ (eps : ℝ) (m : ℕ), e 1 - 10 ≤ eps → eps ≤ e 1 → 0 < m →
          10 ≤ (m : ℝ) / 2 →
          let alpha := (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m
          let Hsoft := H - A 1 + (eps : ℂ) • 1 +
            cfc (Real.softTruncation (m : ℝ) m) (A 1 - (eps : ℂ) • 1)
          let Hsc := Hsoft - (((∑ j, e j) : ℝ) : ℂ) • 1
          ∃ (Es : ℝ) (zs : (Fin L → Fin q) → ℂ) (hHsc : Hsc.IsHermitian),
            Hsoft ≤ H ∧ star zs ⬝ᵥ zs = 1 ∧ Hsc *ᵥ zs = (Es : ℂ) • zs ∧
            (Hsc - (Es : ℂ) • 1).PosSemidef ∧ -alpha ≤ Es ∧ Es ≤ E0 ∧
            ∀ eta : ℝ, 0 ≤ eta → 17 + eta + alpha ≤ (m : ℝ) / 2 →
              let G := Submodule.spectralSpanLE hHsc.eigenvectorBasis
                hHsc.eigenvalues (Es + eta)
              ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                (H - Hsoft)).domRestrict G‖ ≤
                  80 * Real.exp ((17 + eta + alpha) / 8 - (m : ℝ) / 16) := by
  intro k A
  obtain ⟨e, E0, x, z, hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, hres⟩ :=
    exists_interval_physical_scaled_soft_reverse_residual L q p r hq hpr hrL h hs h0 h1
  refine ⟨e, E0, x, z, hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, ?_⟩
  intro eps m hepslo hepshi hm htau
  exact hres eps m (m : ℝ) hepslo hepshi hm (Nat.cast_pos.mpr hm)
    (le_mul_of_one_le_left (Nat.cast_nonneg m) (by norm_num)) htau

end TNLean.MPS.AreaLaw
