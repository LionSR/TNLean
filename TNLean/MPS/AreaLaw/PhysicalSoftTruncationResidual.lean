/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalScaledSoftTruncationResidual

/-!
# The physical soft-truncation residual on the original spectral window

The actual regional exponential moment controls the defining soft-truncation
operator on the whole original low-energy window. The scalar remainder is
factored through an exponential of the same regional operator. No moment or
residual estimate is assumed in the physical theorem.

**Scope restriction (equal order and scale):** The order and scale are the
same positive integer. This is a corrected auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`, lines 1175–1255,
rather than the printed first uniform energy estimate or the reverse
spectral comparison. See
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual soft-truncated Hamiltonian has an exponentially small residual
on the actual original low-energy window. Regional minima and original ground
data are constructed before the approximate energy, bandwidth and order. No
moment or residual bound is supplied. ALVV, arXiv:1602.08828v2,
`def:soft-trunc` and `lem:exp-approx`, lines 1175–1255; this is the corrected
equal-order-and-scale residual, rather than the reverse spectral comparison. -/
theorem exists_interval_physical_soft_truncation_residual
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
      ∃ hHc : Hc.IsHermitian,
        star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        star z ⬝ᵥ z = 1 ∧ Hc *ᵥ z = (E0 : ℂ) • z ∧
        (Hc - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
        ∀ (eps eta : ℝ) (m : ℕ), e 1 - 10 ≤ eps → eps ≤ e 1 → 0 ≤ eta → 0 < m →
          let G := Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues (E0 + eta)
          let Hsoft := H - A 1 + (eps : ℂ) • 1 +
            cfc (Real.softTruncation (m : ℝ) m) (A 1 - (eps : ℂ) • 1)
          Hsoft.IsHermitian ∧ Hsoft ≤ H ∧
            ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
              (H - Hsoft)).domRestrict G‖ ≤
              80 * Real.exp ((17 + eta) / 8 - (m : ℝ) / 16) := by
  intro k A
  obtain ⟨e, E0, x, z, hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, hres⟩ :=
    exists_interval_physical_scaled_soft_truncation_residual L q p r hq hpr hrL h hs h0 h1
  refine ⟨e, E0, x, z, hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, ?_⟩
  intro eps eta m hepslo hepshi heta hm
  exact hres eps eta m (m : ℝ) hepslo hepshi heta hm (Nat.cast_pos.mpr hm)
    (le_mul_of_one_le_left (Nat.cast_nonneg m) (by norm_num))

end TNLean.MPS.AreaLaw
