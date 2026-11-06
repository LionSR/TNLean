/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IndependentLowDensityBufferedTargets

/-!
# Buffered physical low-energy targets at one clipping scale

The actual three-bulk truncation with threshold equal to the window scale
has norm at most seven times that scale. A common residual budget over a
fixed bandwidth supplies both comparisons between the original and clipped
spectral spaces. The regional minima, centered ground energy and spectral
bases are constructed from the original supported positive contractions.

This is a conditional supporting comparison for ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.
The fixed-bandwidth scalar theorem discharges its explicit residual budget.
There is no assumption on a global spectral gap.

**Scope restriction (interior windows):** The five-region fit conditions
and the buffer `6*w ≤ eta` are explicit. Extending the construction to
all intervals is separate; see
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Actual buffered targets at an arbitrary nonnegative error under a common
explicit scalar residual budget. All spectral and ground data are derived
from the physical terms. The scalar hypotheses are discharged in the
fixed-bandwidth family theorem. This supports ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_five_region_low_energy_targets_of_residual_budget_at_error
    (L q a b ell : ℕ) (etaLD w delta : ℝ)
    (hw : 0 < w) (hdelta : 0 ≤ delta)
    (hcut : 19 + etaLD ≤ (ell : ℝ))
    (hxi1 : (288 * Real.exp (11 / 8)) *
      Real.exp (-((ell : ℝ) - etaLD) / 8) ≤ 1)
    (hsmall : 2 * (6 + etaLD) * ((288 * Real.exp (11 / 8)) *
      Real.exp (-((ell : ℝ) - etaLD) / 8)) ≤ delta * w ^ 2)
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
      (hO : (B (ell : ℝ) e ∅).IsHermitian) (hC : (B (ell : ℝ) e K).IsHermitian),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B (ell : ℝ) e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B (ell : ℝ) e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B (ell : ℝ) e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B (ell : ℝ) e K‖ ≤ 7 * (ell : ℝ) ∧
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
  intro k A Cross Y K B
  obtain ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz,
    hE0low, hE0, hE04, hnorm, htargets⟩ :=
    exists_five_region_independent_low_energy_targets_of_residual_budget_at_error
      L q a b ell (ell : ℝ) etaLD w delta (Nat.cast_nonneg ell) hw hdelta
      hcut hxi1 hsmall hq hell hab hbL h hs h0 h1
  exact ⟨e, E0, x, z, hO, hC, hxunit, hx, hlo, hcenter, hzunit, hz,
    hE0low, hE0, hE04, by linarith only [hnorm], htargets⟩

/-- Actual buffered targets for a five-region Hamiltonian under a common
explicit scalar residual budget. All spectral and ground data are derived
from the physical terms. The scalar hypotheses are discharged in the
fixed-bandwidth family theorem. This supports ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_five_region_low_energy_targets_of_residual_budget
    (L q a b ell : ℕ) (etaLD w : ℝ)
    (hw : 0 < w)
    (hcut : 19 + etaLD ≤ (ell : ℝ))
    (hxi1 : (288 * Real.exp (11 / 8)) *
      Real.exp (-((ell : ℝ) - etaLD) / 8) ≤ 1)
    (hsmall : 2 * (6 + etaLD) * ((288 * Real.exp (11 / 8)) *
      Real.exp (-((ell : ℝ) - etaLD) / 8)) ≤ (1 / 200) * w ^ 2)
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
      (hO : (B (ell : ℝ) e ∅).IsHermitian) (hC : (B (ell : ℝ) e K).IsHermitian),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B (ell : ℝ) e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B (ell : ℝ) e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B (ell : ℝ) e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B (ell : ℝ) e K‖ ≤ 7 * (ell : ℝ) ∧
      ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      lower ≤ higher ∧
      Submodule.IsCloseTo (1 / 200)
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo (1 / 200) lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) := by
  exact exists_five_region_low_energy_targets_of_residual_budget_at_error
    L q a b ell etaLD w (1 / 200) hw (by norm_num) hcut hxi1 hsmall
    hq hell hab hbL h hs h0 h1

end TNLean.MPS.AreaLaw
