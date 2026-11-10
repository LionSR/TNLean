/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalLowDensityFamily

/-!
# Physical improving families at a fixed low-density bandwidth

A constant depending only on the fixed bandwidth determines one window
scale and one polynomial degree. The same physical clipping, polynomial
family and count envelope satisfy both original-window comparisons and
the count-suppression inequality. The numerical count base may exceed the
local dimension; the physical Hamiltonian and local spaces are unchanged.

This is the buffered five-region construction supporting ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.
Assumption (LD), lines 281–284, declares the bandwidth fixed. Dependence
on that fixed bandwidth is retained explicitly in the chosen constant.
This is not the subsequent low-density minimal-dimension argument.

**Scope restriction (interior windows):** The stated five-region geometry
is retained. The buffer `6*w ≤ eta` is the source lower-cutoff condition
after `w = mu/(3*log n)`. Boundary and short intervals remain separate;
see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The tensor decompositions involve several dependent finite configuration types.
/-- A common family for the actual clipped physical Hamiltonian at every
buffered cutoff within a fixed bandwidth. All regional energies, ground
data, polynomial decompositions, spectral ceilings and target comparisons
are derived from the original supported positive contractions. The constant
precedes every chain, local dimension, width and Hamiltonian; the family
precedes every buffered cutoff and viable subspace. There is no global
spectral-gap hypothesis. ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041, with the fixed bandwidth of Assumption (LD), lines 281–284. -/
theorem exists_fixed_bandwidth_five_region_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m a b : ℕ) (w : ℝ), 2 ≤ q → q ≤ m → 0 < w →
      let g := min w 1
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      a + 2 * ell ≤ b → b + 2 * ell ≤ L - 1 →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      (∀ i, 0 ≤ h i) → (∀ i, h i ≤ 1) →
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
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
      let J := interval L (a + ell) (b + ell + 1)
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt (w / (7 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
      lower ≤ higher ∧
      Submodule.IsCloseTo (1 / 200)
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo (1 / 200) lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) ∧
      (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∃ p : Polynomial ℝ, p.natDegree = ell ^ 2 ∧ p.eval (E0 + eta - 2 * w) = 1 ∧
          ∃ M : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
            Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (B (ell : ℝ) e K) (p.map (algebraMap ℝ ℂ))) ∘L
                Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
              ∑ j, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j))
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥(Jᶜ) → Fin q) (M j)) ∧
            ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
                (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
              let grow := ⨆ j : Fin N, S.map
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
              Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
                Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                  (Delta / (1 - delta) ^ 2) grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  obtain ⟨C, hC, hCeta, hregional⟩ :=
    exists_fixed_bandwidth_five_region_regional_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m a b w hq hqm hw g u ell D hab hbL h hs h0 h1
  obtain ⟨hell, hlogD, hphysical⟩ := hregional L q m a b w hq hqm hw
  have hcollar :
      (interval L (a + ell) (b + ell + 1) \ interval L (a + ell) (b + ell + 1)).card +
        (interval L (a + ell) (b + ell + 1) \ interval L (a + ell) (b + ell + 1)).card ≤
          2 * ell := by simp
  exact ⟨hell, hlogD, hphysical hab hbL
    (interval L (a + ell) (b + ell + 1)) hcollar h hs h0 h1⟩

end TNLean.MPS.AreaLaw
