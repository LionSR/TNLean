/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.DyadicRegionalLowDensityFamily

/-!
# Word families of the regional low-density filter

Every word of length `a` in the regional low-density family improves the
upper low-energy target to the lower one with suppression `Delta ^ a`. This is
the word clause of the general regional construction.

This supports ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041, with the repeated filter of Theorem `t:alg1`,
lines 1777–1817, used by Theorem `t:alg2`, lines 1869–1878.

**Scope restriction (interior windows):** The stated five-region geometry
is retained, as in the general construction; see
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator TensorProduct

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The actual fixed-bandwidth physical filter family on any prescribed
region whose symmetric difference with the native retained interval contains
at most `2*ell` sites. The scalar bounds are chosen before geometry and the
Hamiltonian. The numerical base grows by powers of two before the family is constructed.
The actual residual gives comparison loss `1 / (200 * 2^(4*i))`.
The same global clipped polynomial supplies the regional operators, and
its exact collar cost fits the same count envelope used in the suppression
bound. Every word of length `a` in the family improves the upper target to
the lower one with the suppression raised to the power `a`, as in the
repeated filter of Theorem `t:alg1`, lines 1777–1817, used by Theorem
`t:alg2`, lines 1869–1878. ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041, and Proposition 5.7, lines 1311–1333. -/
theorem exists_fixed_bandwidth_regional_dyadic_low_energy_word_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m a b i : ℕ) (w : ℝ), 2 ≤ q → q ≤ m → 0 < w →
      let mi := m * 2 ^ i
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      let nu := (1 / 200 : ℝ) / 2 ^ (4 * i)
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
      ∀ (_hab : a + 2 * ell ≤ b) (_hbL : b + 2 * ell ≤ L - 1),
      ∀ Jtarget : Finset (Fin L),
      (interval L (a + ell) (b + ell + 1) \ Jtarget).card +
        (Jtarget \ interval L (a + ell) (b + ell + 1)).card ≤ 2 * ell →
      ∀ (Φ : ManyBody.BondInteraction L q),
      (∀ i, 0 ≤ Φ.term i) → (∀ i, Φ.term i ≤ 1) →
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i
    let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, Φ.term i
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
      B (ell : ℝ) e ∅ = Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B (ell : ℝ) e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B (ell : ℝ) e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      ‖B (ell : ℝ) e K‖ ≤ 7 * (ell : ℝ) ∧
      let J := Jtarget
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
        (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
        (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt (w / (7 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
      lower ≤ higher ∧
      Submodule.IsCloseTo nu
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta)) higher ∧
      Submodule.IsCloseTo nu lower
        (Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w)) ∧
      (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∃ p : Polynomial ℝ, p.natDegree = ell ^ 2 ∧ p.eval (E0 + eta - 2 * w) = 1 ∧
          ∃ M : Fin N → Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ,
            Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (B (ell : ℝ) e K) (p.map (algebraMap ℝ ℂ))) ∘L
                Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
              ∑ j, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j))
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := {v // v ∉ J} → Fin q) (M j)) ∧
            ∀ (a : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
              Submodule.IsViable (F := EuclideanSpace ℂ ({v // v ∉ J} → Fin q)) delta S
                (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
              let grow := ⨆ v : Fin a → Fin N, S.map ((List.ofFn (fun j ↦
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W (v j)))).prod :
                  _ →ₗ[ℂ] _)
              Module.finrank ℂ grow ≤ N ^ a * Module.finrank ℂ S ∧
                Submodule.IsViable (F := EuclideanSpace ℂ ({v // v ∉ J} → Fin q))
                  (Delta ^ a / (1 - delta) ^ 2) grow
                  (lower.map Tm.toLinearEquiv.toLinearMap) :=
  exists_fixed_bandwidth_regional_dyadic_low_energy_family_of_clause etaLD hLD _
    (fun _ _ _ _ _ _ _ _ h ↦ h)

end TNLean.MPS.AreaLaw
