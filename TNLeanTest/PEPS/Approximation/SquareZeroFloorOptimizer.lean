/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareZeroFloorOptimizer

/-! Signature regressions for the original-square zero-floor maximizing family. -/

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.Approximation

variable {L q m : ℕ} {J E₀ Δ : ℝ}
variable [LinearOrder (Lattice.Site (AreaLaw.rectangularDomain L L))]

/-- The selected family gives the usual divided fidelity estimate for a positive gap.
No positivity of the individual original terms or gap on a subregion is assumed. -/
example (h : SquareHamiltonian L q J) (hΔ : 0 < Δ)
    {Ω : StateSpace L q} (hΩ : h.IsGappedGroundState E₀ Ω Δ)
    (D : ℕ → Finset (Lattice.Site (AreaLaw.rectangularDomain L L)))
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (hsingle : ∀ e : Edge (Lattice.domainGraph (AreaLaw.rectangularDomain L L)),
      ∀ i j : Fin m,
        s(e.1.1, e.1.2) ∈ Lattice.edgeBoundary (AreaLaw.rectangularDomain L L) (D i) →
        s(e.1.1, e.1.2) ∈ Lattice.edgeBoundary (AreaLaw.rectangularDomain L L) (D j) →
        i = j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1) :
    ∃ K : (j : Fin m) → Matrix
        (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j))
        (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j)) ℂ,
      (∀ j : Fin m, Entropy.IsFeasibleFilter 0 (a j) (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix
          (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j))
          (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j)) ℂ,
        (∀ j : Fin m, Entropy.IsFeasibleFilter 0 (a j) (K' j)) →
        ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K' fun _ ↦ True))
            (squareAreaLawState Ω)‖ ≤
          ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
            (squareAreaLawState Ω)‖) ∧
      let ψ := toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
        (squareAreaLawState Ω)
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧
        |(⟪φ, toEuclideanLin h.toAreaLawHamiltonian.operator φ⟫_ℂ).re - E₀| ≤
          (q : ℝ) ^ 2 * J * ∑ j : Fin m,
            a j ^ 2 * (Lattice.edgeBoundary (AreaLaw.rectangularDomain L L) (D j)).card ∧
        1 - ((q : ℝ) ^ 2 * J * ∑ j : Fin m,
          a j ^ 2 * (Lattice.edgeBoundary (AreaLaw.rectangularDomain L L) (D j)).card) / Δ ≤
            ‖⟪squareAreaLawState Ω, φ⟫_ℂ‖ ^ 2 := by
  obtain ⟨K, hK, hmax, hpos, hunit, henergy, hfidelity⟩ :=
    h.exists_zero_floor_maximizer_energy_fidelity hΩ D hD hsingle a ha ha1
  refine ⟨K, hK, hmax, hpos, hunit, henergy, ?_⟩
  have hdiv := (le_div_iff₀' hΔ).mpr hfidelity
  linarith

/-- The endpoint weight one is allowed and retains the global maximum and nonzero output. -/
example (h : SquareHamiltonian L q J)
    {Ω : StateSpace L q} (hΩ : h.IsGappedGroundState E₀ Ω Δ)
    (D : ℕ → Finset (Lattice.Site (AreaLaw.rectangularDomain L L)))
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (hsingle : ∀ e : Edge (Lattice.domainGraph (AreaLaw.rectangularDomain L L)),
      ∀ i j : Fin m,
        s(e.1.1, e.1.2) ∈ Lattice.edgeBoundary (AreaLaw.rectangularDomain L L) (D i) →
        s(e.1.1, e.1.2) ∈ Lattice.edgeBoundary (AreaLaw.rectangularDomain L L) (D j) →
        i = j) :
    ∃ K : (j : Fin m) → Matrix
        (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j))
        (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j)) ℂ,
      (∀ j : Fin m, Entropy.IsFeasibleFilter 0 1 (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix
          (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j))
          (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j)) ℂ,
        (∀ j : Fin m, Entropy.IsFeasibleFilter 0 1 (K' j)) →
        ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K' fun _ ↦ True))
            (squareAreaLawState Ω)‖ ≤
          ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
            (squareAreaLawState Ω)‖) ∧
      0 < ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
        (squareAreaLawState Ω)‖ := by
  obtain ⟨K, hK, hmax, hpos, _⟩ :=
    h.exists_zero_floor_maximizer_energy_fidelity hΩ D hD hsingle
      (fun _ ↦ 1) (fun _ ↦ zero_lt_one) (fun _ ↦ le_rfl)
  exact ⟨K, hK, hmax, hpos⟩

/-- The zero-length chain is admitted, with zero energy and infidelity budgets. -/
example (h : SquareHamiltonian L q J)
    {Ω : StateSpace L q} (hΩ : h.IsGappedGroundState E₀ Ω Δ)
    (D : ℕ → Finset (Lattice.Site (AreaLaw.rectangularDomain L L))) :
    ∃ K : (j : Fin 0) → Matrix
        (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j))
        (Entropy.RegionConfig (fun _ : Lattice.Site (AreaLaw.rectangularDomain L L) ↦ q) (D j)) ℂ,
      let ψ := toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
        (squareAreaLawState Ω)
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧
        |(⟪φ, toEuclideanLin h.toAreaLawHamiltonian.operator φ⟫_ℂ).re - E₀| ≤ 0 ∧
        Δ * (1 - ‖⟪squareAreaLawState Ω, φ⟫_ℂ‖ ^ 2) ≤ 0 := by
  obtain ⟨K, _, _, hpos, hunit, henergy, hfidelity⟩ :=
    h.exists_zero_floor_maximizer_energy_fidelity (m := 0) hΩ D
      (by intro i; exact Fin.elim0 i) (by intro _ i; exact Fin.elim0 i)
      (fun _ ↦ 1) (fun _ ↦ zero_lt_one) (fun _ ↦ le_rfl)
  exact ⟨K, hpos, hunit, by simpa using henergy, by simpa using hfidelity⟩

end TNLean.PEPS.Approximation
