/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NestedPatchEnergy
import TNLean.PEPS.AreaLaw.GapMarginalCloseness
import TNLean.PEPS.AreaLaw.PatchEnergySmallnessScale

/-!
# Uniform marginal closeness at a minimizing nested patch filter

A single positive parameter, depending only on the local dimension, interaction
bound and original spectral gap, controls every marginal of every normalized
minimizing output. The regions and their multiplicities are those of the nested
patch construction.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.

The choice follows from the energy bound for the same minimizing output and
the marginal trace-norm estimate for the original full-system spectral gap.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open Classical in
/-- One choice of the patch parameter gives full marginal trace norm at most
one sixteenth for every feasible minimum. The choice precedes the lattice,
Hamiltonian, ground vector, nested squares, regularization parameter and
minimizer. The original full-system gap is the only spectral hypothesis.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`. -/
theorem exists_uniform_nestedPatch_minimizer_marginal_closeness
    (q : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (center : ℝ × ℝ) (u b : ℝ), 4 ≤ u → 0 < b →
          let Λ := AreaLaw.rectangularDomain L L
          letI : LinearOrder (Lattice.Site Λ) :=
            (Fintype.equivFin (Lattice.Site Λ)).linearOrder
          let m := AreaLaw.Geometry.nestedPatchCount u
          let regions : Fin m → Finset (Lattice.Site Λ) :=
            fun j ↦ AreaLaw.Geometry.nestedPatch Λ center u j
          let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
          let U := dependentGlobalConfigIsometry
            (V := Lattice.Site Λ) (Out := fun _ ↦ Fin q)
          let Ωᵤ := U.symm (squareAreaLawState Ω)
          ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
            x ∈ regularizedPatchDomain
              (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions →
            IsMinOn
              (regularizedPatchObjective (Out := fun _ : Lattice.Site Λ ↦ Fin q)
                regions a b Ωᵤ)
              (regularizedPatchDomain (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions) x →
            ∀ R : Finset (Lattice.Site Λ),
              (CFC.abs
                (normalizedRegularizedPatchMarginal
                  (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions a b Ωᵤ x R -
                  Entropy.regionState (n := fun _ : Lattice.Site Λ ↦ q) R
                    (squareAreaLawState Ω))).trace.re ≤ (1 / 16 : ℝ) := by
  obtain ⟨κ, hκ, hκhalf, hsmall⟩ := Real.exists_pos_le_half_mul_sq_le_div_1024
    (C := 36 * (q : ℝ) ^ 2 * J) (by positivity) hΔ
  refine ⟨κ, hκ, hκhalf, ?_⟩
  intro L h E₀ Ω hgs center u b hu hb Λ m regions a U Ωᵤ x hx hmin R
  let : LinearOrder (Lattice.Site Λ) := (Fintype.equivFin (Lattice.Site Λ)).linearOrder
  have henergy := (h.nestedPatch_minimizer_energy_le hJ hΔ Ω hgs center u κ b
    hu hκ (hκhalf.trans (by norm_num)) hb x hx hmin).trans hsmall
  have hnorm := norm_normalizedRegularizedPatchOutput
    (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions a
    (fun _ ↦ div_nonneg hκ.le (Nat.cast_nonneg m)) hb Ωᵤ
    ((U.symm.norm_map _).trans ((norm_squareAreaLawState Ω).trans hgs.1)) hx
  have hgap := FiniteProduct.re_trace_abs_reducedPure_sub_le_one_sixteenth_of_energy
    (fun _ : Lattice.Site Λ ↦ Fin q)
    (h.isGappedGroundState_toAreaLawHamiltonian hJ hgs) hΔ
    ((U.norm_map _).trans hnorm) henergy R
  have hρ := reindex_reducedPure_eq_regionState
    (fun _ : Lattice.Site Λ ↦ Equiv.refl (Fin q)) R Ωᵤ
  simp only [dependentRegionFinEquiv, Equiv.piCongrRight_refl,
    Matrix.reindex_refl_refl] at hρ
  have hU : dependentGlobalFinIsometry
      (fun _ : Lattice.Site Λ ↦ Equiv.refl (Fin q)) Ωᵤ = U Ωᵤ := rfl
  have hΩeq : dependentGlobalConfigIsometry Ωᵤ = squareAreaLawState Ω :=
    U.apply_symm_apply _
  rw [hU, hΩeq] at hρ
  simpa only [normalizedRegularizedPatchMarginal, hρ] using hgap

end TNLean.PEPS.Approximation
