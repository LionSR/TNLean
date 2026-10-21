/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.RangeNestedPatchEnergy
import TNLean.PEPS.AreaLaw.GapMarginalCloseness

/-!
# Uniform marginal closeness at interaction range `R`

For a Hamiltonian of range `R ≥ 1` on a finite induced lattice domain, a single positive
parameter, depending only on `q`, `R`, `J` and `Δ`, controls every marginal of every
normalized minimizing output on the range-`R` nested squares. The estimate holds at
every parameter `0 < κ ≤ 1 / 2` with `C_E κ² ≤ Δ / 1024`, where
`C_E = rangePatchEnergyConstant q R J`. When `C_E > 0` this includes
`rangePatchFilterExponent q R J Δ`; when `C_E = 0` the uniform statement uses `1 / 2`.

**Extension beyond the source:** the source proves the estimate for on-site and
nearest-neighbour interactions; the range-`R` statements are not in the source. The
nearest-neighbour statements are unchanged.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`, read with interactions of
range `R` as in *A two-dimensional area law from a global spectral gap*,
`eq:hamiltonian`; revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean text is reused.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open Classical in
/-- At every parameter `0 < κ ≤ 1 / 2` with `C_E κ² ≤ Δ / 1024`, the full marginal trace
norm is at most one sixteenth for every feasible minimum on the range-`R` nested squares.
The parameter precedes the domain, Hamiltonian, ground vector, squares, regularization
parameter and minimizer.

Extension of polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-marginal-closeness`, to interactions of range `R`. -/
theorem rangeNestedPatch_minimizer_marginal_closeness
    (q R : ℕ) (hR : 1 ≤ R) {J Δ κ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hsmall : rangePatchEnergyConstant q R J * κ ^ 2 ≤ Δ / 1024) :
    ∀ (Λ : Finset (ℤ × ℤ)) (H : LocalHamiltonian Λ q R J) (E₀ : ℝ)
      (Ψ : Lattice.StateSpace Λ q),
      Lattice.IsGappedGroundState Λ q H.operator E₀ Ψ Δ →
      ∀ (center : ℝ × ℝ) (u b : ℝ), 0 ≤ u → 0 < b →
        letI : LinearOrder (Lattice.Site Λ) :=
          (Fintype.equivFin (Lattice.Site Λ)).linearOrder
        let m := AreaLaw.Geometry.rangeNestedPatchCount R u
        let regions : Fin m → Finset (Lattice.Site Λ) :=
          fun j ↦ AreaLaw.Geometry.rangeNestedPatch Λ center R u j
        let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
        let U := dependentGlobalConfigIsometry
          (V := Lattice.Site Λ) (Out := fun _ ↦ Fin q)
        let Ψᵤ := U.symm Ψ
        ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
          x ∈ regularizedPatchDomain
            (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions →
          IsMinOn
            (regularizedPatchObjective (Out := fun _ : Lattice.Site Λ ↦ Fin q)
              regions a b Ψᵤ)
            (regularizedPatchDomain (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions) x →
          ∀ X : Finset (Lattice.Site Λ),
            (CFC.abs
              (normalizedRegularizedPatchMarginal
                (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions a b Ψᵤ x X -
                Entropy.regionState (n := fun _ : Lattice.Site Λ ↦ q) X Ψ)).trace.re ≤
              (1 / 16 : ℝ) := by
  intro Λ H E₀ Ψ hgs center u b hu hb m regions a U Ψᵤ x hx hmin X
  let : LinearOrder (Lattice.Site Λ) := (Fintype.equivFin (Lattice.Site Λ)).linearOrder
  have henergy := (H.rangeNestedPatch_minimizer_energy_le hR hJ Ψ hgs center u κ b
    hu hκ (hκhalf.trans (by norm_num)) hb x hx hmin).trans hsmall
  have hnorm := norm_normalizedRegularizedPatchOutput
    (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions a
    (fun _ ↦ div_nonneg hκ.le (Nat.cast_nonneg m)) hb Ψᵤ
    ((U.symm.norm_map _).trans hgs.1) hx
  have hgap := FiniteProduct.re_trace_abs_reducedPure_sub_le_one_sixteenth_of_energy
    (fun _ : Lattice.Site Λ ↦ Fin q) hgs hΔ ((U.norm_map _).trans hnorm) henergy X
  have hρ := reindex_reducedPure_eq_regionState
    (fun _ : Lattice.Site Λ ↦ Equiv.refl (Fin q)) X Ψᵤ
  simp only [dependentRegionFinEquiv, Equiv.piCongrRight_refl,
    Matrix.reindex_refl_refl] at hρ
  have hU : dependentGlobalFinIsometry
      (fun _ : Lattice.Site Λ ↦ Equiv.refl (Fin q)) Ψᵤ = U Ψᵤ := rfl
  have hΨeq : dependentGlobalConfigIsometry Ψᵤ = Ψ := U.apply_symm_apply _
  rw [hU, hΨeq] at hρ
  simpa only [normalizedRegularizedPatchMarginal, hρ] using hgap

open Classical in
/-- One choice of the patch parameter, depending only on `q`, `R`, `J` and `Δ`, gives full
marginal trace norm at most one sixteenth for every feasible minimum on the range-`R`
nested squares. When `C_E > 0` the choice is `rangePatchFilterExponent q R J Δ`;
otherwise it is `1 / 2`.

Extension of polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`, to interactions of range `R`. -/
theorem exists_uniform_rangeNestedPatch_minimizer_marginal_closeness
    (q R : ℕ) (hR : 1 ≤ R) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (H : LocalHamiltonian Λ q R J) (E₀ : ℝ)
        (Ψ : Lattice.StateSpace Λ q),
        Lattice.IsGappedGroundState Λ q H.operator E₀ Ψ Δ →
        ∀ (center : ℝ × ℝ) (u b : ℝ), 0 ≤ u → 0 < b →
          letI : LinearOrder (Lattice.Site Λ) :=
            (Fintype.equivFin (Lattice.Site Λ)).linearOrder
          let m := AreaLaw.Geometry.rangeNestedPatchCount R u
          let regions : Fin m → Finset (Lattice.Site Λ) :=
            fun j ↦ AreaLaw.Geometry.rangeNestedPatch Λ center R u j
          let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
          let U := dependentGlobalConfigIsometry
            (V := Lattice.Site Λ) (Out := fun _ ↦ Fin q)
          let Ψᵤ := U.symm Ψ
          ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
            x ∈ regularizedPatchDomain
              (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions →
            IsMinOn
              (regularizedPatchObjective (Out := fun _ : Lattice.Site Λ ↦ Fin q)
                regions a b Ψᵤ)
              (regularizedPatchDomain (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions) x →
            ∀ X : Finset (Lattice.Site Λ),
              (CFC.abs
                (normalizedRegularizedPatchMarginal
                  (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions a b Ψᵤ x X -
                  Entropy.regionState (n := fun _ : Lattice.Site Λ ↦ q) X Ψ)).trace.re ≤
                (1 / 16 : ℝ) := by
  rcases (rangePatchEnergyConstant_nonneg q R hJ).eq_or_lt with hC | hC
  · exact ⟨1 / 2, by norm_num, le_rfl, rangeNestedPatch_minimizer_marginal_closeness q R hR
      hJ hΔ (by norm_num) le_rfl (by rw [← hC, zero_mul]; positivity)⟩
  · have hκ : 0 < rangePatchFilterExponent q R J Δ :=
      lt_min (by norm_num) (Real.sqrt_pos.mpr (div_pos hΔ (by positivity)))
    exact ⟨rangePatchFilterExponent q R J Δ, hκ, rangePatchFilterExponent_le_half q R J Δ,
      rangeNestedPatch_minimizer_marginal_closeness q R hR hJ hΔ hκ
        (rangePatchFilterExponent_le_half q R J Δ)
        (mul_sq_le_div_1024_of_le_rangePatchFilterExponent hJ hΔ.le hκ.le le_rfl)⟩

end TNLean.PEPS.Approximation
