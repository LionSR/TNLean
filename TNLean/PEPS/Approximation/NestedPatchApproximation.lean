/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalNestedPatchEntropy
import TNLean.PEPS.Approximation.NestedPatchMarginalCloseness
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimumGrowth
import TNLean.PEPS.AreaLaw.RegularizedPatchRadiusChoice
import TNLean.PEPS.AreaLaw.RegularizedPatchInverseCylinder

/-!
# Uniform approximation in the selected nested cylinders

The square entropy area law and the spectral gap control the actual minimum
of the ordered regularized filter product. An explicit logarithmic regulator
then gives polynomial-dimensional inside spaces and inverse-polynomial error.
The exponent is chosen before the physical instance and the selected square.

**Scope restriction (conditional area law):** The square entropy area law is an
explicit hypothesis `harea`. Its deduction from the original spectral-gap
hypotheses remains to be supplied by the uniform finite-domain area law and its
square specialization. This restriction is recorded in
`docs/paper-gaps/arealaw2d_rectangular_specialization_scope.tex`.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 335–563,
`eq:patch-distance-to-cylinders`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

open scoped BigOperators

namespace TNLean.PEPS.Approximation

/-- The radius exponent `R₀` of the nested cylinders, for a square area law at
the constant `C_A`. It is the explicit radius exponent at
`C_0 = 16 C_S + log 8` with `C_S = max 1 (16 * C_A)` and at the filter exponent
`κ = patchFilterExponent q J Δ`.

Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 362–379 (`C_S` and
`C_Q = 16 C_S`), 409–411 (`C_0 = C_Q + log 8`) and 540–547
(`eq:patch-explicit-radius`), with `κ` from lines 338–343. -/
noncomputable def nestedPatchRadiusExponent (q : ℕ) (J Δ B₀ p C_A : ℝ) : ℝ :=
  regularizedPatchRadiusExponent (16 * max 1 (16 * C_A) + Real.log 8) B₀ p
    (patchFilterExponent q J Δ)

/-- The radius exponent of the nested cylinders is positive
(`03-patches.tex`, lines 540–547). -/
theorem nestedPatchRadiusExponent_pos {q : ℕ} {J Δ B₀ p : ℝ} (C_A : ℝ)
    (hq : 0 < q) (hJ : 0 < J) (hΔ : 0 < Δ) (hB₀ : 0 ≤ B₀) (hp : 0 ≤ p) :
    0 < nestedPatchRadiusExponent q J Δ B₀ p C_A := by
  have hκ := patchFilterExponent_pos_of_pos hq hJ hΔ
  have hC : 0 ≤ 16 * max 1 (16 * C_A) + Real.log 8 :=
    add_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  unfold nestedPatchRadiusExponent regularizedPatchRadiusExponent
  positivity

open Classical in
/-- A square entropy area law at the constant `C_A` gives a sum of nested
regional cylinders with inside dimensions at most `L ^ R₀`, where
`R₀ = nestedPatchRadiusExponent q J Δ B₀ p C_A`. The exponent depends only on
`q`, `J`, `Δ`, `B₀`, `p` and `C_A`. The vector being approximated is the
original ground vector in the full-region coordinates.

This is the large-radius intermediate assertion of the polynomial-PEPS
manuscript, Proposition 4.1, `03-patches.tex`, lines 484–563, especially
`eq:patch-explicit-radius` and `eq:patch-distance-to-cylinders`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem SquareEntropyAreaLawAt.uniform_nestedPatch_cylinders
    {q : ℕ} {J Δ C_A : ℝ} (hA : SquareEntropyAreaLawAt q J Δ C_A) (hq : 2 ≤ q)
    (hJ : 0 < J) (hΔ : 0 < Δ) {B₀ p : ℝ} (hB₀ : 0 < B₀) (hp : 0 < p) :
    ∀ (L : ℕ), 2 ≤ L →
      ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (center : ℝ × ℝ) (u : ℝ), 4 ≤ u → u ≤ B₀ * Real.log L →
          let Λ := AreaLaw.rectangularDomain L L
          letI : LinearOrder (AreaLaw.Site Λ) :=
            (Fintype.equivFin (AreaLaw.Site Λ)).linearOrder
          let m := AreaLaw.Geometry.nestedPatchCount u
          let regions : Fin m → Finset (AreaLaw.Site Λ) :=
            fun j ↦ AreaLaw.Geometry.nestedPatch Λ center u j.val
          let U := dependentGlobalConfigIsometry
            (V := AreaLaw.Site Λ) (Out := fun _ ↦ Fin q)
          let Ωᵤ := U.symm (squareAreaLawState Ω)
          ∃ (S : (j : Fin m) → Submodule ℂ ((regions j → Fin q) → ℂ))
            (v : EuclideanSpace ℂ
              ((w : (Finset.univ : Finset (AreaLaw.Site Λ))) → Fin q)),
            (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤
              (L : ℝ) ^ nestedPatchRadiusExponent q J Δ B₀ p C_A) ∧
            (v : (((w : (Finset.univ : Finset (AreaLaw.Site Λ))) → Fin q) → ℂ)) ∈
              (⨆ j, dependentRegionCylinder
                (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) (regions j) (S j)) ∧
            ‖Ωᵤ - v‖ ≤ (L : ℝ) ^ (-p) := by
  intro L hL h E₀ Ω hgs center u hu huL Λ m regions U Ωᵤ
  let κ := patchFilterExponent q J Δ
  have hκ : 0 < κ := patchFilterExponent_pos_of_pos (by omega) hJ hΔ
  have hclose := nestedPatch_minimizer_marginal_closeness q hJ.le hΔ hκ
    (patchFilterExponent_le_half q J Δ) (mul_patchFilterExponent_sq_le hJ.le hΔ.le)
  let C := max 1 (16 * C_A)
  have hentropy := hA.nestedPatch_entropy_le
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let : LinearOrder (AreaLaw.Site Λ) := (Fintype.equivFin (AreaLaw.Site Λ)).linearOrder
  let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
  let R : ℝ := regularizedPatchRadiusExponent (16 * C + Real.log 8) B₀ p κ * Real.log L
  have hdata : (0 : ℝ) < m ∧ ‖Ωᵤ‖ = 1 ∧ Monotone regions :=
    ⟨Nat.cast_pos.mpr (AreaLaw.Geometry.nestedPatchCount_pos u),
      (U.symm.norm_map _).trans ((norm_squareAreaLawState Ω).trans hgs.1),
      fun i j hij ↦ AreaLaw.Geometry.nestedPatch_mono Λ center u hij⟩
  have ha : (∀ j, 0 < a j) ∧ ∑ j, a j = κ :=
    ⟨fun _ ↦ div_pos hκ hdata.1, by simp [a, div_eq_mul_inv, mul_left_comm, hdata.1.ne']⟩
  have hbounds := regularizedPatchRadiusExponent_bounds (C₀ := 16 * C + Real.log 8)
    (L := (L : ℝ)) (by positivity) hB₀.le hp.le hκ (by exact_mod_cast hL) huL
  have hΩeq : dependentGlobalConfigIsometry Ωᵤ = squareAreaLawState Ω :=
    U.apply_symm_apply _
  have hS (j : Fin m) : Entropy.regionEntropy (n := fun _ : AreaLaw.Site Λ ↦ q) (regions j)
      (dependentGlobalConfigIsometry Ωᵤ) ≤ C * (1 + u) := by
    simpa only [hΩeq] using hentropy L h E₀ Ω hgs center u (by linarith) j
  have hgrowth := log_regularizedPatchMinimum_exp_neg_le_of_entropy_distance
    (n := fun _ : AreaLaw.Site Λ ↦ q) regions hdata.2.2 a ha.1 Ωᵤ hdata.2.1
    hCpos (by linarith : 0 ≤ u) hbounds.2.1 hS
    (fun r _hr x hx hmin j ↦ by
      simpa only [hΩeq] using hclose L h E₀ Ω hgs center u (Real.exp (-r)) hu
        (Real.exp_pos (-r)) x hx hmin (regions j))
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_regularizedPatchObjective
    (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) regions a (Real.exp_pos (-R)) Ωᵤ hdata.2.1
  obtain ⟨S, v, hdim, hv, herr⟩ := exists_mem_iSup_dependentRegionCylinder_norm_sub_le
    (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) regions hdata.2.2 a (fun j ↦ (ha.1 j).le)
    (Real.exp_pos (-R)) Ωᵤ hdata.2.1 hx
  simp only [regularizedPatchObjective_eq_minimum
    (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) regions a (Real.exp (-R)) Ωᵤ hx hmin, ha.2]
    at herr hgrowth
  have hpos : 0 < regularizedPatchMinimum
      (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) regions a (Real.exp (-R)) Ωᵤ ∧ (0 : ℝ) < L :=
    ⟨regularizedPatchMinimum_pos (Out := fun _ : AreaLaw.Site Λ ↦ Fin q)
      regions a (fun j ↦ (ha.1 j).le)
      (Real.exp_pos (-R)) Ωᵤ hdata.2.1, Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) hL)⟩
  have hdim' (j : Fin m) : (Module.finrank ℂ (S j) : ℝ) ≤
      (L : ℝ) ^ regularizedPatchRadiusExponent (16 * C + Real.log 8) B₀ p κ := by
    simpa only [Real.exp_neg, one_div, inv_inv, R, Real.rpow_def_of_pos hpos.2, mul_comm]
      using hdim j
  refine ⟨S, v, hdim', hv, herr.trans ?_⟩
  apply (Real.log_le_log_iff
    (mul_pos hpos.1 (Real.rpow_pos_of_pos (by positivity) _))
    (Real.rpow_pos_of_pos hpos.2 _)).mp
  rw [Real.log_mul hpos.1.ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
    Real.log_rpow (by positivity), Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.exp_ne_zero _), Real.log_exp, Real.log_rpow hpos.2]
  nlinarith only [hgrowth, hbounds.2.2]

open Classical in
/-- The original square entropy area law gives a sum of nested regional cylinders
with polynomially bounded inside dimensions. The exponent is chosen before the
lattice, Hamiltonian, ground vector, center, and admissible radius. It is
`nestedPatchRadiusExponent q J Δ B₀ p C_A` for an area-law constant `C_A`, as in
`SquareEntropyAreaLawAt.uniform_nestedPatch_cylinders`.

This is the large-radius intermediate assertion of the polynomial-PEPS
manuscript, Proposition 4.1, `03-patches.tex`, lines 484–563, especially
`eq:patch-distance-to-cylinders`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The upstream area-law premise is
explicit; this statement alone is not an unconditional proof of Proposition 4.1. -/
theorem SquareEntropyAreaLaw.exists_uniform_nestedPatch_cylinders
    (harea : SquareEntropyAreaLaw) {q : ℕ} (hq : 2 ≤ q)
    {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    {B₀ p : ℝ} (hB₀ : 0 < B₀) (hp : 0 < p) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ (L : ℕ), 2 ≤ L →
        ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
          h.IsGappedGroundState E₀ Ω Δ →
          ∀ (center : ℝ × ℝ) (u : ℝ), 4 ≤ u → u ≤ B₀ * Real.log L →
            let Λ := AreaLaw.rectangularDomain L L
            letI : LinearOrder (AreaLaw.Site Λ) :=
              (Fintype.equivFin (AreaLaw.Site Λ)).linearOrder
            let m := AreaLaw.Geometry.nestedPatchCount u
            let regions : Fin m → Finset (AreaLaw.Site Λ) :=
              fun j ↦ AreaLaw.Geometry.nestedPatch Λ center u j.val
            let U := dependentGlobalConfigIsometry
              (V := AreaLaw.Site Λ) (Out := fun _ ↦ Fin q)
            let Ωᵤ := U.symm (squareAreaLawState Ω)
            ∃ (S : (j : Fin m) → Submodule ℂ ((regions j → Fin q) → ℂ))
              (v : EuclideanSpace ℂ
                ((w : (Finset.univ : Finset (AreaLaw.Site Λ))) → Fin q)),
              (∀ j, (Module.finrank ℂ (S j) : ℝ) ≤ (L : ℝ) ^ R₀) ∧
              (v : (((w : (Finset.univ : Finset (AreaLaw.Site Λ))) → Fin q) → ℂ)) ∈
                (⨆ j, dependentRegionCylinder
                  (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) (regions j) (S j)) ∧
              ‖Ωᵤ - v‖ ≤ (L : ℝ) ^ (-p) := by
  obtain ⟨C_A, hA⟩ := harea.exists_squareEntropyAreaLawAt hq hJ hΔ
  exact ⟨nestedPatchRadiusExponent q J Δ B₀ p C_A,
    nestedPatchRadiusExponent_pos C_A (by omega) hJ hΔ hB₀.le hp.le,
    hA.uniform_nestedPatch_cylinders hq hJ hΔ hB₀ hp⟩

end TNLean.PEPS.Approximation
