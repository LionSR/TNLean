/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.FunctionalCalculus.MatrixPowers
import TNLean.PEPS.Approximation.GroundState.SquareInteractionTerms
import TNLean.PEPS.AreaLaw.Polygons.Squares.NestedPatches
import TNLean.PEPS.AreaLaw.RegionalStates.RegionalFilters.RegularizedPatchListCoordinates
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.PEPS.AreaLaw.RegionalStates.Regions.GapMarginalCloseness
import TNLean.PEPS.AreaLaw.RegionalStates.RegionalFilters.PatchEnergySmallnessScale

/-!
# Energy of minimizing nested patch filters

For the prescribed nested squares and equal weights, the normalized output at
any feasible minimum has excitation energy at most `36 * q ^ 2 * J * κ ^ 2`.
The filters act on the original ground vector. Their spectral relations follow
from minimality, and each nearest-neighbor interaction crosses at most one
selected boundary. The geometric boundary sum gives the numerical constant.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 213–336,
`eq:patch-energy-bound`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.

## Uniform marginal closeness at a minimizing nested patch filter

A single positive parameter, depending only on the local dimension, interaction
bound and original spectral gap, controls every marginal of every normalized
minimizing output. The regions and their multiplicities are those of the nested
patch construction. The estimate holds at every parameter `0 < κ ≤ 1 / 2` with
`36 q² J κ² ≤ Δ / 1024`, in particular at the filter exponent
`patchFilterExponent q J Δ`.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.

The choice follows from the energy bound for the same minimizing output and
the marginal trace-norm estimate for the original full-system spectral gap.
-/

open ManyBody (Config Qudits SquareLatticeVertex)

section

open ManyBody (Edge SquareInteraction)

open Matrix

open ManyBody (IsGapped groundSpace)
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

open Classical in
/-- The actual normalized regularized output of every feasible patch minimum
has excitation energy at most `36 * q ^ 2 * J * κ ^ 2` for the original square Hamiltonian.
The interaction terms need only have a Hermitian total. Their Hermitian parts
preserve the original sum, supports and norm bound.

The regions are the source-selected nested squares, including repeated clipped
regions. The weights are exactly `κ / m`. Commutation, the first-order trace
inequality, and clipped joint eigenvalues follow from the
minimum. No density is assumed nonsingular.

Source: polynomial-PEPS Proposition 4.1, 03-patches.tex, lines 213–336,
eq:patch-single-crossing, eq:patch-one-term-energy and eq:patch-energy-bound;
00-introduction.tex, eq:model and eq:global-gap. -/
theorem _root_.ManyBody.SquareInteraction.nestedPatch_minimizer_energy_le
    {L q : ℕ} {J E₀ Δ : ℝ} (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian)
        (hhJ : ∀ i, ‖h.term i‖ ≤ J)
    (hJ : 0 ≤ J) (_hΔ : 0 < Δ)
    (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))) (hΩ : ‖Ω‖ = 1)
    (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (center : ℝ × ℝ) (u κ b : ℝ)
    (hu : 4 ≤ u) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hb : 0 < b) :
    let Λ := ManyBody.rectangularDomain L L
    letI : LinearOrder ↥Λ :=
      (Fintype.equivFin ↥Λ).linearOrder
    let m := AreaLaw.Geometry.nestedPatchCount u
    let regions : Fin m → Finset ↥Λ :=
      fun j ↦ AreaLaw.Geometry.nestedPatch Λ center u j
    let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
    let Ωᵤ := AreaLaw.rectangleAreaLawState Ω
    ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
      x ∈ regularizedPatchDomain (Out := fun _ : ↥Λ ↦ Fin q) regions →
      IsMinOn
        (regularizedPatchObjective (Out := fun _ : ↥Λ ↦ Fin q)
          regions a b Ωᵤ)
        (regularizedPatchDomain (Out := fun _ : ↥Λ ↦ Fin q) regions) x →
      let φ : EuclideanSpace ℂ (↥Λ → Fin q) :=
        (normalizedRegularizedPatchOutput (Out := fun _ : ↥Λ ↦ Fin q)
          regions a b Ωᵤ x)
      (inner ℂ φ (Matrix.toEuclideanLin
          (ManyBody.RectangleInteraction.toPlaneInteraction h.hermitianPart).hamiltonian
            φ)).re - E₀ ≤
        36 * (q : ℝ) ^ 2 * J * κ ^ 2 := by
  intro Λ m regions a Ωᵤ x hx hmin φ
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (AreaLaw.Geometry.nestedPatchCount_pos u)
  have ha : ∀ j, 0 < a j := fun _ ↦ div_pos hκ hm
  have hΩᵤ : ‖Ωᵤ‖ = 1 :=
    ((AreaLaw.norm_rectangleAreaLawState Ω).trans hΩ)
  let : LinearOrder ↥Λ := (Fintype.equivFin ↥Λ).linearOrder
  have hnorm := norm_normalizedRegularizedPatchOutput
    (Out := fun _ : ↥Λ ↦ Fin q) regions a (fun j ↦ (ha j).le) hb Ωᵤ hΩᵤ hx
  have hφ : ‖φ‖ = 1 := hnorm
  have hregions : Monotone regions := fun i j hij ↦
    AreaLaw.Geometry.nestedPatch_mono Λ center u hij
  have hcl := exists_clipped_filter_of_isMinOn_regularizedPatchObjective
    (n := fun _ : ↥Λ ↦ q) regions hregions a ha hb Ωᵤ hΩᵤ x hx hmin
  obtain ⟨T, hsupp, hherm, hTnorm, hTsum⟩ := h.exists_nearestNeighbor_terms hh hhJ
  let D : ℕ → Finset ↥Λ := AreaLaw.Geometry.nestedPatch Λ center u
  let K : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun _ ↦ Fin q) (D j))
      (ManyBody.RegionConfig (fun _ ↦ Fin q) (D j)) ℂ :=
    fun j ↦ (x j + b • 1) ^ (-(a j) / 2)
  have hunit : ∀ j, IsUnit (K j).det := fun j ↦
    (Matrix.isUnit_iff_isUnit_det _).mp (((hx j).1.add_smul_one_posDef hb).rpow _).isUnit
  have ha₁ : ∀ j, a j ≤ 1 := fun _ ↦
    (div_nat_le_self_of_nonneg hκ.le m).trans hκ₁
  have hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j := fun _ _ hij ↦ hregions hij
  have hφpatch := normalizedRegularizedPatchOutput_eq_patchState
    (n := fun _ : ↥Λ ↦ q) (fun j : Fin m ↦ D j) a b Ωᵤ x
  change φ = Entropy.patchState b (regularizedPatchFactorList (fun j : Fin m ↦ D j) a x)
    (AreaLaw.rectangleAreaLawState Ω) at hφpatch
  simp only [Entropy.patchState, Entropy.patchOutput,
    map_filter_regularizedPatchFactorList_eq_chainList] at hφpatch
  have hinv : Entropy.liftProdInv (Entropy.chainList D K fun _ ↦ True) *
      Entropy.liftProd (Entropy.chainList D K fun _ ↦ True) = 1 :=
    Entropy.liftProdInv_mul_liftProd_of_isUnit fun p hp ↦
      (List.mem_map.mp hp).elim fun i hi ↦ hi.2 ▸ hunit i
  have heig := Entropy.toEuclideanLin_conj_apply_eq
    (ManyBody.mem_groundSpace_iff.mp
      ((h.isGapped_toPlaneInteraction_hermitianPart hh hΩ hgap hspan).2.2 ▸
        Submodule.mem_span_singleton_self _)) hinv
    (((‖Matrix.toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
      (AreaLaw.rectangleAreaLawState Ω)‖⁻¹ : ℝ) : ℂ))
  rw [← hφpatch, ← hTsum] at heig
  have hφne : φ ≠ 0 := norm_ne_zero_iff.mp (hφ.trans_ne one_ne_zero)
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp (show (φ : _ → ℂ) ≠ 0 from by
    intro hzero; apply hφne; simpa using congrArg (WithLp.toLp 2) hzero)
  have hsingle : ∀ (i : ↥Λ ⊕ Edge (ManyBody.planeDomainGraph Λ)),
      ∀ j ∈ Entropy.splitIndices (AreaLaw.nearestNeighborSupport (Λ := Λ) i) D m,
      ∀ k ∈ Entropy.splitIndices (AreaLaw.nearestNeighborSupport (Λ := Λ) i) D m,
        j = k := by
    intro i j hj k hk
    have hc (l : Fin m) (hl : l ∈ Entropy.splitIndices
        (AreaLaw.nearestNeighborSupport (Λ := Λ) i) D m) :
        i ∈ ManyBody.crossingTerms (AreaLaw.nearestNeighborSupport (Λ := Λ)) (D l) :=
      by
        simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Entropy.mem_splitIndices.mp hl
    cases i with
    | inl v => exact False.elim (AreaLaw.inl_not_mem_crossingTerms (D j) v (hc j hj))
    | inr e =>
        exact Fin.ext (AreaLaw.Geometry.nestedPatch_crossing_unique
          (Λ := Λ) (c := center) (u := u) (i := (j : ℕ)) (j := (k : ℕ))
          ((AreaLaw.inr_mem_crossingTerms_iff (D j) e).mp (hc j hj))
          ((AreaLaw.inr_mem_crossingTerms_iff (D k) e).mp (hc k hk)))
  have henergy := Entropy.re_inner_sub_le_of_chain_sharp D hD K hunit hφ a ha₁ hcl
    T (AreaLaw.nearestNeighborSupport (Λ := Λ)) hsupp hherm σ₀ hTnorm hsingle heig
  have hcard (A S : Finset ↥Λ) :
      Fintype.card (ManyBody.InnerConfig (fun _ : ↥Λ ↦ q) A S) =
        Fintype.card (↥(S ∩ A) → Fin q) := by
    rw [ManyBody.card_innerConfig]
    simp only [Finset.prod_const, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  simp only [hcard, hTsum] at henergy
  rw [AreaLaw.nearestNeighbor_crossing_budget (Λ := Λ) q J
    (fun j : Fin m ↦ D j) a] at henergy
  have hboundary : (∑ j : Fin m, a j ^ 2 *
      (ManyBody.edgeBoundary (ManyBody.planeDomainGraph Λ) (D j)).card) ≤ 36 * κ ^ 2 := by
    simpa only [D, a, m, mul_comm] using
      AreaLaw.Geometry.sum_card_edgeBoundary_nestedPatch_mul_sq_le Λ center (u := u) hu κ
  calc
    _ ≤ ((q : ℝ) ^ 2 * J) * (36 * κ ^ 2) :=
      henergy.trans (mul_le_mul_of_nonneg_left hboundary (mul_nonneg (sq_nonneg _) hJ))
    _ = 36 * (q : ℝ) ^ 2 * J * κ ^ 2 := by ring

end TNLean.PEPS.Approximation

end

section

open Matrix

open ManyBody (IsGapped groundSpace SquareInteraction)
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

open Classical in
/-- At every parameter `0 < κ ≤ 1 / 2` with `36 q² J κ² ≤ Δ / 1024`, the full
marginal trace norm is at most one sixteenth for every feasible minimum. The
parameter precedes the lattice, Hamiltonian, ground vector, nested squares,
regularization parameter and minimizer. The original full-system gap is the
only spectral hypothesis. The filter exponent `patchFilterExponent q J Δ` is
such a parameter.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`. -/
theorem nestedPatch_minimizer_marginal_closeness
    (q : ℕ) {J Δ κ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hsmall : 36 * (q : ℝ) ^ 2 * J * κ ^ 2 ≤ Δ / 1024) :
    ∀ (L : ℕ) (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian) (_ : ∀ i, ‖h.term i‖ ≤ J)
        (E₀ : ℝ) (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))),
      ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (center : ℝ × ℝ) (u b : ℝ), 4 ≤ u → 0 < b →
        let Λ := ManyBody.rectangularDomain L L
        letI : LinearOrder ↥Λ :=
          (Fintype.equivFin ↥Λ).linearOrder
        let m := AreaLaw.Geometry.nestedPatchCount u
        let regions : Fin m → Finset ↥Λ :=
          fun j ↦ AreaLaw.Geometry.nestedPatch Λ center u j
        let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
        let Ωᵤ := AreaLaw.rectangleAreaLawState Ω
        ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
          x ∈ regularizedPatchDomain
            (Out := fun _ : ↥Λ ↦ Fin q) regions →
          IsMinOn
            (regularizedPatchObjective (Out := fun _ : ↥Λ ↦ Fin q)
              regions a b Ωᵤ)
            (regularizedPatchDomain (Out := fun _ : ↥Λ ↦ Fin q) regions) x →
          ∀ R : Finset ↥Λ,
            (CFC.abs
              (normalizedRegularizedPatchMarginal
                (Out := fun _ : ↥Λ ↦ Fin q) regions a b Ωᵤ x R -
                ManyBody.regionState (X := fun _ ↦ Fin q) (AreaLaw.rectangleAreaLawState Ω)
                  R)).trace.re ≤ (1 / 16 : ℝ) := by
  intro L h hh hhJ E₀ Ω hΩ hgap hspan center u b hu hb Λ m regions a Ωᵤ x hx hmin R
  let : LinearOrder ↥Λ := (Fintype.equivFin ↥Λ).linearOrder
  have henergy := (h.nestedPatch_minimizer_energy_le hh hhJ hJ hΔ Ω hΩ hgap hspan center u κ b
    hu hκ (hκhalf.trans (by norm_num)) hb x hx hmin).trans hsmall
  have hnorm := norm_normalizedRegularizedPatchOutput
    (Out := fun _ : ↥Λ ↦ Fin q) regions a
    (fun _ ↦ div_nonneg hκ.le (Nat.cast_nonneg m)) hb Ωᵤ
    ((AreaLaw.norm_rectangleAreaLawState Ω).trans hΩ) hx
  obtain ⟨hΩ', hgap', hspan'⟩ := h.isGapped_toPlaneInteraction_hermitianPart hh hΩ hgap hspan
  have hgap := ManyBody.re_trace_abs_regionState_sub_le_one_sixteenth_of_energy
    (fun _ : ↥Λ ↦ Fin q)
        (ManyBody.Interaction.isHermitian_hamiltonian
          h.isHermitian_toPlaneInteraction_hermitianPart_term) hΩ'
        hgap' hspan' hΔ
    (hnorm) henergy R
  have hρ := reindex_reducedPure_eq_regionState
    (fun _ : ↥Λ ↦ Equiv.refl (Fin q)) R Ωᵤ
  simp only [dependentRegionFinEquiv, Equiv.piCongrRight_refl,
    Matrix.reindex_refl_refl] at hρ
  have hU : dependentGlobalFinIsometry
      (fun _ : ↥Λ ↦ Equiv.refl (Fin q)) Ωᵤ = Ωᵤ := rfl
  have hΩeq : Ωᵤ = AreaLaw.rectangleAreaLawState Ω := rfl
  rw [hU, hΩeq] at hρ
  simpa only [normalizedRegularizedPatchMarginal, hρ] using hgap

open Classical in
/-- One choice of the patch parameter gives full marginal trace norm at most
one sixteenth for every feasible minimum. The choice precedes the lattice,
Hamiltonian, ground vector, nested squares, regularization parameter and
minimizer. When `36 q² J > 0` the choice is the filter exponent
`patchFilterExponent q J Δ`; otherwise it is `1 / 2`.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 335–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`. -/
theorem exists_uniform_nestedPatch_minimizer_marginal_closeness
    (q : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧
      ∀ (L : ℕ) (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
          (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ)
          (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (center : ℝ × ℝ) (u b : ℝ), 4 ≤ u → 0 < b →
          let Λ := ManyBody.rectangularDomain L L
          letI : LinearOrder ↥Λ :=
            (Fintype.equivFin ↥Λ).linearOrder
          let m := AreaLaw.Geometry.nestedPatchCount u
          let regions : Fin m → Finset ↥Λ :=
            fun j ↦ AreaLaw.Geometry.nestedPatch Λ center u j
          let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
          let Ωᵤ := AreaLaw.rectangleAreaLawState Ω
          ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
            x ∈ regularizedPatchDomain
              (Out := fun _ : ↥Λ ↦ Fin q) regions →
            IsMinOn
              (regularizedPatchObjective (Out := fun _ : ↥Λ ↦ Fin q)
                regions a b Ωᵤ)
              (regularizedPatchDomain (Out := fun _ : ↥Λ ↦ Fin q) regions) x →
            ∀ R : Finset ↥Λ,
              (CFC.abs
                (normalizedRegularizedPatchMarginal
                  (Out := fun _ : ↥Λ ↦ Fin q) regions a b Ωᵤ x R -
                  ManyBody.regionState (X := fun _ ↦ Fin q) (AreaLaw.rectangleAreaLawState Ω)
                    R)).trace.re ≤ (1 / 16 : ℝ) := by
  rcases (show (0 : ℝ) ≤ 36 * (q : ℝ) ^ 2 * J by positivity).eq_or_lt with hC | hC
  · exact ⟨1 / 2, by norm_num, le_rfl, nestedPatch_minimizer_marginal_closeness q hJ hΔ
      (by norm_num) le_rfl (by rw [← hC, zero_mul]; positivity)⟩
  · exact ⟨patchFilterExponent q J Δ, patchFilterExponent_pos hC hΔ,
      patchFilterExponent_le_half q J Δ, nestedPatch_minimizer_marginal_closeness q hJ hΔ
      (patchFilterExponent_pos hC hΔ) (patchFilterExponent_le_half q J Δ)
      (mul_patchFilterExponent_sq_le hJ hΔ.le)⟩

end TNLean.PEPS.Approximation

end
