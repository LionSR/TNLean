/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import QICLean.Analysis.OperatorMean.MatrixPowers
import TNLean.PEPS.Approximation.SquareInteractionTerms
import TNLean.PEPS.AreaLaw.Geometry.NestedPatches
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimizerFilter

/-!
# Energy of minimizing nested patch filters

For the prescribed nested squares and equal weights, the normalized output at
any feasible minimum has excitation energy at most $36q^2J\kappa^2$.
The filters act on the original ground vector. Their spectral relations follow
from minimality, and each nearest-neighbor interaction crosses at most one
selected boundary. The geometric boundary sum gives the numerical constant.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 213–336,
`eq:patch-energy-bound`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

open Classical in
/-- The actual normalized regularized output of every feasible patch minimum
has excitation energy at most $36q^2J\kappa^2$ for the original square Hamiltonian.
The interaction terms need only have a Hermitian total. Their Hermitian parts
preserve the original sum, supports and norm bound.

The regions are the source-selected nested squares, including repeated clipped
regions. The weights are exactly `κ / m`. Commutation, the first-order trace
inequality, and clipped joint eigenvalues follow from the
minimum. No density is assumed nonsingular.

Source: polynomial-PEPS Proposition 4.1, 03-patches.tex, lines 213–336,
eq:patch-single-crossing, eq:patch-one-term-energy and eq:patch-energy-bound;
00-introduction.tex, eq:model and eq:global-gap. -/
theorem SquareHamiltonian.nestedPatch_minimizer_energy_le
    {L q : ℕ} {J E₀ Δ : ℝ} (h : SquareHamiltonian L q J)
    (hJ : 0 ≤ J) (_hΔ : 0 < Δ)
    (Ω : StateSpace L q) (hgs : h.IsGappedGroundState E₀ Ω Δ)
    (center : ℝ × ℝ) (u κ b : ℝ)
    (hu : 4 ≤ u) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hb : 0 < b) :
    let Λ := AreaLaw.rectangularDomain L L
    letI : LinearOrder (AreaLaw.Site Λ) :=
      (Fintype.equivFin (AreaLaw.Site Λ)).linearOrder
    let m := AreaLaw.Geometry.nestedPatchCount u
    let regions : Fin m → Finset (AreaLaw.Site Λ) :=
      fun j ↦ AreaLaw.Geometry.nestedPatch Λ center u j
    let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
    let U := dependentGlobalConfigIsometry
      (V := AreaLaw.Site Λ) (Out := fun _ ↦ Fin q)
    let Ωᵤ := U.symm (squareAreaLawState Ω)
    ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
      x ∈ regularizedPatchDomain (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) regions →
      IsMinOn
        (regularizedPatchObjective (Out := fun _ : AreaLaw.Site Λ ↦ Fin q)
          regions a b Ωᵤ)
        (regularizedPatchDomain (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) regions) x →
      let φ : AreaLaw.StateSpace Λ q := U
        (normalizedRegularizedPatchOutput (Out := fun _ : AreaLaw.Site Λ ↦ Fin q)
          regions a b Ωᵤ x)
      (inner ℂ φ (Matrix.toEuclideanLin (h.toAreaLawHamiltonian hJ).operator φ)).re - E₀ ≤
        36 * (q : ℝ) ^ 2 * J * κ ^ 2 := by
  intro Λ m regions a U Ωᵤ x hx hmin φ
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (AreaLaw.Geometry.nestedPatchCount_pos u)
  have ha : ∀ j, 0 < a j := fun _ ↦ div_pos hκ hm
  have hΩᵤ : ‖Ωᵤ‖ = 1 :=
    (U.symm.norm_map _).trans ((norm_squareAreaLawState Ω).trans hgs.1)
  let : LinearOrder (AreaLaw.Site Λ) := (Fintype.equivFin (AreaLaw.Site Λ)).linearOrder
  have hnorm := norm_normalizedRegularizedPatchOutput
    (Out := fun _ : AreaLaw.Site Λ ↦ Fin q) regions a (fun j ↦ (ha j).le) hb Ωᵤ hΩᵤ hx
  have hφ : ‖φ‖ = 1 := (U.norm_map _).trans hnorm
  have hregions : Monotone regions := fun i j hij ↦
    AreaLaw.Geometry.nestedPatch_mono Λ center u hij
  have hcl := exists_clipped_filter_of_isMinOn_regularizedPatchObjective
    (n := fun _ : AreaLaw.Site Λ ↦ q) regions hregions a ha hb Ωᵤ hΩᵤ x hx hmin
  obtain ⟨T, hsupp, hherm, hTnorm, hTsum⟩ := h.exists_nearestNeighbor_terms hJ
  let D : ℕ → Finset (AreaLaw.Site Λ) := AreaLaw.Geometry.nestedPatch Λ center u
  let K : (j : Fin m) → Matrix (Entropy.RegionConfig (fun _ : AreaLaw.Site Λ ↦ q) (D j))
      (Entropy.RegionConfig (fun _ : AreaLaw.Site Λ ↦ q) (D j)) ℂ :=
    fun j ↦ (x j + b • 1) ^ (-(a j) / 2)
  have hunit : ∀ j, IsUnit (K j).det := fun j ↦
    (Matrix.isUnit_iff_isUnit_det _).mp (((hx j).1.add_smul_one_posDef hb).rpow _).isUnit
  have ha₁ : ∀ j, a j ≤ 1 := fun _ ↦
    (div_nat_le_self_of_nonnneg hκ.le m).trans hκ₁
  have hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j := fun _ _ hij ↦ hregions hij
  have hφpatch := dependentGlobalConfigIsometry_normalizedRegularizedPatchOutput
    (n := fun _ : AreaLaw.Site Λ ↦ q) (fun j : Fin m ↦ D j) a b Ωᵤ x
  change φ = Entropy.patchState b (regularizedPatchFactorList (fun j : Fin m ↦ D j) a x)
    (U (U.symm (squareAreaLawState Ω))) at hφpatch
  simp only [U.apply_symm_apply, Entropy.patchState, Entropy.patchOutput,
    map_filter_regularizedPatchFactorList_eq_chainList] at hφpatch
  have hinv : Entropy.liftProdInv (Entropy.chainList D K fun _ ↦ True) *
      Entropy.liftProd (Entropy.chainList D K fun _ ↦ True) = 1 :=
    Entropy.liftProdInv_mul_liftProd_of_isUnit fun p hp ↦
      (List.mem_map.mp hp).elim fun i hi ↦ hi.2 ▸ hunit i
  have heig := Entropy.toEuclideanLin_conj_apply_eq
    (h.isGappedGroundState_toAreaLawHamiltonian hJ hgs).2.1 hinv
    (((‖Matrix.toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
      (squareAreaLawState Ω)‖⁻¹ : ℝ) : ℂ))
  rw [← hφpatch, ← hTsum] at heig
  have hφne : φ ≠ 0 := norm_ne_zero_iff.mp (hφ.trans_ne one_ne_zero)
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp (show (φ : _ → ℂ) ≠ 0 from by
    intro hzero; apply hφne; simpa using congrArg (WithLp.toLp 2) hzero)
  have hsingle : ∀ (i : AreaLaw.Site Λ ⊕ Edge (AreaLaw.domainGraph Λ)),
      ∀ j ∈ Entropy.splitIndices (AreaLaw.nearestNeighborSupport (Λ := Λ) i) D m,
      ∀ k ∈ Entropy.splitIndices (AreaLaw.nearestNeighborSupport (Λ := Λ) i) D m,
        j = k := by
    intro i j hj k hk
    have hc (l : Fin m) (hl : l ∈ Entropy.splitIndices
        (AreaLaw.nearestNeighborSupport (Λ := Λ) i) D m) :
        i ∈ Entropy.crossingTerms (AreaLaw.nearestNeighborSupport (Λ := Λ)) (D l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, Entropy.mem_splitIndices.mp hl⟩
    cases i with
    | inl v => exact False.elim (AreaLaw.inl_not_mem_crossingTerms (D j) v (hc j hj))
    | inr e =>
        exact Fin.ext (AreaLaw.Geometry.nestedPatch_crossing_unique
          (Λ := Λ) (c := center) (u := u) (i := (j : ℕ)) (j := (k : ℕ))
          ((AreaLaw.inr_mem_crossingTerms_iff (D j) e).mp (hc j hj))
          ((AreaLaw.inr_mem_crossingTerms_iff (D k) e).mp (hc k hk)))
  have henergy := Entropy.re_inner_sub_le_of_chain_sharp D hD K hunit hφ a ha₁ hcl
    T (AreaLaw.nearestNeighborSupport (Λ := Λ)) hsupp hherm σ₀ hTnorm hsingle heig
  have hcard (A S : Finset (AreaLaw.Site Λ)) :
      Fintype.card (Entropy.InnerConfig (fun _ : AreaLaw.Site Λ ↦ q) A S) =
        Fintype.card (↥(S ∩ A) → Fin q) := by
    rw [Entropy.card_innerConfig]
    simp only [Finset.prod_const, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  simp only [hcard, hTsum] at henergy
  rw [AreaLaw.nearestNeighbor_crossing_budget (Λ := Λ) q J
    (fun j : Fin m ↦ D j) a] at henergy
  have hboundary : (∑ j : Fin m, a j ^ 2 *
      (AreaLaw.edgeBoundary Λ (D j)).card) ≤ 36 * κ ^ 2 := by
    simpa only [D, a, m, mul_comm] using
      AreaLaw.Geometry.sum_card_edgeBoundary_nestedPatch_mul_sq_le Λ center (u := u) hu κ
  calc
    _ ≤ ((q : ℝ) ^ 2 * J) * (36 * κ ^ 2) :=
      henergy.trans (mul_le_mul_of_nonneg_left hboundary (mul_nonneg (sq_nonneg _) hJ))
    _ = 36 * (q : ℝ) ^ 2 * J * κ ^ 2 := by ring

end TNLean.PEPS.Approximation
