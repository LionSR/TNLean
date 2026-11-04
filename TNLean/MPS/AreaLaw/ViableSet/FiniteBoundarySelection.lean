/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.GluingCoordinates
import TNLean.MPS.AreaLaw.ViableSet.LeftColumns
import QICLean.Channel.BoundaryDensitySelection

/-!
# A finite family of minimizing boundary states

For every feasible point in a prescribed finite boundary set, choose a density matrix that
globally minimizes the left energy and a unit eigenvector for its largest eigenvalue. The
left columns of these vectors form the named finite family `boundaryMinimizerFamily`,
contained in the prescribed left span. The choices use only that span, the left
Hamiltonian, the bond dimension and the boundary set; no ground vector or physical
extension of the right bond is supplied.

This is an auxiliary construction for Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`References/1307.5143/algo53.tex`, equation `eq:conv`, lines 472–476, the column extraction,
lines 477–478, and Claim `c:2`, lines 520–527. Only feasible boundary points are retained.
The construction concerns a fixed actual bond dimension and asserts neither viability nor
the source's quantitative AKLV bound. It asserts no matrix product state bond budget; the
positive-budget convention of `IsLeftOpenMPS` remains in that definition.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- The feasible densities at the boundary point `X`: density matrices on the left block
and a bond of dimension `m`, supported on the span of `S`, whose boundary contraction is
within trace-norm distance `η` of `X`. LVV13, `algo53.tex`, equation `eq:conv`,
lines 472–476. -/
def feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) (m : ℕ) (η : ℝ)
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    Set (Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ) :=
  {ρ | ρ.PosSemidef ∧ ρ.trace = 1 ∧
    (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ ∧
    rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}

/-- The feasible points of a finite boundary set: those with a feasible density.
LVV13, `algo53.tex`, lines 476–478. -/
noncomputable def feasibleBoundaryPoints (S : Set (LeftBlockVector L q k)) (m : ℕ) (η : ℝ)
    (N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)) :
    Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :=
  open Classical in N.filter fun X ↦ (feasibleBoundaryDensities S m η X).Nonempty

theorem mem_feasibleBoundaryPoints {S : Set (LeftBlockVector L q k)} {m : ℕ} {η : ℝ}
    {N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)}
    {X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ} :
    X ∈ feasibleBoundaryPoints S m η N ↔
      X ∈ N ∧ (feasibleBoundaryDensities S m η X).Nonempty := by
  classical
  exact Finset.mem_filter

open Classical in
/-- A chosen feasible density of least left energy at the boundary point `X`, and `0`
at an infeasible point. LVV13, `algo53.tex`, equation `eq:conv`, lines 472–476. -/
noncomputable def boundaryMinimizer (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ :=
  if hX : (feasibleBoundaryDensities S m η X).Nonempty then
    Classical.choose (exists_boundary_density_minimizer_max_eigenvector
      (a := CutLeft L q k) (s := CutSite L q k) (b := Fin m) _ HL X η hX)
  else 0

open Classical in
/-- A chosen unit eigenvector of the largest eigenvalue of the chosen minimizer at `X`,
and `0` at an infeasible point. LVV13, `algo53.tex`, lines 477–478. -/
noncomputable def boundaryLeadingVector (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m) :=
  if hX : (feasibleBoundaryDensities S m η X).Nonempty then
    Classical.choose (Classical.choose_spec (exists_boundary_density_minimizer_max_eigenvector
      (a := CutLeft L q k) (s := CutSite L q k) (b := Fin m) _ HL X η hX))
  else 0

open Classical in
/-- The largest eigenvalue of the chosen minimizer at `X`, and `0` at an infeasible point. -/
noncomputable def boundaryLeadingValue (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) : ℝ :=
  if hX : (feasibleBoundaryDensities S m η X).Nonempty then
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (exists_boundary_density_minimizer_max_eigenvector
        (a := CutLeft L q k) (s := CutSite L q k) (b := Fin m) _ HL X η hX)))
  else 0

/-- At a feasible boundary point, the chosen minimizer is feasible and minimizes the left
energy over the feasible densities, and the chosen leading vector is a unit eigenvector of
its largest eigenvalue, which is positive, fixed by the span projection. LVV13,
`algo53.tex`, equation `eq:conv` and Lemma `l:leading`, lines 472–505. -/
theorem boundaryMinimizer_spec (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ) {X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hX : (feasibleBoundaryDensities S m η X).Nonempty) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S)
    let σ := boundaryMinimizer S HL m η X
    let u := boundaryLeadingVector S HL m η X
    let μ := boundaryLeadingValue S HL m η X
    σ.PosSemidef ∧ σ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * σ = σ ∧
      rectangularTraceNorm (partialTraceFirst σ - X) ≤ η ∧
      (∀ ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
          ((CutLeft L q k × CutSite L q k) × Fin m) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ →
        rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η →
        (σ * (HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
          (ρ * (HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) ∧
      ‖u‖ = 1 ∧ 0 < μ ∧ σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧
      (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ∧
      ∀ (ν : ℝ) (w : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)),
        w ≠ 0 → σ *ᵥ WithLp.ofLp w = (ν : ℂ) • WithLp.ofLp w → ν ≤ μ := by
  intro P σ u μ
  simp only [σ, u, μ, boundaryMinimizer, boundaryLeadingVector, boundaryLeadingValue, hX,
    ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (exists_boundary_density_minimizer_max_eigenvector
      (a := CutLeft L q k) (s := CutSite L q k) (b := Fin m) P HL X η hX)))

/-- **The family of minimizing boundary states.** The left columns, in the gluing
coordinates, of the chosen leading vectors at the feasible points of the boundary set `N`.
The choices use only `S`, `H_L`, `m`, `η` and `N`. LVV13, `algo53.tex`, equation `eq:conv`,
lines 472–478, and Claim `c:2`, lines 520–527. -/
noncomputable def boundaryMinimizerFamily (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ)
    (N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)) :
    Finset (LeftBlockVector L q k) :=
  leftColumns (feasibleBoundaryPoints S m η N)
    (fun X ↦ gluingLeftCoordinates L q k m (boundaryLeadingVector S HL m η X))

/-- The family has at most `m |N|` members. LVV13, `algo53.tex`, Claim `c:2`, line 525. -/
theorem card_boundaryMinimizerFamily_le (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ)
    (N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)) :
    (boundaryMinimizerFamily S HL m η N).card ≤ m * N.card := by
  classical
  calc
    _ ≤ (feasibleBoundaryPoints S m η N).card * m := card_leftColumns_le _ _
    _ ≤ N.card * m := Nat.mul_le_mul_right m (Finset.card_filter_le _ _)
    _ = m * N.card := Nat.mul_comm _ _

/-- The family lies in the span of `S`. LVV13, `algo53.tex`, Claim `c:2`, line 526. -/
theorem boundaryMinimizerFamily_subset_span (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ)
    (N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)) :
    (boundaryMinimizerFamily S HL m η N : Set (LeftBlockVector L q k)) ⊆
      Submodule.span ℂ S :=
  leftColumns_subset_span S _ _ fun _ hX ↦
    (gluingLeftCoordinates_spanProjection_eq_iff S _).mp
      (boundaryMinimizer_spec S HL m η (mem_feasibleBoundaryPoints.mp hX).2).2.2.2.2.2.2.2.2.1

end TNLean.MPS.AreaLaw
