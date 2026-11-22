/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareInteractionTerms
import QICLean.ManyBody.Entropy.Filter.ZeroFloorEnergy
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Zero-floor maximizing filters for the original square Hamiltonian

For supplied nested regions crossed at most once by each nearest-neighbor edge,
choose one zero-floor feasible family that globally maximizes the output norm.
Its output is nonzero, its normalization is a unit vector, and both its absolute
energy error and its full-system gap-weighted infidelity are bounded by the exact
weighted crossing count with coefficient `q² J`.

The input Hamiltonian and gapped ground vector are the original square-grid ones.
Filters and output vectors use their canonical integer-domain configuration
coordinates. The existing Hermitian-part and coordinate transport preserves the
Hamiltonian sum, interaction bound, unit vector, and full-system projector gap.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `00-introduction.tex`, `eq:model`, `eq:global-gap`, and companion
`lean/OAI/MathematicalPhysics/PEPSFilters/EnergyOptimizer.lean`,
`exists_maximizer_energy`, lines 62–109, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized using the existing QICLean and TNLean estimates; no upstream
Lean proof text is reused.

**Scope restriction (canonical filter coordinates):** The theorem adds no
hypothesis to the companion lemma `exists_maximizer_energy`. As there, the nested
single-crossing regions and the weights are supplied, and every real interaction
bound is allowed. The filters here are QICLean's zero-floor feasible families in
canonical integer-domain coordinates. Their identification with adapted copies
of the companion source's positive filters is proved in
`PinnedNestedFilterCoordinates.lean`, and `PinnedZeroFloorOptimizer.lean`
restates this theorem in those coordinates. Both
are recorded, including the empty-square case, in
`docs/paper-gaps/polypeps_square_zero_floor_optimizer_scope.tex`. The comparison
with the companion code's own filter types is recorded in
https://sirui-lu.com/QICLean/paper-gaps/oai26_zero_floor_energy_scope.pdf.
-/

open ManyBody (Edge SquareInteraction)

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open TNLean.Lattice

open ManyBody (IsGapped groundSpace edgeBoundary planeDomainGraph)

namespace TNLean.PEPS.Approximation

/-- One zero-floor norm maximizer has the sharp physical energy and full-gap
fidelity estimates, simultaneously with nonvanishing and unit normalization.
Only the total original Hamiltonian must be Hermitian. The regions and the
at-most-one-crossing condition are supplied; crossings count unordered edges once.

Source: the companion `EnergyOptimizer.lean`, `exists_maximizer_energy`,
lines 62–109, at the revision cited in the module docstring. The vectors and
regional matrices below are in the canonical integer square coordinates. -/
theorem _root_.ManyBody.SquareInteraction.exists_zero_floor_maximizer_energy_fidelity
    {L q m : ℕ} {J E₀ Δ : ℝ} (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian)
        (hhJ : ∀ i, ‖h.term i‖ ≤ J)
    [LinearOrder (Lattice.Site (ManyBody.rectangularDomain L L))]
    {Ω : StateSpace L q} (hΩn : ‖Ω‖ = 1) (hΩg : IsGapped h.hamiltonian E₀ Δ)
    (hΩs : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (D : ℕ → Finset (Lattice.Site (ManyBody.rectangularDomain L L)))
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (hsingle : ∀ e : Edge (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L)),
      ∀ i j : Fin m,
        s(e.1.1, e.1.2) ∈ edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L)) (D i) →
        s(e.1.1, e.1.2) ∈ edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L)) (D j) →
        i = j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1) :
    ∃ K : (j : Fin m) → Matrix
        (ManyBody.RegionConfig (fun _ ↦ Fin q) (D j))
        (ManyBody.RegionConfig (fun _ ↦ Fin q) (D j)) ℂ,
      (∀ j : Fin m, Entropy.IsFeasibleFilter 0 (a j) (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix
          (ManyBody.RegionConfig (fun _ ↦ Fin q) (D j))
          (ManyBody.RegionConfig (fun _ ↦ Fin q) (D j)) ℂ,
        (∀ j : Fin m, Entropy.IsFeasibleFilter 0 (a j) (K' j)) →
        ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K' fun _ ↦ True))
            (AreaLaw.rectangleAreaLawState Ω)‖ ≤
          ‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
            (AreaLaw.rectangleAreaLawState Ω)‖) ∧
      let ψ := toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
        (AreaLaw.rectangleAreaLawState Ω)
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧
        |(⟪φ, toEuclideanLin
            (ManyBody.RectangleInteraction.toPlaneInteraction h.hermitianPart).hamiltonian
              φ⟫_ℂ).re - E₀| ≤
          (q : ℝ) ^ 2 * J * ∑ j : Fin m,
            a j ^ 2 *
              (edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L)) (D j)).card ∧
        Δ * (1 - ‖⟪AreaLaw.rectangleAreaLawState Ω, φ⟫_ℂ‖ ^ 2) ≤
          (q : ℝ) ^ 2 * J * ∑ j : Fin m,
            a j ^ 2 *
              (edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L)) (D j)).card := by
  classical
  obtain ⟨T, hT, hTH, hTJ, hsum⟩ := h.exists_nearestNeighbor_terms hh hhJ
  obtain ⟨hΩ, hgs, hspan⟩ := h.isGapped_toPlaneInteraction_hermitianPart hh hΩn hΩg hΩs
  have hΩ0 : AreaLaw.rectangleAreaLawState Ω ≠ 0 := fun h0 ↦ by
    have hnorm := hΩ
    simp [h0] at hnorm
  have hsplit : ∀ i : Lattice.Site (ManyBody.rectangularDomain L L) ⊕
      Edge (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L)),
      ∀ j ∈ Entropy.splitIndices (AreaLaw.nearestNeighborSupport i) D m,
      ∀ k ∈ Entropy.splitIndices (AreaLaw.nearestNeighborSupport i) D m, j = k := by
    intro i j hj k hk
    have hc (l : Fin m)
        (hl : l ∈ Entropy.splitIndices (AreaLaw.nearestNeighborSupport i) D m) :
        i ∈ ManyBody.crossingTerms AreaLaw.nearestNeighborSupport (D l) :=
      by
        simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Entropy.mem_splitIndices.mp hl
    cases i with
    | inl v => exact False.elim (AreaLaw.inl_not_mem_crossingTerms (D j) v (hc j hj))
    | inr e =>
      exact hsingle e j k
        ((AreaLaw.inr_mem_crossingTerms_iff (D j) e).mp (hc j hj))
        ((AreaLaw.inr_mem_crossingTerms_iff (D k) e).mp (hc k hk))
  have heig : toEuclideanLin (∑ i, T i) (AreaLaw.rectangleAreaLawState Ω) =
      (E₀ : ℂ) • AreaLaw.rectangleAreaLawState Ω := by
    rw [hsum]
    exact ManyBody.mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self _)
  obtain ⟨K, hK, hmax, hpos, hunit, henergy⟩ :=
    Entropy.exists_max_feasible_chain_zero_floor_normalized_abs_energy_sharp
      D hD a ha ha1 hΩ0 T AreaLaw.nearestNeighborSupport hT hTH hTJ hsplit heig
  have hbudget :
      (∑ j : Fin m, a j ^ 2 *
        ∑ i ∈ ManyBody.crossingTerms AreaLaw.nearestNeighborSupport (D j),
          (Fintype.card (ManyBody.InnerConfig
            (fun _ : Lattice.Site (ManyBody.rectangularDomain L L) ↦ q)
            (D j) (AreaLaw.nearestNeighborSupport i)) : ℝ) ^ 2 * J) =
        (q : ℝ) ^ 2 * J * ∑ j : Fin m,
          a j ^ 2 *
            (edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L)) (D j)).card := by
    simp_rw [ManyBody.card_innerConfig]
    simpa only [Finset.prod_const, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using
      AreaLaw.nearestNeighbor_crossing_budget q J (fun j : Fin m ↦ D j) a
  rw [hsum, hbudget] at henergy
  refine ⟨K, hK, hmax, hpos, hunit, henergy, ?_⟩
  have hgap := Matrix.PosSemidef.gap_le (Ω := AreaLaw.rectangleAreaLawState Ω)
    (hgs.posSemidef_sub_smul_one
        (ManyBody.Interaction.isHermitian_hamiltonian
        h.isHermitian_toPlaneInteraction_hermitianPart_term) hΩ hspan)
    (((‖toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
      (AreaLaw.rectangleAreaLawState Ω)‖⁻¹ : ℝ) : ℂ) •
      toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
        (AreaLaw.rectangleAreaLawState Ω))
  rw [hunit, one_pow, mul_one] at hgap
  exact hgap.trans ((le_abs_self _).trans henergy)

end TNLean.PEPS.Approximation
