/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GroundState.SquareInteractionTerms
import QICLean.ManyBody.Entropy.Filter.ZeroFloorEnergy
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.PEPS.Approximation.GroundState.PinnedNestedFilterCoordinates
import TNLean.PEPS.AreaLaw.SquareAreaLawSpecialization
import TNLean.PEPS.Approximation.GroundState.RegionalStates

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

## A source-facing maximizing family for the original square Hamiltonian

For supplied nested original-grid regions crossed at most once by every forward
edge, the same canonical maximizing family gives an adapted bundled source
maximum, positive output norm, unit normalized output, and the original energy
and full-gap fidelity bounds. Each physical crossing is counted once.

The interaction bound may have either sign. The canonical physical theorem
applies directly to the original Hamiltonian, including the empty grid with a
negative vacuous bound. Its once-counted crossing budget is transported without
changing the interaction bound or the maximizing family.

Source: openai/math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`lean/OAI/MathematicalPhysics/PEPSFilters/EnergyOptimizer.lean`,
`exists_maximizer_energy`, lines 62–109. Independently formalized using the
accepted canonical physical theorem and the attributed adapted filter interface;
no upstream Lean proof text is reused. This is not a theorem about unimported
OAI types. Regions and weights are supplied; no geometry, inverse-density
optimization, or full geometric optimizer is constructed here.
-/

section

open ManyBody (Edge SquareInteraction)

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

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
    [LinearOrder ↥(ManyBody.rectangularDomain L L)]
    {Ω : StateSpace L q} (hΩn : ‖Ω‖ = 1) (hΩg : IsGapped h.hamiltonian E₀ Δ)
    (hΩs : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (D : ℕ → Finset ↥(ManyBody.rectangularDomain L L))
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
  have hsplit : ∀ i : ↥(ManyBody.rectangularDomain L L) ⊕
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
            (fun _ : ↥(ManyBody.rectangularDomain L L) ↦ q)
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

end

section

open ManyBody (Edge squareLatticeGraph SquareInteraction)

noncomputable section

open Matrix

open ManyBody (IsGapped groundSpace edgeBoundary planeDomainGraph)
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

open Pinned.NestedFilter Pinned.NestedFilter.Energy

/-- Exact once-counted cardinality, using the two existing count transports. -/
theorem Pinned.NestedFilter.Energy.card_edgeBoundary_eq_crossingCount {L : ℕ}
    (A : Finset (Vertex L)) :
    (edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
      (A.map (ManyBody.rectangleSiteEquiv L L).toEmbedding)).card =
      crossingCount A := by
  classical
  rw [card_edgeBoundary_rectangle, ← forwardSquareBoundary_card, Fintype.card_subtype]
  unfold crossingCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro e _
  unfold Crosses
  tauto

/-- The existing source/native bijection followed by graph-isomorphism transport. -/
private def rectangleForwardEdgeEquiv (L : ℕ)
    [LinearOrder ↥(ManyBody.rectangularDomain L L)] :
    Edge (squareLatticeGraph L L) ≃
      Edge (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L)) :=
  (ManyBody.Edge.equiv (ManyBody.rectangleGraphIso L L))

/-- The crossing predicate is insensitive to the endpoint swap caused by the
chosen target order. No order compatibility of rectangleSiteEquiv is assumed. -/
private theorem rectangleForwardEdge_crosses_iff {L : ℕ}
    [LinearOrder ↥(ManyBody.rectangularDomain L L)]
    (A : Finset (Vertex L)) (e : Edge (squareLatticeGraph L L)) :
    s((rectangleForwardEdgeEquiv L e).1.1,
      (rectangleForwardEdgeEquiv L e).1.2) ∈
        edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
          (A.map (ManyBody.rectangleSiteEquiv L L).toEmbedding) ↔
      Crosses A e := by
  classical
  let σ := ManyBody.rectangleSiteEquiv L L
  have hmem : ∀ v : Vertex L, σ v ∈ A.map σ.toEmbedding ↔ v ∈ A :=
    fun v => by simp [σ]
  have hend := ManyBody.Edge.map_endpoints (ManyBody.rectangleGraphIso L L)
    e
  change ((rectangleForwardEdgeEquiv L e).1.1 = σ e.val.1 ∧
      (rectangleForwardEdgeEquiv L e).1.2 = σ e.val.2) ∨
    ((rectangleForwardEdgeEquiv L e).1.1 = σ e.val.2 ∧
      (rectangleForwardEdgeEquiv L e).1.2 = σ e.val.1) at hend
  rw [ManyBody.mk_mem_edgeBoundary_iff]
  have hadj := (rectangleForwardEdgeEquiv L e).property.2
  simp only [hadj, true_and]
  change (((rectangleForwardEdgeEquiv L e).1.1 ∈ A.map σ.toEmbedding ∧
      (rectangleForwardEdgeEquiv L e).1.2 ∉ A.map σ.toEmbedding) ∨
    ((rectangleForwardEdgeEquiv L e).1.2 ∈ A.map σ.toEmbedding ∧
      (rectangleForwardEdgeEquiv L e).1.1 ∉ A.map σ.toEmbedding)) ↔ _
  rcases hend with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp only [h₁, h₂, hmem, Crosses]
  · simp only [h₁, h₂, hmem, Crosses, or_comm]

/-- Every canonical edge inherits the original one-crossing condition. -/
private theorem rectangle_singleCrossing {L m : ℕ}
    [LinearOrder ↥(ManyBody.rectangularDomain L L)]
    (X : Fin m → Finset (Vertex L))
    (hsingle : ∀ e : Edge (squareLatticeGraph L L), ∀ i j : Fin m,
      Crosses (X i) e → Crosses (X j) e → i = j) :
    ∀ e : Edge (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L)),
      ∀ i j : Fin m,
        s(e.1.1, e.1.2) ∈ edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
          ((X i).map (ManyBody.rectangleSiteEquiv L L).toEmbedding) →
        s(e.1.1, e.1.2) ∈ edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
          ((X j).map (ManyBody.rectangleSiteEquiv L L).toEmbedding) →
        i = j := by
  intro e i j hi hj
  obtain ⟨f, rfl⟩ := (rectangleForwardEdgeEquiv L).surjective e
  exact hsingle f i j
    ((rectangleForwardEdge_crosses_iff (X i) f).mp hi)
    ((rectangleForwardEdge_crosses_iff (X j) f).mp hj)

/-- Converts the canonical theorem's a² * boundary-card convention to the
source's crossingCount * a² convention at the original interaction bound. -/
private theorem canonicalCrossingBudget_eq_original {L q m : ℕ}
    (J : ℝ) (X : Fin m → Finset (Vertex L))
    (a : Fin m → ℝ) :
    (q : ℝ) ^ 2 * J * ∑ j : Fin m, a j ^ 2 *
      (edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
        ((X j).map (ManyBody.rectangleSiteEquiv L L).toEmbedding)).card =
    (q : ℝ) ^ 2 * J * ∑ j : Fin m,
      (crossingCount (X j) : ℝ) * a j ^ 2 := by
  simp_rw [card_edgeBoundary_eq_crossingCount]
  have hs : (∑ j : Fin m, a j ^ 2 * (crossingCount (X j) : ℝ)) =
      ∑ j : Fin m, (crossingCount (X j) : ℝ) * a j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hs]

private theorem squareAreaLawState_inner {L q : ℕ} (φ ψ : StateSpace L q) :
    ⟪AreaLaw.rectangleAreaLawState φ, AreaLaw.rectangleAreaLawState ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (AreaLaw.rectangleConfigurationEquiv L L q)).inner_map_map φ ψ

private theorem squareAreaLawState_operator {L q : ℕ}
    (H : Matrix (Configuration L q) (Configuration L q) ℂ) (ψ : StateSpace L q) :
    AreaLaw.rectangleAreaLawState (toEuclideanLin H ψ) =
      toEuclideanLin (reindex (AreaLaw.rectangleConfigurationEquiv L L q)
        (AreaLaw.rectangleConfigurationEquiv L L q) H) (AreaLaw.rectangleAreaLawState ψ) := by
  ext σ
  exact (congrFun (reindex_mulVec (AreaLaw.rectangleConfigurationEquiv L L q)
    H (WithLp.ofLp ψ)) σ).symm

/-- Transport supplied canonical conclusions for the explicitly pulled-back
family. This helper makes no optimizer choice. -/
private theorem fromCanonical_physical_estimates
    {L q m : ℕ} {E₀ Δ B : ℝ} (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian)
    {Ω : StateSpace L q} {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (K : CanonicalFamily q X) (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j))
    (hmax : ∀ K' : CanonicalFamily q X,
      (∀ j, Entropy.IsFeasibleFilter 0 (a j) (K' j)) →
      ‖toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K' fun _ ↦ True))
            (AreaLaw.rectangleAreaLawState Ω)‖ ≤
      ‖toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K fun _ ↦ True)) (AreaLaw.rectangleAreaLawState Ω)‖)
    (hresult :
      let ψ := toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K fun _ ↦ True)) (AreaLaw.rectangleAreaLawState Ω)
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧
        |(⟪φ, toEuclideanLin
            (ManyBody.RectangleInteraction.toPlaneInteraction h.hermitianPart).hamiltonian
              φ⟫_ℂ).re - E₀| ≤ B ∧
        Δ * (1 - ‖⟪AreaLaw.rectangleAreaLawState Ω, φ⟫_ℂ‖ ^ 2) ≤ B) :
    IsMaximizer Ω a (fromCanonical K hK) ∧
      0 < ‖output (fromCanonical K hK) Ω‖ ∧
      ‖normalizedOutput (fromCanonical K hK) Ω‖ = 1 ∧
      |(⟪normalizedOutput (fromCanonical K hK) Ω,
          toEuclideanLin h.hamiltonian (normalizedOutput (fromCanonical K hK) Ω)⟫_ℂ).re - E₀| ≤ B ∧
      Δ * (1 - ‖⟪Ω, normalizedOutput (fromCanonical K hK) Ω⟫_ℂ‖ ^ 2) ≤ B := by
  have hout := squareAreaLawState_output (fromCanonical K hK) Ω
  have hnorm := squareAreaLawState_normalizedOutput (fromCanonical K hK) Ω
  rw [canonicalMatrices_fromCanonical] at hout hnorm
  dsimp only at hnorm hresult
  rw [← hnorm, ← hout, h.hamiltonian_toPlaneInteraction_hermitianPart hh,
    ← squareAreaLawState_operator] at hresult
  simp only [AreaLaw.norm_rectangleAreaLawState, squareAreaLawState_inner] at hresult
  refine ⟨?_, hresult⟩
  apply (isMaximizer_iff Ω a ha (fromCanonical K hK)).mpr
  simpa only [canonicalMatrices_fromCanonical] using And.intro hK hmax

/-- A single source-facing maximizing family has both the original-Hamiltonian
energy bound and the original full-system gap-weighted fidelity bound.

The filters are the attributed adapted source type. Only the total original
Hamiltonian must be Hermitian. The sign of `J`, positive local dimension, a
positive gap and a chosen order on integer-domain sites are not premises.
Source: `EnergyOptimizer.lean`, lines 62–109, at the revision cited above. -/
theorem _root_.ManyBody.SquareInteraction.exists_pinned_maximizer_energy_fidelity
    {L q m : ℕ} {J E₀ Δ : ℝ} (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian)
        (hhJ : ∀ i, ‖h.term i‖ ≤ J)
    {Ω : Pinned.State L q} (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (hsingle : ∀ e : Edge (squareLatticeGraph L L), ∀ i j : Fin m,
      Crosses (X i) e → Crosses (X j) e → i = j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1) :
    ∃ F : FilterFamily q m X,
      IsMaximizer Ω a F ∧ 0 < ‖output F Ω‖ ∧ ‖normalizedOutput F Ω‖ = 1 ∧
      |(⟪normalizedOutput F Ω, toEuclideanLin h.hamiltonian (normalizedOutput F Ω)⟫_ℂ).re - E₀| ≤
        (q : ℝ) ^ 2 * J * ∑ j : Fin m, (crossingCount (X j) : ℝ) * a j ^ 2 ∧
      Δ * (1 - ‖⟪Ω, normalizedOutput F Ω⟫_ℂ‖ ^ 2) ≤
        (q : ℝ) ^ 2 * J * ∑ j : Fin m, (crossingCount (X j) : ℝ) * a j ^ 2 := by
  classical
  let : LinearOrder ↥(ManyBody.rectangularDomain L L) :=
    LinearOrder.lift' (ManyBody.rectangleSiteEquiv L L).symm
      (ManyBody.rectangleSiteEquiv L L).symm.injective
  have hD : ∀ i j : Fin m, i ≤ j → canonicalRegions X i ⊆ canonicalRegions X j := by
    intro i j hij
    simpa only [canonicalRegions_fin, Finset.map_subset_map] using hX hij
  have hsep : ∀ e : Edge (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L)),
      ∀ i j : Fin m,
        s(e.1.1, e.1.2) ∈ edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
          (canonicalRegions X i) →
        s(e.1.1, e.1.2) ∈ edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
          (canonicalRegions X j) → i = j := by
    simpa only [canonicalRegions_fin] using rectangle_singleCrossing X hsingle
  obtain ⟨K, hK, hmax, hresult⟩ :=
    h.exists_zero_floor_maximizer_energy_fidelity hh hhJ hΩ hgap hspan (canonicalRegions X) hD
      hsep a ha ha1
  have hbudget : (q : ℝ) ^ 2 * J * ∑ j : Fin m, a j ^ 2 *
      (edgeBoundary (planeDomainGraph (ManyBody.rectangularDomain L L))
        (canonicalRegions X j)).card =
      (q : ℝ) ^ 2 * J * ∑ j : Fin m, (crossingCount (X j) : ℝ) * a j ^ 2 := by
    simpa only [canonicalRegions_fin] using canonicalCrossingBudget_eq_original (q := q) J X a
  dsimp only at hresult
  rw [hbudget] at hresult
  exact ⟨fromCanonical K hK,
    fromCanonical_physical_estimates h hh a ha K hK hmax hresult⟩

end TNLean.PEPS.Approximation
end

end
