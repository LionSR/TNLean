/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PinnedNestedFilterCoordinates
import TNLean.PEPS.Approximation.SquareZeroFloorOptimizer
import TNLean.PEPS.Approximation.SquareAreaLawSpecialization
import TNLean.PEPS.Approximation.RegionalStates

/-!
# A source-facing maximizing family for the original square Hamiltonian

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

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

open Pinned.NestedFilter Pinned.NestedFilter.Energy

/-- Exact once-counted cardinality, using the two existing count transports. -/
theorem Pinned.NestedFilter.Energy.card_edgeBoundary_eq_crossingCount {L : ℕ}
    (A : Finset (Vertex L)) :
    (AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
      (A.map (AreaLaw.rectangleSiteEquiv L L).toEmbedding)).card =
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
    [LinearOrder (AreaLaw.Site (AreaLaw.rectangularDomain L L))] :
    ForwardEdge L ≃ Edge (AreaLaw.domainGraph (AreaLaw.rectangularDomain L L)) :=
  (forwardSquareEdgeEquiv L).trans (Edge.equiv (AreaLaw.rectangleGraphIso L L))

/-- The crossing predicate is insensitive to the endpoint swap caused by the
chosen target order. No order compatibility of rectangleSiteEquiv is assumed. -/
private theorem rectangleForwardEdge_crosses_iff {L : ℕ}
    [LinearOrder (AreaLaw.Site (AreaLaw.rectangularDomain L L))]
    (A : Finset (Vertex L)) (e : ForwardEdge L) :
    s((rectangleForwardEdgeEquiv L e).1.1,
      (rectangleForwardEdgeEquiv L e).1.2) ∈
        AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
          (A.map (AreaLaw.rectangleSiteEquiv L L).toEmbedding) ↔
      Crosses A e := by
  classical
  let σ := AreaLaw.rectangleSiteEquiv L L
  have hmem : ∀ v : Vertex L, σ v ∈ A.map σ.toEmbedding ↔ v ∈ A :=
    fun v => by simp [σ]
  have hend := Edge.map_endpoints (AreaLaw.rectangleGraphIso L L)
    (forwardSquareEdgeEquiv L e)
  change ((rectangleForwardEdgeEquiv L e).1.1 = σ e.val.1 ∧
      (rectangleForwardEdgeEquiv L e).1.2 = σ e.val.2) ∨
    ((rectangleForwardEdgeEquiv L e).1.1 = σ e.val.2 ∧
      (rectangleForwardEdgeEquiv L e).1.2 = σ e.val.1) at hend
  rw [AreaLaw.mem_edgeBoundary_pair_iff]
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
    [LinearOrder (AreaLaw.Site (AreaLaw.rectangularDomain L L))]
    (X : Fin m → Finset (Vertex L))
    (hsingle : ∀ e : ForwardEdge L, ∀ i j : Fin m,
      Crosses (X i) e → Crosses (X j) e → i = j) :
    ∀ e : Edge (AreaLaw.domainGraph (AreaLaw.rectangularDomain L L)),
      ∀ i j : Fin m,
        s(e.1.1, e.1.2) ∈ AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
          ((X i).map (AreaLaw.rectangleSiteEquiv L L).toEmbedding) →
        s(e.1.1, e.1.2) ∈ AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
          ((X j).map (AreaLaw.rectangleSiteEquiv L L).toEmbedding) →
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
      (AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
        ((X j).map (AreaLaw.rectangleSiteEquiv L L).toEmbedding)).card =
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
    ⟪squareAreaLawState φ, squareAreaLawState ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (AreaLaw.rectangleConfigurationEquiv L L q)).inner_map_map φ ψ

private theorem squareAreaLawState_operator {L q : ℕ}
    (H : Matrix (Configuration L q) (Configuration L q) ℂ) (ψ : StateSpace L q) :
    squareAreaLawState (toEuclideanLin H ψ) =
      toEuclideanLin (reindex (AreaLaw.rectangleConfigurationEquiv L L q)
        (AreaLaw.rectangleConfigurationEquiv L L q) H) (squareAreaLawState ψ) := by
  ext σ
  exact (congrFun (reindex_mulVec (AreaLaw.rectangleConfigurationEquiv L L q)
    H (WithLp.ofLp ψ)) σ).symm

/-- Transport supplied canonical conclusions for the explicitly pulled-back
family. This helper makes no optimizer choice. -/
private theorem fromCanonical_physical_estimates
    {L q m : ℕ} {J E₀ Δ B : ℝ} (h : SquareHamiltonian L q J)
    {Ω : StateSpace L q} {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (K : CanonicalFamily q X) (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j))
    (hmax : ∀ K' : CanonicalFamily q X,
      (∀ j, Entropy.IsFeasibleFilter 0 (a j) (K' j)) →
      ‖toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K' fun _ ↦ True)) (squareAreaLawState Ω)‖ ≤
      ‖toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K fun _ ↦ True)) (squareAreaLawState Ω)‖)
    (hresult :
      let ψ := toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K fun _ ↦ True)) (squareAreaLawState Ω)
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧
        |(⟪φ, toEuclideanLin h.toAreaLawHamiltonian.operator φ⟫_ℂ).re - E₀| ≤ B ∧
        Δ * (1 - ‖⟪squareAreaLawState Ω, φ⟫_ℂ‖ ^ 2) ≤ B) :
    IsMaximizer Ω a (fromCanonical K hK) ∧
      0 < ‖output (fromCanonical K hK) Ω‖ ∧
      ‖normalizedOutput (fromCanonical K hK) Ω‖ = 1 ∧
      |(⟪normalizedOutput (fromCanonical K hK) Ω,
          toEuclideanLin h.operator (normalizedOutput (fromCanonical K hK) Ω)⟫_ℂ).re - E₀| ≤ B ∧
      Δ * (1 - ‖⟪Ω, normalizedOutput (fromCanonical K hK) Ω⟫_ℂ‖ ^ 2) ≤ B := by
  have hout := squareAreaLawState_output (fromCanonical K hK) Ω
  have hnorm := squareAreaLawState_normalizedOutput (fromCanonical K hK) Ω
  rw [canonicalMatrices_fromCanonical] at hout hnorm
  dsimp only at hnorm hresult
  rw [← hnorm, ← hout, h.toAreaLawHamiltonian_operator,
    ← squareAreaLawState_operator] at hresult
  simp only [norm_squareAreaLawState, squareAreaLawState_inner] at hresult
  refine ⟨?_, hresult⟩
  apply (isMaximizer_iff Ω a ha (fromCanonical K hK)).mpr
  simpa only [canonicalMatrices_fromCanonical] using And.intro hK hmax

/-- A single source-facing maximizing family has both the original-Hamiltonian
energy bound and the original full-system gap-weighted fidelity bound.

The filters are the attributed adapted source type. Only the total original
Hamiltonian must be Hermitian. The sign of `J`, positive local dimension, a
positive gap and a chosen order on integer-domain sites are not premises.
Source: `EnergyOptimizer.lean`, lines 62–109, at the revision cited above. -/
theorem SquareHamiltonian.exists_pinned_maximizer_energy_fidelity
    {L q m : ℕ} {J E₀ Δ : ℝ} (h : SquareHamiltonian L q J)
    {Ω : Pinned.State L q} (hΩ : h.IsGappedGroundState E₀ Ω Δ)
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (hsingle : ∀ e : ForwardEdge L, ∀ i j : Fin m,
      Crosses (X i) e → Crosses (X j) e → i = j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1) :
    ∃ F : FilterFamily q m X,
      IsMaximizer Ω a F ∧ 0 < ‖output F Ω‖ ∧ ‖normalizedOutput F Ω‖ = 1 ∧
      |(⟪normalizedOutput F Ω, toEuclideanLin h.operator (normalizedOutput F Ω)⟫_ℂ).re - E₀| ≤
        (q : ℝ) ^ 2 * J * ∑ j : Fin m, (crossingCount (X j) : ℝ) * a j ^ 2 ∧
      Δ * (1 - ‖⟪Ω, normalizedOutput F Ω⟫_ℂ‖ ^ 2) ≤
        (q : ℝ) ^ 2 * J * ∑ j : Fin m, (crossingCount (X j) : ℝ) * a j ^ 2 := by
  classical
  let : LinearOrder (AreaLaw.Site (AreaLaw.rectangularDomain L L)) :=
    LinearOrder.lift' (AreaLaw.rectangleSiteEquiv L L).symm
      (AreaLaw.rectangleSiteEquiv L L).symm.injective
  have hD : ∀ i j : Fin m, i ≤ j → canonicalRegions X i ⊆ canonicalRegions X j := by
    intro i j hij
    simpa only [canonicalRegions_fin, Finset.map_subset_map] using hX hij
  have hsep : ∀ e : Edge (AreaLaw.domainGraph (AreaLaw.rectangularDomain L L)),
      ∀ i j : Fin m,
        s(e.1.1, e.1.2) ∈ AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
          (canonicalRegions X i) →
        s(e.1.1, e.1.2) ∈ AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
          (canonicalRegions X j) → i = j := by
    simpa only [canonicalRegions_fin] using rectangle_singleCrossing X hsingle
  obtain ⟨K, hK, hmax, hresult⟩ :=
    h.exists_zero_floor_maximizer_energy_fidelity hΩ (canonicalRegions X) hD hsep a ha ha1
  have hbudget : (q : ℝ) ^ 2 * J * ∑ j : Fin m, a j ^ 2 *
      (AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L) (canonicalRegions X j)).card =
      (q : ℝ) ^ 2 * J * ∑ j : Fin m, (crossingCount (X j) : ℝ) * a j ^ 2 := by
    simpa only [canonicalRegions_fin] using canonicalCrossingBudget_eq_original (q := q) J X a
  dsimp only at hresult
  rw [hbudget] at hresult
  exact ⟨fromCanonical K hK,
    fromCanonical_physical_estimates h a ha K hK hmax hresult⟩

end TNLean.PEPS.Approximation
