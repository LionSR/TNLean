/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
/-
Provenance ledger: docs/provenance/openai-math.d/8740-regionalstates.json.
Adapted from OpenAI's openai/math repository (Apache-2.0).
September 24, 2026 manuscript; PEPS definition preceding thm:main.
Changes: rename the regional definitions and use the identical QICLean entropy function.
Provenance-ID: 8740-state-pinned-regionconfiguration
Downstream: TNLean.PEPS.Approximation.Pinned.RegionConfiguration
Upstream: OAI.PolynomialPEPS.PinnedEntropy.RegionConfiguration
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L32-L33
Provenance-ID: 8740-state-pinned-joinconfigurations
Downstream: TNLean.PEPS.Approximation.Pinned.joinConfigurations
Upstream: OAI.PolynomialPEPS.PinnedEntropy.joinConfigurations
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L109-L113
Provenance-ID: 8740-state-pinned-coefficientmatrix
Downstream: TNLean.PEPS.Approximation.Pinned.coefficientMatrix
Upstream: OAI.PolynomialPEPS.PinnedEntropy.coefficientMatrix
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L115-L117
Provenance-ID: 8740-state-pinned-reduceddensity
Downstream: TNLean.PEPS.Approximation.Pinned.reducedDensity
Upstream: OAI.PolynomialPEPS.PinnedEntropy.reducedDensity
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L119-L121
Provenance-ID: 8740-state-pinned-vonneumannentropy
Downstream: TNLean.PEPS.Approximation.Pinned.vonNeumannEntropy
Upstream: OAI.PolynomialPEPS.PinnedEntropy.vonNeumannEntropy
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L127-L128
Provenance-ID: 8740-state-pinned-boundarycard
Downstream: TNLean.PEPS.Approximation.Pinned.boundaryCard
Upstream: OAI.PolynomialPEPS.PinnedEntropy.boundaryCard
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L130-L133
-/
/-
Provenance ledger: docs/provenance/openai-math.d/8740-regionalstates.json.
Original proofs; no upstream Lean proof text reused.
September 24, 2026 manuscript; PEPS definition preceding thm:main.
Original exact comparison for native square-grid PEPS.
Provenance-ID: 8740-state-joinconfigurations-eq-assembleregion
Downstream: TNLean.PEPS.Approximation.joinConfigurations_eq_assembleRegion
Provenance-ID: 8740-state-regionreduceddensity-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.regionReducedDensity_pinnedTensorToGraphTensor
Provenance-ID: 8740-state-regionreduceddensity-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.regionReducedDensity_vectorTensorToGraphTensor
Provenance-ID: 8740-state-entropy-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.entropy_pinnedTensorToGraphTensor
Provenance-ID: 8740-state-forwardsquareboundaryequiv
Downstream: TNLean.PEPS.Approximation.forwardSquareBoundaryEquiv
Provenance-ID: 8740-state-boundarycard-eq-graph
Downstream: TNLean.PEPS.Approximation.boundaryCard_eq_graph
-/
import QICLean.Analysis.Entropy
import TNLean.PEPS.Approximation.SquareGridContraction
import TNLean.PEPS.ParentHamiltonian.RegionReducedDensity

/-!
# Regional states of square-grid PEPS

The forward-edge and graph-tensor contractions have equal reduced density
matrices on every region and the same number of crossing edges. The matrices
are unnormalized, as in the source definition. The entropy equality uses the
existing spectral entropy function; interpreting it as the entropy of a density
state requires a unit global vector. No normalization of a zero vector is used.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, definition of PEPS preceding Theorem 1.1.
* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 and its edge-boundary convention.
-/

open scoped BigOperators ComplexOrder

namespace TNLean.PEPS.Approximation

noncomputable section

namespace Pinned

/-- Physical configurations restricted to a region. -/
abbrev RegionConfiguration {L : ℕ} (q : ℕ) (R : Finset (Vertex L)) :=
  {v : Vertex L // v ∈ R} → Fin q

/-- Join configurations on a region and its complement. -/
def joinConfigurations {L q : ℕ} (R : Finset (Vertex L))
    (x : RegionConfiguration q R) (z : RegionConfiguration q Rᶜ) : Vertex L → Fin q := by
  classical
  exact fun v => if h : v ∈ R then x ⟨v, h⟩ else z ⟨v, Finset.mem_compl.mpr h⟩

/-- The coefficient matrix across a physical cut. -/
def coefficientMatrix {L q : ℕ} (Ω : State L q) (R : Finset (Vertex L)) :
    Matrix (RegionConfiguration q R) (RegionConfiguration q Rᶜ) ℂ :=
  fun x z => Ω (joinConfigurations R x z)

/-- The source reduced matrix is unnormalized when the source vector is unnormalized. -/
def reducedDensity {L q : ℕ} (Ω : State L q) (R : Finset (Vertex L)) :
    Matrix (RegionConfiguration q R) (RegionConfiguration q R) ℂ :=
  coefficientMatrix Ω R * (coefficientMatrix Ω R).conjTranspose

/-- The source spectral entropy, with natural logarithms and zero logarithmic terms. -/
def vonNeumannEntropy {L q : ℕ} (Ω : State L q) (R : Finset (Vertex L)) : ℝ :=
  _root_.vonNeumannEntropy (reducedDensity Ω R)
    (Matrix.isHermitian_mul_conjTranspose_self _)

/-- The number of forward edges crossing a region. -/
def boundaryCard {L : ℕ} (R : Finset (Vertex L)) : ℕ :=
  Fintype.card {e : ForwardEdge L //
    (e.val.1 ∈ R ∧ e.val.2 ∉ R) ∨ (e.val.1 ∉ R ∧ e.val.2 ∈ R)}

end Pinned

variable {L q : ℕ}

/-- Regional physical labels are unchanged; the complement is the same finite set. -/
theorem joinConfigurations_eq_assembleRegion (R : Finset (Vertex L))
    (x : Pinned.RegionConfiguration q R) (z : Pinned.RegionConfiguration q Rᶜ) :
    Pinned.joinConfigurations R x z = assembleRegionσ R x z := by
  classical
  funext v
  by_cases hv : v ∈ R <;> simp [Pinned.joinConfigurations, assembleRegionσ, hv]

/-- The regional density agrees exactly after converting arbitrary local tensors. -/
theorem regionReducedDensity_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) (R : Finset (Vertex L)) :
    regionReducedDensity (pinnedTensorToGraphTensor D A) R =
      Pinned.reducedDensity (Pinned.contractPEPS D A) R := by
  rw [regionReducedDensity_eq_mul_conjTranspose]
  apply congrArg (fun M : Matrix (RegionPhysicalConfig (d := q) R)
    (RegionPhysicalConfig (d := q) (Finset.univ \ R)) ℂ => M * M.conjTranspose)
  funext x z
  exact stateCoeff_pinnedTensorToGraphTensor D A (assembleRegionσ R x z)

/-- The virtual-first contraction has the same regional reduced matrix. -/
theorem regionReducedDensity_vectorTensorToGraphTensor (P : Vector.Tensor q L)
    (R : Finset (Vertex L)) :
    regionReducedDensity (vectorTensorToGraphTensor P) R =
      Pinned.reducedDensity P.contract R :=
  by
    rw [regionReducedDensity_eq_mul_conjTranspose]
    apply congrArg (fun M : Matrix (RegionPhysicalConfig (d := q) R)
      (RegionPhysicalConfig (d := q) (Finset.univ \ R)) ℂ => M * M.conjTranspose)
    funext x z
    exact stateCoeff_vectorTensorToGraphTensor P (assembleRegionσ R x z)

/-- The spectral entropy comparison uses the existing quantum-information definition. -/
theorem entropy_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) (R : Finset (Vertex L)) :
    _root_.vonNeumannEntropy (regionReducedDensity (pinnedTensorToGraphTensor D A) R)
        (regionReducedDensity_posSemidef _ R).isHermitian =
      Pinned.vonNeumannEntropy (Pinned.contractPEPS D A) R :=
  vonNeumannEntropy_congr (regionReducedDensity_pinnedTensorToGraphTensor D A R) _ _

/-- Crossing edges correspond individually, with both endpoint memberships unchanged. -/
def forwardSquareBoundaryEquiv (R : Finset (Vertex L)) :
    {e : ForwardEdge L //
      (e.val.1 ∈ R ∧ e.val.2 ∉ R) ∨ (e.val.1 ∉ R ∧ e.val.2 ∈ R)} ≃
      {e : PEPS.Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge R e} :=
  (forwardSquareEdgeEquiv L).subtypeEquiv (fun _ => Iff.rfl)

/-- Every physical cut has exactly the same number of crossing bonds. -/
theorem boundaryCard_eq_graph (R : Finset (Vertex L)) :
    Pinned.boundaryCard R =
      Fintype.card {e : PEPS.Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge R e} :=
  Fintype.card_congr (forwardSquareBoundaryEquiv R)

end

end TNLean.PEPS.Approximation
