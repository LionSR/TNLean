/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.SquareGridContraction
import TNLean.PEPS.ParentHamiltonian.RegionReducedDensity
import QICLean.Analysis.Entropy

/-
Original proofs; no upstream Lean proof text reused.
September 24, 2026 manuscript, sec:introduction; exact conversion of its PEPS definition.
Provenance-ID: 8740-squaregridstateisometry
Downstream: TNLean.PEPS.Approximation.squareGridStateIsometry
Provenance-ID: 8740-vector-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.vector_pinnedTensorToGraphTensor
Provenance-ID: 8740-vector-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.vector_vectorTensorToGraphTensor
Provenance-ID: 8740-norm-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.norm_pinnedTensorToGraphTensor
Provenance-ID: 8740-nonzero-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.nonzero_pinnedTensorToGraphTensor
Provenance-ID: 8740-normalized-error-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.normalized_error_pinnedTensorToGraphTensor
Provenance-ID: 8740-normalized-error-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.normalized_error_vectorTensorToGraphTensor
Provenance-ID: 8740-graphbonddim-forall
Downstream: TNLean.PEPS.Approximation.graphBondDim_forall
Provenance-ID: 8740-vectortensortographtensor-bonddim-pos
Downstream: TNLean.PEPS.Approximation.vectorTensorToGraphTensor_bondDim_pos
Provenance-ID: 8740-maxbonddim-le-iff
Downstream: TNLean.PEPS.Approximation.maxBondDim_le_iff
Provenance-ID: 8740-forwardsquareboundaryequiv
Downstream: TNLean.PEPS.Approximation.forwardSquareBoundaryEquiv
Provenance-ID: 8740-forwardsquareboundary-card
Downstream: TNLean.PEPS.Approximation.forwardSquareBoundary_card
Provenance-ID: 8740-squarecomplementconfigequiv
Downstream: TNLean.PEPS.Approximation.squareComplementConfigEquiv
Provenance-ID: 8740-regionreduceddensity-eq-pisubtype
Downstream: TNLean.PEPS.Approximation.regionReducedDensity_eq_piSubtype
Provenance-ID: 8740-regionreduceddensity-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.regionReducedDensity_pinnedTensorToGraphTensor
Provenance-ID: 8740-regionreduceddensity-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.regionReducedDensity_vectorTensorToGraphTensor
Provenance-ID: 8740-entropy-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.entropy_pinnedTensorToGraphTensor
Provenance-ID: 8740-entropy-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.entropy_vectorTensorToGraphTensor
-/

/-!
# Vector and regional consequences of exact square-grid conversion

Original proofs from the coefficient correspondence. The physical coordinate
space is the Euclidean space on site configurations, as in both upstream
presentations. No Hamiltonian or entropy model is introduced.
The reductions below use the existing native regional configuration equivalence
and QICLean's partial trace and von Neumann entropy.

Source: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
September 24 polynomial PEPS manuscript, introduction lines 20–34.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.Approximation

variable {L q : ℕ}

/-- Physical configurations are unchanged, so their Euclidean identification is an isometry. -/
def squareGridStateIsometry (L q : ℕ) :
    Pinned.State L q ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SquareLatticeVertex L L → Fin q) :=
  LinearIsometryEquiv.refl ℂ _

/-- Exact equality of Euclidean vectors for physical-first tensors. -/
theorem vector_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) :
    pepsVector (pinnedTensorToGraphTensor D A) =
      Pinned.contractPEPS D A := by
  apply WithLp.ext_iff.mpr
  funext x
  exact stateCoeff_pinnedTensorToGraphTensor D A x

/-- Exact equality of Euclidean vectors for virtual-first tensors. -/
theorem vector_vectorTensorToGraphTensor (P : Vector.Tensor q L) :
    pepsVector (vectorTensorToGraphTensor P) = P.contract := by
  apply WithLp.ext_iff.mpr
  funext x
  exact stateCoeff_vectorTensorToGraphTensor P x

/-- The contracted vector norm is unchanged. -/
theorem norm_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) :
    ‖pepsVector (pinnedTensorToGraphTensor D A)‖ =
      ‖Pinned.contractPEPS D A‖ := by rw [vector_pinnedTensorToGraphTensor]

/-- Nonzero contraction is preserved, without any positivity assumption on the dimensions. -/
theorem nonzero_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) :
    pepsVector (pinnedTensorToGraphTensor D A) ≠ 0 ↔
      Pinned.contractPEPS D A ≠ 0 := by rw [vector_pinnedTensorToGraphTensor]

/-- Every normalized phase-error inequality transfers without loss, for any complex phase.
The inverse-norm convention also makes the equality valid for the zero vector. -/
theorem normalized_error_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v)
    (Ω : Pinned.State L q) (z : ℂ) :
    let ψ := pepsVector (pinnedTensorToGraphTensor D A)
    ‖((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ - z • Ω‖ =
      ‖((‖Pinned.contractPEPS D A‖⁻¹ : ℝ) : ℂ) • Pinned.contractPEPS D A - z • Ω‖ := by
  dsimp only
  rw [vector_pinnedTensorToGraphTensor]

/-- The virtual-first source's complex inverse-norm convention is preserved exactly. -/
theorem normalized_error_vectorTensorToGraphTensor (P : Vector.Tensor q L)
    (Ω : Vector.State q L) (z : ℂ) :
    let ψ := pepsVector (vectorTensorToGraphTensor P)
    ‖(‖ψ‖ : ℂ)⁻¹ • ψ - z • Ω‖ =
      ‖(‖P.contract‖ : ℂ)⁻¹ • P.contract - z • Ω‖ := by
  dsimp only
  rw [vector_vectorTensorToGraphTensor]

/-- All pointwise constraints on edge dimensions transfer in both directions. -/
theorem graphBondDim_forall (D : ForwardEdge L → ℕ) (P : ℕ → Prop) :
    (∀ e, P (graphBondDim D e)) ↔ ∀ e, P (D e) := by
  constructor
  · intro h e
    exact h (forwardSquareEdgeEquiv L e)
  · intro h e
    exact h ((forwardSquareEdgeEquiv L).symm e)

/-- The virtual-first adapter preserves the required positivity on every native edge. -/
theorem vectorTensorToGraphTensor_bondDim_pos (P : Vector.Tensor q L)
    (e : Edge (squareLatticeGraph L L)) :
    0 < (vectorTensorToGraphTensor P).bondDim e :=
  P.bondDim_pos ((forwardSquareEdgeEquiv L).symm e)

/-- Maximum-bond bounds are precisely native per-edge bounds. The empty maximum is zero. -/
theorem maxBondDim_le_iff (P : Vector.Tensor q L) (B : ℕ) :
    P.maxBondDim ≤ B ↔ ∀ e, (vectorTensorToGraphTensor P).bondDim e ≤ B := by
  classical
  change Finset.univ.sup P.bondDim ≤ B ↔ ∀ e, graphBondDim P.bondDim e ≤ B
  rw [graphBondDim_forall]
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const]

/-- Crossing edges correspond bijectively, for every region including empty and full regions. -/
def forwardSquareBoundaryEquiv (R : Finset (Vertex L)) :
    {e : ForwardEdge L //
      (e.val.1 ∈ R ∧ e.val.2 ∉ R) ∨ (e.val.1 ∉ R ∧ e.val.2 ∈ R)} ≃
      {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge R e} where
  toFun e := ⟨forwardSquareEdgeEquiv L e.val, e.property⟩
  invFun e := ⟨(forwardSquareEdgeEquiv L).symm e.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Source and native crossing-boundary cardinalities are equal. -/
theorem forwardSquareBoundary_card (R : Finset (Vertex L)) :
    Fintype.card {e : ForwardEdge L //
      (e.val.1 ∈ R ∧ e.val.2 ∉ R) ∨ (e.val.1 ∉ R ∧ e.val.2 ∈ R)} =
      Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge R e} :=
  Fintype.card_congr (forwardSquareBoundaryEquiv R)

/-- Complement configurations identify the native finite-set complement with nonmembership. -/
def squareComplementConfigEquiv (R : Finset (Vertex L)) :
    RegionPhysicalConfig (d := q) (Finset.univ \ R) ≃
      ({v : Vertex L // v ∉ R} → Fin q) where
  toFun f v := f ⟨v.val, by simp [v.property]⟩
  invFun f v := f ⟨v.val, (Finset.mem_sdiff.mp v.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The native reduced density uses the same cut as the canonical predicate-based split.
Only the complement's configuration coordinates need reindexing. -/
theorem regionReducedDensity_eq_piSubtype (A : Tensor (squareLatticeGraph L L) q)
    (R : Finset (Vertex L)) :
    let split := Equiv.piEquivPiSubtypeProd (fun v : Vertex L => v ∈ R) (fun _ => Fin q)
    regionReducedDensity A R = Matrix.partialTraceRight (Matrix.vecMulVec
      (stateCoeff A ∘ split.symm) (star (stateCoeff A ∘ split.symm))) := by
  classical
  dsimp only
  ext x y
  simp only [regionReducedDensity, Matrix.partialTraceRight_apply]
  exact Fintype.sum_equiv (squareComplementConfigEquiv (q := q) R) _ _ (fun _ => rfl)

/-- Native regional reduction equals the partial trace of the actual physical-first contraction. -/
theorem regionReducedDensity_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) (R : Finset (Vertex L)) :
    regionReducedDensity (pinnedTensorToGraphTensor D A) R =
      Matrix.partialTraceRight (Matrix.vecMulVec
        (Pinned.contractPEPS D A ∘ (regionConfigEquiv (d := q) R).symm)
        (star (Pinned.contractPEPS D A ∘ (regionConfigEquiv (d := q) R).symm))) := by
  have h := funext (stateCoeff_pinnedTensorToGraphTensor D A)
  simp only [regionReducedDensity, h]

/-- The same reduction identity for the separate virtual-first contraction. -/
theorem regionReducedDensity_vectorTensorToGraphTensor (P : Vector.Tensor q L)
    (R : Finset (Vertex L)) :
    regionReducedDensity (vectorTensorToGraphTensor P) R =
      Matrix.partialTraceRight (Matrix.vecMulVec
        (P.contract ∘ (regionConfigEquiv (d := q) R).symm)
        (star (P.contract ∘ (regionConfigEquiv (d := q) R).symm))) := by
  have h := funext (stateCoeff_vectorTensorToGraphTensor P)
  simp only [regionReducedDensity, h]

/-- The canonical entropy of the physical-first regional contraction is unchanged.
This applies QICLean's entropy congruence; it introduces no separate entropy definition. -/
theorem entropy_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) (R : Finset (Vertex L)) :
    let f := Pinned.contractPEPS D A ∘ (regionConfigEquiv (d := q) R).symm
    vonNeumannEntropy (regionReducedDensity (pinnedTensorToGraphTensor D A) R)
        (regionReducedDensity_posSemidef _ _).isHermitian =
      vonNeumannEntropy (Matrix.partialTraceRight (Matrix.vecMulVec f (star f)))
        (Matrix.posSemidef_vecMulVec_self_star f).partialTraceRight.isHermitian := by
  exact vonNeumannEntropy_congr (regionReducedDensity_pinnedTensorToGraphTensor D A R) _ _

/-- Canonical regional entropy is also unchanged for the virtual-first presentation. -/
theorem entropy_vectorTensorToGraphTensor (P : Vector.Tensor q L) (R : Finset (Vertex L)) :
    let f := P.contract ∘ (regionConfigEquiv (d := q) R).symm
    vonNeumannEntropy (regionReducedDensity (vectorTensorToGraphTensor P) R)
        (regionReducedDensity_posSemidef _ _).isHermitian =
      vonNeumannEntropy (Matrix.partialTraceRight (Matrix.vecMulVec f (star f)))
        (Matrix.posSemidef_vecMulVec_self_star f).partialTraceRight.isHermitian := by
  exact vonNeumannEntropy_congr (regionReducedDensity_vectorTensorToGraphTensor P R) _ _

end TNLean.PEPS.Approximation
