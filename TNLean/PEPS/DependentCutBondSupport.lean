/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondCoefficients
import TNLean.PEPS.DependentBondCut
import TNLean.PEPS.DependentBondProjectorExpansion
import TNLean.PEPS.DependentPhysicalProductRangeSupport

/-!
# Coherent bond expansions forced by complementary cuts

For any family of cuts whose uncut edges cover the graph, simultaneous
membership in the actual canonical cut spaces forces representation-matrix
support on each edge. The dependent product-range theorem then produces an
actual coherent expansion in the complete bond-label family. Existence needs
no semi-regularity. When the independently chosen edge representations are
semi-regular, trace-dual extraction reconstructs that vector.

The argument allows independent edge dimensions, arbitrary joint cut boundaries,
parallel edges, and self edges, and makes no torus-specific geometric assumptions.
Source: SCP10, arXiv:1001.3807, Theorem 5.5 and Lemma 4.6.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

section CoordinateSlices
variable {Site : Type*} [Fintype Site] [DecidableEq Site] {Out : Site → Type*}

/-- Fixing all but one coordinate in a dependent product leaves a scalar
multiple of its factor at that coordinate. -/
theorem dependentProduct_coordinateSlice_eq_smul
    (f : (e : Site) → Out e → ℂ) (e : Site) (τ : (w : Site) → Out w) :
    (fun s => ∏ w, f w (Function.update τ e s w)) =
      (∏ w ∈ Finset.univ.erase e, f w (τ w)) • f e := by
  funext s
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

end CoordinateSlices

variable {Vertex Edge G : Type*} [Group G] [Fintype G]
variable [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- Representation matrices as columns in head-row/tail-column coordinates. -/
def bondMatrix (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (e : Edge) :
    Matrix (D e × D e) G ℂ := fun t g => U e g t.1 t.2

omit [Fintype Edge] [DecidableEq Edge] in
/-- Each representation matrix is a literal column of its edge's map. -/
theorem representation_mem_bondMatrix_range
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (e : Edge) (g : G) :
    (fun t : D e × D e => U e g t.1 t.2) ∈ (Matrix.mulVecLin (bondMatrix D U e)).range := by
  classical
  refine ⟨Pi.single g 1, ?_⟩
  ext t
  simp [bondMatrix, Matrix.mulVec_single, Matrix.col]

/-- Read a one-edge slice while holding every other physical endpoint fixed. -/
def physicalBondSlice (e : Edge) (τ : (w : Edge) → D w × D w) :
    (((v : Vertex) → LocalConfig tail head D v) → ℂ) →ₗ[ℂ] ((D e × D e) → ℂ) :=
  LinearMap.pi fun s => LinearMap.proj ((siteBondEquiv tail head D).symm (Function.update τ e s))

/-- The matrix on an edge after fixing all vertex group actions. -/
def gaugeBondMatrix (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (q : Vertex → G) (e : Edge) :
    Matrix (D e) (D e) ℂ := U e (q (head e)) * B e * U e ((q (tail e))⁻¹)

/-- The actual averaging-site contraction in regrouped physical coordinates. -/
theorem bondRegrouping_network_averagingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    bondRegrouping tail head D (network tail head D (averagingSite tail head D U) B) =
      fun β => (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex *
        ∑ q : Vertex → G, ∏ e, gaugeBondMatrix tail head D U B q e (β e).1 (β e).2 := by
  funext β
  rw [bondRegrouping_apply, network_averagingSite]
  simp only [siteBondEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply, endpointPairEquiv, Equiv.coe_fn_symm_mk,
    Bool.false_eq_true, ↓reduceIte, gaugeBondMatrix]

/-- The canonical network is a coherent sum of physical matrix products. -/
theorem network_averagingSite_eq_sum_matrixBondProduct
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    network tail head D (averagingSite tail head D U) B =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex •
        ∑ q : Vertex → G, matrixBondProduct tail head D (gaugeBondMatrix tail head D U B q) := by
  funext σ
  rw [network_averagingSite]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, matrixBondProduct,
    siteBondEquiv, Equiv.trans_apply, endpointPairEquiv_apply, gaugeBondMatrix]

/-- Trace-dual extraction of an actual canonical network retains arbitrary
edge insertions and the complete coherent vertex-group sum. -/
theorem bondCoefficientExtraction_network_averagingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (p : Edge → G) :
    bondCoefficientExtraction tail head D U p
      (network tail head D (averagingSite tail head D U) B) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex *
        ∑ q : Vertex → G, ∏ e, torusDeltaPairing (U e) (p e)
          (U e (q (head e)) * B e * U e ((q (tail e))⁻¹)) := by
  rw [network_averagingSite_eq_sum_matrixBondProduct, map_smul, map_sum]
  simp only [bondCoefficientExtraction, outputBondPairing_matrixBondProduct,
    gaugeBondMatrix, smul_eq_mul]

/-- An uncut identity edge has representation-matrix support in every physical
slice, despite arbitrary insertions and coherent contractions elsewhere. -/
theorem physicalBondSlice_network_averagingSite_mem_range
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (e : Edge) (he : B e = 1) (τ : (w : Edge) → D w × D w) :
    physicalBondSlice tail head D e τ
      (network tail head D (averagingSite tail head D U) B) ∈
      (Matrix.mulVecLin (bondMatrix D U e)).range := by
  have hrepr (q : Vertex → G) :
      (fun s : D e × D e => gaugeBondMatrix tail head D U B q e s.1 s.2) ∈
        (Matrix.mulVecLin (bondMatrix D U e)).range := by
    simpa only [gaugeBondMatrix, he, Matrix.mul_one, ← map_mul] using
      representation_mem_bondMatrix_range D U e (q (head e) * (q (tail e))⁻¹)
  have heq : physicalBondSlice tail head D e τ
      (network tail head D (averagingSite tail head D U) B) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex •
        ∑ q : Vertex → G, (fun s => ∏ w,
          gaugeBondMatrix tail head D U B q w
            (Function.update τ e s w).1 (Function.update τ e s w).2) := by
    funext s
    simpa only [physicalBondSlice, LinearMap.pi_apply, LinearMap.proj_apply,
      bondRegrouping_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using
      congrFun (bondRegrouping_network_averagingSite tail head D U B) (Function.update τ e s)
  rw [heq]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro q _
  rw [dependentProduct_coordinateSlice_eq_smul
    (fun w (s : D w × D w) => gaugeBondMatrix tail head D U B q w s.1 s.2) e τ]
  exact Submodule.smul_mem _ _ (hrepr q)

/-- Every actual canonical cut vector has representation-matrix support on
its uncut edges, for arbitrary correlated boundary tensors. -/
theorem physicalBondSlice_mem_range_of_mem_cutSpace
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (C : Finset Edge) (e : Edge) (he : e ∉ C) (τ : (w : Edge) → D w × D w)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ψ ∈ cutSpace tail head D (averagingSite tail head D U) C) :
    physicalBondSlice tail head D e τ ψ ∈ (Matrix.mulVecLin (bondMatrix D U e)).range := by
  classical
  let S := (Matrix.mulVecLin (bondMatrix D U e)).range.comap (physicalBondSlice tail head D e τ)
  have hle : cutSpace tail head D (averagingSite tail head D U) C ≤ S := by
    rw [cutSpace_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨η, rfl⟩
    change physicalBondSlice tail head D e τ
      (cutMap tail head D (averagingSite tail head D U) C (Pi.single η 1)) ∈
        (Matrix.mulVecLin (bondMatrix D U e)).range
    have hnet := funext (cutMap_single_eq_network tail head D (averagingSite tail head D U) C η)
    rw [hnet]
    apply physicalBondSlice_network_averagingSite_mem_range
    simp [cutBondUnits, he]
  exact hle hψ

/-- Complementary uncut edges force full product support in any graph and
with independently sized bonds. Semi-regularity is not needed. -/
theorem bondRegrouping_mem_product_range_of_mem_cutSpaces
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    {ι : Type*} (C : ι → Finset Edge) (hcover : ∀ e, ∃ i, e ∉ C i)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ∀ i, ψ ∈ cutSpace tail head D (averagingSite tail head D U) (C i)) :
    bondRegrouping tail head D ψ ∈ (dependentPhysicalProductFamilyMap (bondMatrix D U)).range := by
  apply (mem_range_dependentPhysicalProductFamilyMap_iff _ _).mpr
  intro e τ
  obtain ⟨i, hi⟩ := hcover e
  exact physicalBondSlice_mem_range_of_mem_cutSpace tail head D U (C i) e hi τ (hψ i)

/-- An actual coherent bond-label expansion follows from simultaneous canonical
cut membership. No coefficient expansion is assumed as a premise. -/
theorem exists_bondCoefficients_of_mem_cutSpaces
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    {ι : Type*} (C : ι → Finset Edge) (hcover : ∀ e, ∃ i, e ∉ C i)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ∀ i, ψ ∈ cutSpace tail head D (averagingSite tail head D U) (C i)) :
    ∃ c : (Edge → G) → ℂ, ψ = ∑ p, c p • representationBondProduct tail head D U p := by
  obtain ⟨c, hc⟩ := bondRegrouping_mem_product_range_of_mem_cutSpaces tail head D U C hcover hψ
  refine ⟨c, ?_⟩
  apply (bondRegrouping tail head D).injective
  rw [map_sum]
  simp_rw [map_smul]
  rw [← hc]
  funext β
  simp only [dependentPhysicalProductFamilyMap_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, representationBondProduct, bondRegrouping_matrixBondProduct, bondMatrix]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Semi-regular edge trace pairings reconstruct every actual simultaneous cut
vector from its extracted coefficients. Source: SCP10, Theorem 5.5. -/
theorem eq_sum_extracted_bondProducts_of_mem_cutSpaces
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    {ι : Type*} (C : ι → Finset Edge) (hcover : ∀ e, ∃ i, e ∉ C i)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ∀ i, ψ ∈ cutSpace tail head D (averagingSite tail head D U) (C i)) :
    ψ = ∑ p, bondCoefficientExtraction tail head D U p ψ •
      representationBondProduct tail head D U p := by
  obtain ⟨c, hc⟩ := exists_bondCoefficients_of_mem_cutSpaces tail head D U C hcover hψ
  have hcoeff p : bondCoefficientExtraction tail head D U p ψ = c p := by
    rw [hc, bondCoefficientExtraction_sum tail head D U hU]
  simp_rw [hcoeff]
  exact hc

end TNLean.PEPS.DependentBondNetwork
