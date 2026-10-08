/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.VertexVirtualParentTransport
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Star.StarProjection

/-!
# Regional operators in dependent product coordinates

A regional matrix acts as the identity on the complementary coordinates.
Splitting the full product of site matrices across the region shows that any
regional intertwining identity extends to the full product space.
These finite-dimensional identities allow different input and output spaces
at each vertex and require no range or commutation assumptions.
-/

open scoped BigOperators Matrix Kronecker

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {In Out : V → Type*}

/-- Extend a regional matrix by the identity on its complementary coordinates. -/
noncomputable def dependentRegionOperatorLift (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    Matrix ((w : {w : V // w ∈ Finset.univ}) → Out w.1)
      ((w : {w : V // w ∈ Finset.univ}) → Out w.1) ℂ := by
  classical
  exact Matrix.reindex (dependentRegionConfigEquiv R).symm
    (dependentRegionConfigEquiv R).symm (K ⊗ₖ 1)

/-- Lifting preserves the identity matrix. -/
theorem dependentRegionOperatorLift_one [∀ v, DecidableEq (Out v)] (R : Finset V) :
    dependentRegionOperatorLift (Out := Out) R 1 = 1 := by
  classical
  simp [dependentRegionOperatorLift, Matrix.reindex_apply]

/-- Lifting preserves multiplication. -/
theorem dependentRegionOperatorLift_mul [∀ v, Fintype (Out v)] (R : Finset V)
    (K L : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    dependentRegionOperatorLift R (K * L) =
      dependentRegionOperatorLift R K * dependentRegionOperatorLift R L := by
  classical
  simp only [dependentRegionOperatorLift, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Lifting preserves the adjoint. -/
theorem dependentRegionOperatorLift_conjTranspose (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    (dependentRegionOperatorLift R K).conjTranspose =
      dependentRegionOperatorLift R K.conjTranspose := by
  classical
  simp only [dependentRegionOperatorLift, Matrix.conjTranspose_reindex,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Lifting preserves orthogonal projections. -/
theorem dependentRegionOperatorLift_isStarProjection [∀ v, Fintype (Out v)]
    (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (hK : IsStarProjection K) : IsStarProjection (dependentRegionOperatorLift R K) := by
  rw [isStarProjection_iff'] at hK ⊢
  constructor
  · rw [← dependentRegionOperatorLift_mul, hK.1]
  · simpa only [Matrix.star_eq_conjTranspose, dependentRegionOperatorLift_conjTranspose]
      using congrArg (dependentRegionOperatorLift R) hK.2

/-- Coefficients of a lifted matrix in assembled regional coordinates. -/
theorem dependentRegionOperatorLift_assemble [∀ v, DecidableEq (Out v)] (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (α β : (w : {w : V // w ∈ R}) → Out w.1)
    (τ ρ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1) :
    dependentRegionOperatorLift R K
        (assembleDependentRegionConfig R α τ) (assembleDependentRegionConfig R β ρ) =
      if τ = ρ then K α β else 0 := by
  classical
  have he (a : (w : {w : V // w ∈ R}) → Out w.1)
      (t : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1) :
      dependentRegionConfigEquiv R (assembleDependentRegionConfig R a t) = (a, t) :=
    (dependentRegionConfigEquiv R).apply_symm_apply (a, t)
  simp [dependentRegionOperatorLift, Matrix.reindex_apply, he, Matrix.one_apply, mul_ite]

/-- Every complementary slice sees exactly the original regional matrix. -/
theorem dependentRegionSlice_mulVec_dependentRegionOperatorLift
    [∀ v, Fintype (Out v)] (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (x : ((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ)
    (τ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1) :
    dependentRegionSlice R τ ((dependentRegionOperatorLift R K).mulVec x) =
      K.mulVec (dependentRegionSlice R τ x) := by
  classical
  funext α
  change (∑ η, dependentRegionOperatorLift R K
      (assembleDependentRegionConfig R α τ) η * x η) = _
  calc
    _ = ∑ p : ((w : {w : V // w ∈ R}) → Out w.1) ×
          ((w : {w : V // w ∈ Finset.univ \ R}) → Out w.1),
        dependentRegionOperatorLift R K (assembleDependentRegionConfig R α τ)
          (assembleDependentRegionConfig R p.1 p.2) *
            x (assembleDependentRegionConfig R p.1 p.2) :=
      (Equiv.sum_comp (dependentRegionConfigEquiv R).symm _).symm
    _ = _ := by
      simp [Fintype.sum_prod_type, dependentRegionOperatorLift_assemble,
        Matrix.mulVec, dotProduct, dependentRegionSlice, ite_mul]

/-- A vector is fixed by the lifted matrix exactly when every regional slice is fixed. -/
theorem dependentRegionOperatorLift_mulVec_eq_self_iff
    [∀ v, Fintype (Out v)] (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (x : ((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ) :
    (dependentRegionOperatorLift R K).mulVec x = x ↔
      ∀ τ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1,
        K.mulVec (dependentRegionSlice R τ x) = dependentRegionSlice R τ x := by
  constructor
  · intro h τ
    rw [← dependentRegionSlice_mulVec_dependentRegionOperatorLift, h]
  · intro h
    funext η
    obtain ⟨⟨α, τ⟩, rfl⟩ := (dependentRegionConfigEquiv R).symm.surjective η
    exact congrFun ((dependentRegionSlice_mulVec_dependentRegionOperatorLift R K x τ).trans
      (h τ)) α

/-- The full product of site matrices factors across a region and its complement. -/
theorem regionPhysicalProductMatrix_univ_eq_reindex_kronecker (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ) :
    regionPhysicalProductMatrix Finset.univ F =
      Matrix.reindex (dependentRegionConfigEquiv (Out := Out) R).symm
        (dependentRegionConfigEquiv (Out := In) R).symm
        (regionPhysicalProductMatrix R F ⊗ₖ
          regionPhysicalProductMatrix (Finset.univ \ R) F) := by
  classical
  ext τ σ
  change (∏ w : {w : V // w ∈ Finset.univ}, F w.1 (τ w) (σ w)) =
    (∏ w : {w : V // w ∈ R},
      F w.1 (τ ⟨w.1, Finset.mem_univ w.1⟩) (σ ⟨w.1, Finset.mem_univ w.1⟩)) *
    ∏ w : {w : V // w ∈ Finset.univ \ R},
      F w.1 (τ ⟨w.1, Finset.mem_univ w.1⟩) (σ ⟨w.1, Finset.mem_univ w.1⟩)
  simp only [← Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
      (fun v => F v (τ ⟨v, Finset.mem_univ v⟩) (σ ⟨v, Finset.mem_univ v⟩)),
    ← Finset.prod_subtype R (fun _ => Iff.rfl)
      (fun v => F v (τ ⟨v, Finset.mem_univ v⟩) (σ ⟨v, Finset.mem_univ v⟩)),
    ← Finset.prod_subtype (Finset.univ \ R) (fun _ => Iff.rfl)
      (fun v => F v (τ ⟨v, Finset.mem_univ v⟩) (σ ⟨v, Finset.mem_univ v⟩)),
    ← Finset.compl_eq_univ_sdiff, Finset.prod_mul_prod_compl]

/-- An intertwining identity on a region extends through the product of all site maps. -/
theorem dependentRegionOperatorLift_intertwine
    [∀ v, Fintype (In v)] [∀ v, Fintype (Out v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ)
    (H : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (K : Matrix ((w : {w : V // w ∈ R}) → In w.1)
      ((w : {w : V // w ∈ R}) → In w.1) ℂ)
    (h : H * regionPhysicalProductMatrix R F = regionPhysicalProductMatrix R F * K) :
    dependentRegionOperatorLift R H * regionPhysicalProductMatrix Finset.univ F =
      regionPhysicalProductMatrix Finset.univ F * dependentRegionOperatorLift R K := by
  classical
  rw [regionPhysicalProductMatrix_univ_eq_reindex_kronecker R F]
  simp only [dependentRegionOperatorLift, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, h]

/-- Lifting respects subtraction of regional matrices. -/
theorem dependentRegionOperatorLift_sub (R : Finset V)
    (K L : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    dependentRegionOperatorLift R (K - L) =
      dependentRegionOperatorLift R K - dependentRegionOperatorLift R L := by
  classical
  ext α β
  simp [dependentRegionOperatorLift, Matrix.reindex_apply, sub_mul]

/-- Coefficients of a regional lift vanish unless all complementary coordinates agree. -/
theorem dependentRegionOperatorLift_apply [∀ v, DecidableEq (Out v)] (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (α β : (w : {w : V // w ∈ Finset.univ}) → Out w.1) :
    dependentRegionOperatorLift R K α β =
      if ∀ v, v ∉ R → α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩ then
        K (fun w => α ⟨w.1, Finset.mem_univ w.1⟩)
          (fun w => β ⟨w.1, Finset.mem_univ w.1⟩)
      else 0 := by
  classical
  simp [dependentRegionOperatorLift, Matrix.reindex_apply, Matrix.one_apply,
    dependentRegionConfigEquiv, funext_iff, mul_ite]

/-- Extend an operator on a subregion to the coordinates of a containing region. -/
noncomputable def dependentSubregionOperatorLift (R U : Finset V) (hRU : R ⊆ U)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    Matrix ((w : {w : V // w ∈ U}) → Out w.1)
      ((w : {w : V // w ∈ U}) → Out w.1) ℂ := by
  classical
  exact fun α β =>
    if ∀ v, ∀ hv : v ∈ U, v ∉ R → α ⟨v, hv⟩ = β ⟨v, hv⟩ then
      K (fun w => α ⟨w.1, hRU w.2⟩) (fun w => β ⟨w.1, hRU w.2⟩)
    else 0

/-- Extending first to a containing region and then globally gives the direct lift. -/
theorem dependentRegionOperatorLift_subregion (R U : Finset V) (hRU : R ⊆ U)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    dependentRegionOperatorLift U (dependentSubregionOperatorLift R U hRU K) =
      dependentRegionOperatorLift R K := by
  classical
  ext α β
  simp only [dependentRegionOperatorLift_apply]
  let k := K (fun w => α ⟨w.1, Finset.mem_univ w.1⟩)
    (fun w => β ⟨w.1, Finset.mem_univ w.1⟩)
  change (if ∀ v, v ∉ U → α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩ then
      if ∀ v, v ∈ U → v ∉ R →
          α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩ then k else 0
    else 0) =
    if ∀ v, v ∉ R → α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩ then
      k else 0
  by_cases hR : ∀ v, v ∉ R → α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩
  · have hU : ∀ v, v ∉ U → α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩ :=
      fun v hv => hR v (fun h => hv (hRU h))
    rw [ite_eq_left hU, ite_eq_left (fun v _ hv => hR v hv), ite_eq_left hR]
  · by_cases hU : ∀ v, v ∉ U →
        α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩
    · have hUR : ¬ ∀ v, v ∈ U → v ∉ R →
          α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩ := by
        intro h
        apply hR
        intro v hv
        by_cases hvU : v ∈ U
        · exact h v hvU hv
        · exact hU v hvU
      simp [hR, hUR]
    · simp [hR, hU]

/-- Every operator supported in a subregion is a lift from any containing region. -/
theorem exists_dependentRegionOperatorLift_of_subset (R U : Finset V) (hRU : R ⊆ U)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    ∃ L : Matrix ((w : {w : V // w ∈ U}) → Out w.1)
        ((w : {w : V // w ∈ U}) → Out w.1) ℂ,
      dependentRegionOperatorLift R K = dependentRegionOperatorLift U L :=
  ⟨dependentSubregionOperatorLift R U hRU K,
    (dependentRegionOperatorLift_subregion R U hRU K).symm⟩

/-- Products of regional lifts are supported on the union of the regions. -/
theorem exists_dependentRegionOperatorLift_mul_union [∀ v, Fintype (Out v)]
    (R S : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (L : Matrix ((w : {w : V // w ∈ S}) → Out w.1)
      ((w : {w : V // w ∈ S}) → Out w.1) ℂ) :
    ∃ M : Matrix ((w : {w : V // w ∈ R ∪ S}) → Out w.1)
        ((w : {w : V // w ∈ R ∪ S}) → Out w.1) ℂ,
      dependentRegionOperatorLift R K * dependentRegionOperatorLift S L =
        dependentRegionOperatorLift (R ∪ S) M := by
  obtain ⟨K', hK⟩ := exists_dependentRegionOperatorLift_of_subset R (R ∪ S)
    Finset.subset_union_left K
  obtain ⟨L', hL⟩ := exists_dependentRegionOperatorLift_of_subset S (R ∪ S)
    Finset.subset_union_right L
  exact ⟨K' * L', by rw [hK, hL, dependentRegionOperatorLift_mul]⟩

/-- Differences of regional lifts are supported on the union of the regions. -/
theorem exists_dependentRegionOperatorLift_sub_union (R S : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (L : Matrix ((w : {w : V // w ∈ S}) → Out w.1)
      ((w : {w : V // w ∈ S}) → Out w.1) ℂ) :
    ∃ M : Matrix ((w : {w : V // w ∈ R ∪ S}) → Out w.1)
        ((w : {w : V // w ∈ R ∪ S}) → Out w.1) ℂ,
      dependentRegionOperatorLift R K - dependentRegionOperatorLift S L =
        dependentRegionOperatorLift (R ∪ S) M := by
  refine ⟨dependentSubregionOperatorLift R (R ∪ S) Finset.subset_union_left K -
    dependentSubregionOperatorLift S (R ∪ S) Finset.subset_union_right L, ?_⟩
  rw [dependentRegionOperatorLift_sub, dependentRegionOperatorLift_subregion,
    dependentRegionOperatorLift_subregion]

/-- Commutators of regional lifts are supported on the union of the regions. -/
theorem exists_dependentRegionOperatorLift_commutator_union [∀ v, Fintype (Out v)]
    (R S : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (L : Matrix ((w : {w : V // w ∈ S}) → Out w.1)
      ((w : {w : V // w ∈ S}) → Out w.1) ℂ) :
    ∃ M : Matrix ((w : {w : V // w ∈ R ∪ S}) → Out w.1)
        ((w : {w : V // w ∈ R ∪ S}) → Out w.1) ℂ,
      dependentRegionOperatorLift R K * dependentRegionOperatorLift S L -
          dependentRegionOperatorLift S L * dependentRegionOperatorLift R K =
        dependentRegionOperatorLift (R ∪ S) M := by
  obtain ⟨K', hK⟩ := exists_dependentRegionOperatorLift_of_subset R (R ∪ S)
    Finset.subset_union_left K
  obtain ⟨L', hL⟩ := exists_dependentRegionOperatorLift_of_subset S (R ∪ S)
    Finset.subset_union_right L
  exact ⟨K' * L' - L' * K', by
    rw [hK, hL, dependentRegionOperatorLift_sub,
      dependentRegionOperatorLift_mul, dependentRegionOperatorLift_mul]⟩

/-- Multiplying a regional lift by a full product matrix separates the complementary factor. -/
theorem dependentRegionOperatorLift_mul_regionPhysicalProductMatrix
    [∀ v, Fintype (Out v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    dependentRegionOperatorLift R K * regionPhysicalProductMatrix Finset.univ F =
      Matrix.reindex (dependentRegionConfigEquiv (Out := Out) R).symm
        (dependentRegionConfigEquiv (Out := In) R).symm
        ((K * regionPhysicalProductMatrix R F) ⊗ₖ
          regionPhysicalProductMatrix (Finset.univ \ R) F) := by
  classical
  rw [regionPhysicalProductMatrix_univ_eq_reindex_kronecker R F]
  simp only [dependentRegionOperatorLift, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- A nonzero complementary factor can be canceled from a zero regional tensor product. -/
theorem dependentRegion_reindex_kronecker_eq_zero_iff (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → In w.1) ℂ)
    (L : Matrix ((w : {w : V // w ∈ Finset.univ \ R}) → Out w.1)
      ((w : {w : V // w ∈ Finset.univ \ R}) → In w.1) ℂ)
    (hL : L ≠ 0) :
    Matrix.reindex (dependentRegionConfigEquiv (Out := Out) R).symm
        (dependentRegionConfigEquiv (Out := In) R).symm (K ⊗ₖ L) = 0 ↔ K = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨τ, ρ, hτρ⟩ : ∃ τ ρ, L τ ρ ≠ 0 := by
      by_contra! hz
      exact hL (by ext τ ρ; exact hz τ ρ)
    ext α β
    have hz := congrFun (congrFun h ((dependentRegionConfigEquiv R).symm (α, τ)))
      ((dependentRegionConfigEquiv R).symm (β, ρ))
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, Matrix.kronecker_apply, Matrix.zero_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_right hτρ
  · rintro rfl
    simp [Matrix.reindex_apply]

/-- A nonzero complementary site product can be canceled after a regional lift. -/
theorem dependentRegionOperatorLift_mul_product_eq_zero_iff
    [∀ v, Fintype (Out v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (In v) ℂ)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (hF : regionPhysicalProductMatrix (Finset.univ \ R) F ≠ 0) :
    dependentRegionOperatorLift R K * regionPhysicalProductMatrix Finset.univ F = 0 ↔
      K * regionPhysicalProductMatrix R F = 0 := by
  rw [dependentRegionOperatorLift_mul_regionPhysicalProductMatrix]
  exact dependentRegion_reindex_kronecker_eq_zero_iff R _ _ hF

/-- If the regional site product fixes an operator, a nonzero complementary product
allows cancellation from the full product equation. -/
theorem dependentRegionOperatorLift_eq_zero_of_mul_product_eq_zero
    [∀ v, Fintype (Out v)] (R : Finset V)
    (F : (v : V) → Matrix (Out v) (Out v) ℂ)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ)
    (hK : K * regionPhysicalProductMatrix R F = K)
    (hF : regionPhysicalProductMatrix (Finset.univ \ R) F ≠ 0)
    (h : dependentRegionOperatorLift R K * regionPhysicalProductMatrix Finset.univ F = 0) :
    K = 0 := by
  rw [dependentRegionOperatorLift_mul_product_eq_zero_iff R F K hF, hK] at h
  exact h

end TNLean.PEPS
