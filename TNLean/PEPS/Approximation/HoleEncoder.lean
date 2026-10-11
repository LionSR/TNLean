/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.NestedCylinderOrthogonalization
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Exact tags and zero resets for one hole

The orthogonalized inside spaces determine genuine orthonormal bases and a finite
tag space. Each tag branch extracts one basis coefficient, resets its own region
to a chosen computational configuration, and preserves the complementary raw
coordinates. Every raw register remains in the output.

This is the exact one-hole construction in the polynomial PEPS approximation
manuscript, `05-frames.tex`, lines 13–97 at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Party layouts, products over frames,
and the approximation estimate are separate statements.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {ι : Type*} [Fintype ι]

/-- Extract a vector coefficient and reset the output to one computational basis state. -/
noncomputable def coordinateResetMatrix (zero : ι) (v : ι → ℂ) : Matrix ι ι ℂ := by
  classical
  exact Matrix.of fun a b => if a = zero then star (v b) else 0

/-- A computational reset has unit Gram factor, with no normalization assumption on the
coefficient vector. -/
theorem coordinateResetMatrix_gram (zero : ι) (v : ι → ℂ) :
    (coordinateResetMatrix zero v).conjTranspose * coordinateResetMatrix zero v =
      Matrix.vecMulVec v (star v) := by
  classical
  ext a b
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, coordinateResetMatrix,
    Matrix.vecMulVec_apply]

omit [Fintype ι] in
/-- Passing to the physical Euclidean inner product preserves the inside dimension. -/
theorem finrank_coordinateSubspaceES (S : Submodule ℂ (ι → ℂ)) :
    Module.finrank ℂ (coordinateSubspaceES S) = Module.finrank ℂ S :=
  (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.finrank_map_eq S

/-- The coordinate projector is the sum of rank-one matrices from any genuine
orthonormal basis of the physical subspace. -/
theorem coordinateRangeProjector_eq_sum_basis {κ : Type*} [Fintype κ]
    (S : Submodule ℂ (ι → ℂ)) (b : OrthonormalBasis κ ℂ (coordinateSubspaceES S)) :
    coordinateRangeProjector S =
      ∑ k, Matrix.vecMulVec (fun a => (b k).val a) (star (fun a => (b k).val a)) := by
  classical
  unfold coordinateRangeProjector
  rw [b.starProjection_eq_sum_rankOne]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum,
    InnerProductSpace.symm_toEuclideanLin_rankOne]

private theorem stacked_matrix_gram {κ μ ν : Type*} [Fintype κ] [Fintype μ]
    (B : κ → Matrix μ ν ℂ) :
    (Matrix.of (fun (p : κ × μ) (q : ν) => B p.1 p.2 q)).conjTranspose *
      Matrix.of (fun (p : κ × μ) (q : ν) => B p.1 p.2 q) =
      ∑ k, (B k).conjTranspose * B k := by
  ext a b
  simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

private theorem inner_mulVec_gram {μ : Type*} [Fintype μ]
    (M : Matrix μ ι ℂ) (x : ι → ℂ) :
    inner ℂ (WithLp.toLp 2 (M *ᵥ x)) (WithLp.toLp 2 (M *ᵥ x)) =
      star x ⬝ᵥ ((M.conjTranspose * M) *ᵥ x) := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

private theorem norm_mulVec_eq_of_gram_eq {μ ν : Type*} [Fintype μ] [Fintype ν]
    (A : Matrix μ ι ℂ) (B : Matrix ν ι ℂ) (h : A.conjTranspose * A = B.conjTranspose * B)
    (x : ι → ℂ) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ = ‖WithLp.toLp 2 (B *ᵥ x)‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    inner_mulVec_gram, inner_mulVec_gram, h]

/-- The source's empty-outer-sample convention retains one tag and every raw coordinate. -/
noncomputable def identityHoleEncoder : Matrix (PUnit.{1} × ι) ι ℂ := by
  classical
  exact Matrix.of fun p b => (1 : Matrix ι ι ℂ) p.2 b

open Classical in
/-- The one-tag identity encoder has identity Gram matrix, including an empty raw alphabet. -/
theorem identityHoleEncoder_gram :
    (identityHoleEncoder (ι := ι)).conjTranspose * identityHoleEncoder (ι := ι) =
      (1 : Matrix ι ι ℂ) := by
  classical
  simpa [identityHoleEncoder] using
    stacked_matrix_gram (fun _ : PUnit.{1} => (1 : Matrix ι ι ℂ))

/-- Appending the sole identity tag preserves every input coefficient. -/
@[simp]
theorem identityHoleEncoder_mulVec (x : ι → ℂ) (a : ι) :
    (identityHoleEncoder *ᵥ x) (PUnit.unit, a) = x a := by
  classical
  change ((1 : Matrix ι ι ℂ) *ᵥ x) a = x a
  simp

/-- The identity encoding preserves the physical Hilbert norm. -/
theorem identityHoleEncoder_norm (x : ι → ℂ) :
    ‖WithLp.toLp 2 (identityHoleEncoder *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  classical
  have h : (identityHoleEncoder (ι := ι)).conjTranspose * identityHoleEncoder =
      (1 : Matrix ι ι ℂ).conjTranspose * 1 := by
    simp [identityHoleEncoder_gram]
  simpa using norm_mulVec_eq_of_gram_eq identityHoleEncoder (1 : Matrix ι ι ℂ) h x

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)] {n : ℕ}

omit [∀ v, Fintype (Out v)] in
private theorem dependentRegionOperatorLift_sum {κ : Type*} [Fintype κ] (R : Finset V)
    (B : κ → Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    dependentRegionOperatorLift R (∑ k, B k) =
      ∑ k, dependentRegionOperatorLift R (B k) := by
  classical
  ext α β
  simp [dependentRegionOperatorLift, Matrix.reindex_apply, Matrix.sum_apply, Finset.sum_mul]

/-- The tag records the branch and one actual inside innovation basis index. -/
abbrev HoleEncoderTag (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :=
  Σ j : Fin n, Fin (Module.finrank ℂ (coordinateSubspaceES
    (nestedCylinderInnovation R hR S j)))

/-- A genuine orthonormal basis of the projected-image inside innovation. -/
noncomputable def holeEncoderBasis (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (j : Fin n) :
    OrthonormalBasis (Fin (Module.finrank ℂ (coordinateSubspaceES
      (nestedCylinderInnovation R hR S j)))) ℂ
      (coordinateSubspaceES (nestedCylinderInnovation R hR S j)) :=
  stdOrthonormalBasis ℂ _

/-- The tag count is exactly the sum of inside innovation dimensions. -/
theorem card_holeEncoderTag (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    Fintype.card (HoleEncoderTag R hR S) =
      ∑ j, Module.finrank ℂ (nestedCylinderInnovation R hR S j) := by
  simp [HoleEncoderTag, Fintype.card_sigma, finrank_coordinateSubspaceES]

/-- Only inside ranks contribute to the tag bound; complementary raw dimensions do not. -/
theorem card_holeEncoderTag_le (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    Fintype.card (HoleEncoderTag R hR S) ≤ ∑ j, Module.finrank ℂ (S j) := by
  rw [card_holeEncoderTag]
  exact sum_finrank_nestedCylinderInnovation_le R hR S

/-- The rectangular one-hole encoder. The supplied global computational configuration
gives a unit reset on every branch, and the full raw output factor retains every site. -/
noncomputable def holeEncoder (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) :
    Matrix (HoleEncoderTag R hR S × ((w : {w : V // w ∈ Finset.univ}) → Out w.1))
      ((w : {w : V // w ∈ Finset.univ}) → Out w.1) ℂ :=
  Matrix.of fun p β => dependentRegionOperatorLift (R p.1.1)
    (coordinateResetMatrix (fun w => zero w.1)
      (fun a => (holeEncoderBasis R hR S p.1.1 p.1.2).val a)) p.2 β

/-- The encoder Gram matrix is exactly the projector onto the original cylinder span.
The orthogonal decomposition and its sum are derived from the original subspaces. -/
theorem holeEncoder_gram (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) :
    (holeEncoder R hR S zero).conjTranspose * holeEncoder R hR S zero =
      coordinateRangeProjector (⨆ j, dependentRegionCylinder (R j) (S j)) := by
  classical
  let B (t : HoleEncoderTag R hR S) :=
    dependentRegionOperatorLift (R t.1)
      (coordinateResetMatrix (fun w => zero w.1)
        (fun a => (holeEncoderBasis R hR S t.1 t.2).val a))
  have hg : (holeEncoder R hR S zero).conjTranspose * holeEncoder R hR S zero =
      ∑ t, (B t).conjTranspose * B t := stacked_matrix_gram B
  rw [hg, Fintype.sum_sigma, nestedCylinderInnovation_projector_sum R hR S]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [B]
  simp_rw [dependentRegionOperatorLift_conjTranspose,
    ← dependentRegionOperatorLift_mul, coordinateResetMatrix_gram]
  rw [← dependentRegionOperatorLift_sum,
    ← coordinateRangeProjector_eq_sum_basis _ (holeEncoderBasis R hR S j)]

open Classical in
/-- A branch coefficient vanishes unless its region is reset and its complement is unchanged. -/
theorem holeEncoder_apply (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) (t : HoleEncoderTag R hR S)
    (α β : (w : {w : V // w ∈ Finset.univ}) → Out w.1) :
    holeEncoder R hR S zero (t, α) β =
      if ∀ v, v ∉ R t.1 → α ⟨v, Finset.mem_univ v⟩ = β ⟨v, Finset.mem_univ v⟩ then
        if (fun w : {w : V // w ∈ R t.1} => α ⟨w.1, Finset.mem_univ w.1⟩) =
            (fun w : {w : V // w ∈ R t.1} => zero w.1) then
          star ((holeEncoderBasis R hR S t.1 t.2).val
            (fun w => β ⟨w.1, Finset.mem_univ w.1⟩))
        else 0
      else 0 := by
  classical
  unfold holeEncoder
  rw [Matrix.of_apply, dependentRegionOperatorLift_apply]
  simp only [coordinateResetMatrix, Matrix.of_apply]

/-- A raw output coordinate inside this branch's region must be at the reset value. -/
theorem holeEncoder_eq_zero_of_not_reset (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) (t : HoleEncoderTag R hR S)
    (α β : (w : {w : V // w ∈ Finset.univ}) → Out w.1)
    (v : V) (hv : v ∈ R t.1) (hα : α ⟨v, Finset.mem_univ v⟩ ≠ zero v) :
    holeEncoder R hR S zero (t, α) β = 0 := by
  classical
  have hne : (fun w : {w : V // w ∈ R t.1} => α ⟨w.1, Finset.mem_univ w.1⟩) ≠
      (fun w : {w : V // w ∈ R t.1} => zero w.1) := fun h => hα (congrFun h ⟨v, hv⟩)
  simp [holeEncoder_apply, hne]

/-- Complementary raw coordinates are preserved coefficient by coefficient. -/
theorem holeEncoder_eq_zero_of_complement_ne (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) (t : HoleEncoderTag R hR S)
    (α β : (w : {w : V // w ∈ Finset.univ}) → Out w.1)
    (v : V) (hv : v ∉ R t.1)
    (hαβ : α ⟨v, Finset.mem_univ v⟩ ≠ β ⟨v, Finset.mem_univ v⟩) :
    holeEncoder R hR S zero (t, α) β = 0 := by
  classical
  have hne : ¬ ∀ w, w ∉ R t.1 →
      α ⟨w, Finset.mem_univ w⟩ = β ⟨w, Finset.mem_univ w⟩ := fun h => hαβ (h v hv)
  simp [holeEncoder_apply, hne]

open Classical in
/-- The rectangular encoder is a contraction for the physical L² operator norm. -/
theorem holeEncoder_opNorm_le_one (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) : ‖holeEncoder R hR S zero‖ ≤ 1 := by
  classical
  have hp : ‖coordinateRangeProjector
      (⨆ j, dependentRegionCylinder (R j) (S j))‖ ≤ 1 := by
    exact IsStarProjection.norm_le _ (coordinateRangeProjector_isStarProjection _)
  rw [← holeEncoder_gram R hR S zero, Matrix.l2_opNorm_conjTranspose_mul_self] at hp
  nlinarith [norm_nonneg (holeEncoder R hR S zero)]

/-- A one-hole encoding has exactly the norm of the original cylinder-span projection. -/
theorem holeEncoder_norm_eq_projector (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v)
    (x : ((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ) :
    ‖WithLp.toLp 2 (holeEncoder R hR S zero *ᵥ x)‖ =
      ‖WithLp.toLp 2 (coordinateRangeProjector
        (⨆ j, dependentRegionCylinder (R j) (S j)) *ᵥ x)‖ := by
  classical
  apply norm_mulVec_eq_of_gram_eq
  rw [holeEncoder_gram]
  symm
  change star (coordinateRangeProjector _) * coordinateRangeProjector _ = _
  rw [(coordinateRangeProjector_isStarProjection _).isSelfAdjoint.star_eq,
    (coordinateRangeProjector_isStarProjection _).isIdempotentElem.eq]

/-- The one-hole encoder preserves the physical Hilbert norm on the span of the
original regional cylinders. This is a consequence of the projector Gram identity
in polynomial-PEPS, `05-frames.tex`, `eq:encoder-contraction`, lines 62–64.
-/
theorem holeEncoder_norm_eq_of_mem (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v)
    (x : ((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ)
    (hx : x ∈ ⨆ j, dependentRegionCylinder (R j) (S j)) :
    ‖WithLp.toLp 2 (holeEncoder R hR S zero *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  exact (holeEncoder_norm_eq_projector R hR S zero x).trans
    (congrArg (fun y ↦ ‖WithLp.toLp 2 y‖)
      ((coordinateRangeProjector_mulVec_eq_self_iff _ x).mpr hx))

/-- Contractivity holds on every physical vector, without a reference-state assumption. -/
theorem holeEncoder_norm_le (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v)
    (x : ((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ) :
    ‖WithLp.toLp 2 (holeEncoder R hR S zero *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  classical
  calc
    _ ≤ ‖holeEncoder R hR S zero‖ * ‖WithLp.toLp 2 x‖ :=
      Matrix.l2_opNorm_mulVec _ (WithLp.toLp 2 x)
    _ ≤ 1 * ‖WithLp.toLp 2 x‖ :=
      mul_le_mul_of_nonneg_right (holeEncoder_opNorm_le_one R hR S zero) (norm_nonneg _)
    _ = _ := one_mul _

/-- An empty innovation family gives the zero encoder, rather than the empty-outer
identity convention. -/
theorem holeEncoder_empty (R : Fin 0 → Finset V) (hR : Monotone R)
    (S : (j : Fin 0) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (zero : (v : V) → Out v) : holeEncoder R hR S zero = 0 := by
  ext ⟨⟨j, k⟩, α⟩ β
  exact Fin.elim0 j

/-- Zero inside spaces produce no tags and the zero encoder. -/
theorem holeEncoder_zero_spaces (R : Fin n → Finset V) (hR : Monotone R)
    (zero : (v : V) → Out v) : holeEncoder R hR (fun _ => ⊥) zero = 0 := by
  have hc : Fintype.card (HoleEncoderTag (Out := Out) R hR (fun _ => ⊥)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa using card_holeEncoderTag_le (Out := Out) R hR (fun _ => ⊥)
  let : IsEmpty (HoleEncoderTag (Out := Out) R hR (fun _ => ⊥)) :=
    Fintype.card_eq_zero_iff.mp hc
  ext ⟨t, α⟩ β
  exact isEmptyElim t

end TNLean.PEPS
