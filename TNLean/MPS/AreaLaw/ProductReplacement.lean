/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import QICLean.Analysis.ProductOverlapReplacement
import QICLean.Analysis.ChronologicalGarbage
import TNLean.MPS.AreaLaw.SupportedCutRank
import QICLean.Entropy.RightLocalLift

/-!
# Product replacement without increasing the MPS bond dimension

Let `C` be the coefficient matrix of a chain vector at one cut. If `u = C w` and
`v = Cᵀ z`, the product matrix `u vᵀ` can be obtained either by applying a matrix
on the left factor or by applying one on the right factor:
`(u zᵀ) C = u vᵀ = C (v wᵀ)ᵀ`.
At every other cut, one of these operations acts entirely on one side. Hence no
cut rank increases. The characterization of open MPS by their internal cut ranks
then preserves the original bond bound, including zero bond bounds.

Applying the QICLean product-overlap theorem to the two coefficient spaces gives
a normalized product replacement with no smaller overlap with a product target.
The proof constructs a replacement for each supplied MPS and does not assume
that an optimal approximant exists.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2, `paper_v2.tex`,
the footnote at lines 436–470. The argument uses the same boundary subspaces as
the source, with cut ranks in place of changes to the boundary matrices.
-/

open Matrix
open scoped Kronecker
open ManyBody (cutMatrix)

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

private theorem cutMatrix_localLift (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (K : Matrix (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k))
      (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k)) ℂ) :
    cutMatrix (leftBlock L k) (toEuclideanLin (ManyBody.place (leftBlock L k) K) ψ) =
      K * cutMatrix (leftBlock L k) ψ := by
  rw [cutMatrix_toEuclideanLin, ManyBody.cutOperator_place,
    Matrix.schmidtCoeffMatrix_kronecker_one_mulVec]
  rfl

private theorem exists_left_supported_product
    (ψ χ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (u z : (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k)) → ℂ)
    (v : ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q) → ℂ)
    (hv : (cutMatrix (leftBlock L k) ψ)ᵀ *ᵥ z = v)
    (hχ : cutMatrix (leftBlock L k) χ = vecMulVec u v) :
    ∃ X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) X (leftBlock L k) ∧
      toEuclideanLin X ψ = χ := by
  refine ⟨ManyBody.place (leftBlock L k) (vecMulVec u z),
    ManyBody.place_mem_supportedOperators _, ?_⟩
  apply cutMatrix_injective k
  dsimp only
  rw [cutMatrix_localLift ψ k (vecMulVec u z), hχ, vecMulVec_mul, ← mulVec_transpose, hv]

private noncomputable def rightCutLift (k : ℕ)
    (R : Matrix ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q)
      ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q) ℂ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock L k)).symm
    (ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock L k)).symm (1 ⊗ₖ R)

private theorem cutMatrix_rightCutLift (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (R : Matrix ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q)
      ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q) ℂ) :
    cutMatrix (leftBlock L k) (toEuclideanLin (rightCutLift k R) ψ) =
      cutMatrix (leftBlock L k) ψ * Rᵀ := by
  rw [cutMatrix_toEuclideanLin]
  have hr : ManyBody.cutOperator (leftBlock L k) (rightCutLift k R) = 1 ⊗ₖ R := by
    ext a b
    simp [rightCutLift, ManyBody.cutOperator]
  rw [hr, Matrix.schmidtCoeffMatrix_one_kronecker_mulVec]
  rfl

private theorem exists_right_supported_product
    (ψ χ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (u : (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k)) → ℂ)
    (v w : ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q) → ℂ)
    (hu : cutMatrix (leftBlock L k) ψ *ᵥ w = u)
    (hχ : cutMatrix (leftBlock L k) χ = vecMulVec u v) :
    ∃ X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) X (leftBlock L k)ᶜ ∧
      toEuclideanLin X ψ = χ := by
  refine ⟨rightCutLift k (vecMulVec v w),
    Entropy.isSupportedOn_rightCut (leftBlock L k) _, ?_⟩
  apply cutMatrix_injective k
  dsimp only
  rw [cutMatrix_rightCutLift, hχ, transpose_vecMulVec, mul_vecMulVec, hu]

/-- Replacing a cut matrix by a product of vectors in its column and row spaces
cannot increase any cut rank. Source: arXiv:0705.0292v2, lines 436–470. -/
theorem rank_cutMatrix_le_of_product_mem_ranges
    (ψ χ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (u : EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k)))
    (v : EuclideanSpace ℂ ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q))
    (hu : u ∈ LinearMap.range (toEuclideanLin (cutMatrix (leftBlock L k) ψ)))
    (hv : v ∈ LinearMap.range (toEuclideanLin (cutMatrix (leftBlock L k) ψ)ᵀ))
    (hχ : cutMatrix (leftBlock L k) χ = vecMulVec (WithLp.ofLp u) (WithLp.ofLp v)) (j : ℕ) :
    (cutMatrix (leftBlock L j) χ).rank ≤ (cutMatrix (leftBlock L j) ψ).rank := by
  classical
  obtain ⟨w, hw⟩ := hu
  obtain ⟨z, hz⟩ := hv
  rcases isEmpty_or_nonempty (Fin L → Fin q) with hconfig | hconfig
  · exact le_of_eq (congrArg
      (fun ξ : EuclideanSpace ℂ (Fin L → Fin q) ↦ (cutMatrix (leftBlock L j) ξ).rank)
      (Subsingleton.elim χ ψ))
  · obtain ⟨σ₀⟩ := hconfig
    by_cases hjk : j ≤ k
    · obtain ⟨X, hX, hXχ⟩ := exists_right_supported_product ψ χ k
        (WithLp.ofLp u) (WithLp.ofLp v) (WithLp.ofLp w) (congrArg WithLp.ofLp hw) hχ
      have hdis : Disjoint (leftBlock L k)ᶜ (leftBlock L j) :=
        Finset.disjoint_left.mpr fun i hi hj ↦ (Finset.mem_compl.mp hi)
          (mem_leftBlock.mpr ((mem_leftBlock.mp hj).trans_le hjk))
      simpa only [hXχ] using rank_cutMatrix_toEuclideanLin_le_of_isOneSided ψ j
        (hX.isOneSided_of_disjoint hdis (fun i ↦ σ₀ i.1))
    · obtain ⟨X, hX, hXχ⟩ := exists_left_supported_product ψ χ k
        (WithLp.ofLp u) (WithLp.ofLp z) (WithLp.ofLp v) (congrArg WithLp.ofLp hz) hχ
      have hsub : leftBlock L k ⊆ leftBlock L j := fun i hi ↦
        mem_leftBlock.mpr ((mem_leftBlock.mp hi).trans (lt_of_not_ge hjk))
      simpa only [hXχ] using rank_cutMatrix_toEuclideanLin_le_of_isOneSided ψ j
        (hX.isOneSided_of_subset hsub (fun i ↦ σ₀ i.1))

/-- Product replacement within the two cut supports preserves the MPS bond bound.
Source: arXiv:0705.0292v2, the footnote at lines 436–470. -/
theorem IsOpenMPS.of_product_mem_cut_ranges {D : ℕ}
    {ψ χ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) (k : ℕ)
    (u : EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k)))
    (v : EuclideanSpace ℂ ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q))
    (hu : u ∈ LinearMap.range (toEuclideanLin (cutMatrix (leftBlock L k) ψ)))
    (hv : v ∈ LinearMap.range (toEuclideanLin (cutMatrix (leftBlock L k) ψ)ᵀ))
    (hχ : cutMatrix (leftBlock L k) χ = vecMulVec (WithLp.ofLp u) (WithLp.ofLp v)) :
    IsOpenMPS L q D (fun x ↦ χ x) :=
  isOpenMPS_of_internal_cutMatrix_rank_le χ fun j hj0 hjL ↦
    (rank_cutMatrix_le_of_product_mem_ranges ψ χ k u v hu hv hχ j).trans
      (hψ.rank_cutMatrix_le hj0 hjL)

/-- A normalized MPS can be replaced by a normalized MPS that factors across a given
cut, without increasing any cut rank or decreasing its overlap with a product target.
Source: arXiv:0705.0292v2, the footnote at lines 436–470. -/
theorem IsOpenMPS.exists_product_overlap_ge {D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) (hnorm : ‖ψ‖ = 1) (k : ℕ)
    (a : EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k)))
    (b : EuclideanSpace ℂ ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q)) :
    ∃ (χ : EuclideanSpace ℂ (Fin L → Fin q))
      (u : EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ ↦ Fin q) (leftBlock L k)))
      (v : EuclideanSpace ℂ ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q)),
      IsOpenMPS L q D (fun x ↦ χ x) ∧ ‖χ‖ = 1 ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      cutMatrix (leftBlock L k) χ = vecMulVec (WithLp.ofLp u) (WithLp.ofLp v) ∧
      (∀ j, (cutMatrix (leftBlock L j) χ).rank ≤ (cutMatrix (leftBlock L j) ψ).rank) ∧
      ‖inner ℂ (euclideanTensorVector a b) (ManyBody.cutVector (leftBlock L k) ψ)‖ ≤
        ‖inner ℂ a u‖ * ‖inner ℂ b v‖ := by
  have hC : ‖ManyBody.cutVector (leftBlock L k) ψ‖ = 1 :=
    (Entropy.norm_cutVector (leftBlock L k) ψ).trans hnorm
  obtain ⟨u, v, hu, hv, huC, hvC, huv⟩ :=
    Matrix.exists_unit_product_overlap_ge (cutMatrix (leftBlock L k) ψ) hC a b
  let χ : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2 fun x ↦
    euclideanTensorVector u v ((ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock L k)) x)
  have hcut : ManyBody.cutVector (leftBlock L k) χ = euclideanTensorVector u v := by
    ext ij
    simp [χ]
  have hmatrix :
      cutMatrix (leftBlock L k) χ = vecMulVec (WithLp.ofLp u) (WithLp.ofLp v) := by
    change schmidtCoeffMatrix (WithLp.ofLp (ManyBody.cutVector (leftBlock L k) χ)) = _
    rw [hcut]
    rfl
  refine ⟨χ, u, v, hψ.of_product_mem_cut_ranges k u v huC hvC hmatrix,
    ?_, hu, hv, hmatrix,
    rank_cutMatrix_le_of_product_mem_ranges ψ χ k u v huC hvC hmatrix, huv⟩
  rw [← Entropy.norm_cutVector (leftBlock L k) χ, hcut, norm_euclideanTensorVector,
    hu, hv, one_mul]

end TNLean.MPS.AreaLaw
