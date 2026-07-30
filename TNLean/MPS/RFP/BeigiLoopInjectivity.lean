/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.MPS.RFP.BeigiLoopSchmidtSupport

/-!
# Injectivity of the minimal Beigi loop tensor

The rank factors of a loop bond coefficient matrix span its Schmidt support.
Their pairwise outer products are the letters of the minimal loop tensor, so
these letters span the full matrix algebra.  Thus the coordinate tensor and
its physical unitary rotation are injective, and the latter is normal.

This module makes no normalization or transfer-idempotence assertion and does
not identify the loop tensors with the basis of normal tensors of the original
tensor.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
  Section IV, equation (10) and the paragraph following it.
-/

open scoped BigOperators Kronecker Matrix

namespace Matrix

/-- Pairwise outer products of two spanning vector families span the full
matrix space. -/
private theorem span_range_vecMulVec_eq_top
    {ι κ n : Type*} [Finite n]
    (u : ι → n → ℂ) (v : κ → n → ℂ)
    (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ
      (Set.range fun p : ι × κ ↦ Matrix.vecMulVec (u p.1) (v p.2)) = ⊤ := by
  classical
  letI := Fintype.ofFinite n
  let S := Submodule.span ℂ
    (Set.range fun p : ι × κ ↦ Matrix.vecMulVec (u p.1) (v p.2))
  have hright (i : ι) : ∀ y ∈ Submodule.span ℂ (Set.range v),
      Matrix.vecMulVec (u i) y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨(i, j), rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
        simpa only [Matrix.vecMulVec_add] using S.add_mem hx hy
    | smul c x _ hx =>
        simpa only [Matrix.vecMulVec_smul] using S.smul_mem c hx
  have houter : ∀ x ∈ Submodule.span ℂ (Set.range u),
      ∀ y ∈ Submodule.span ℂ (Set.range v),
        Matrix.vecMulVec x y ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hright i
    | zero =>
        intro y _
        simp
    | add x y _ _ hx hy =>
        intro z hz
        simpa only [Matrix.add_vecMulVec] using S.add_mem (hx z hz) (hy z hz)
    | smul c x _ hx =>
        intro y hy
        simpa only [Matrix.smul_vecMulVec] using S.smul_mem c (hx y hy)
  refine (Submodule.eq_top_iff_forall_basis_mem (Matrix.stdBasis ℂ n n)).2 ?_
  rintro ⟨i, j⟩
  have hi : Pi.single i (1 : ℂ) ∈ Submodule.span ℂ (Set.range u) := by
    rw [hu]
    exact Submodule.mem_top
  have hj : Pi.single j (1 : ℂ) ∈ Submodule.span ℂ (Set.range v) := by
    rw [hv]
    exact Submodule.mem_top
  rw [Matrix.stdBasis_eq_single, Matrix.single_eq_single_vecMulVec_single]
  exact houter _ hi _ hj

end Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- A unitary change of physical coordinates preserves one-site
injectivity. -/
private theorem isInjective_rotatePhysical (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (hA : IsInjective A) :
    IsInjective (rotatePhysical u A) := by
  classical
  have hstar : uᴴ * u = 1 := mul_eq_one_comm.mp hu
  have hletter (j : Fin d) :
      A j = ∑ i : Fin d, (uᴴ) j i • rotatePhysical u A i := by
    have hentry (k : Fin d) :
        ∑ i : Fin d, (uᴴ) j i * u i k = if j = k then 1 else 0 := by
      have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ ↦ M j k) hstar
      simpa [Matrix.mul_apply, Matrix.one_apply] using h
    simp only [rotatePhysical_apply]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hentry]
    simp
  rw [IsInjective, eq_top_iff]
  intro M _
  have hM : M ∈ Submodule.span ℂ (Set.range A) := hA ▸ Submodule.mem_top
  apply (Submodule.span_le.mpr ?_) hM
  rintro _ ⟨j, rfl⟩
  rw [hletter]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

namespace BeigiSectorGraphData

open FiniteWeightedDigraph

variable {A : MPSTensor d D}

private theorem loopSchmidtFactorization_rightFactor_rank
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    (F.loopSchmidtFactorization l).rightFactor.rank =
      F.loopSchmidtRank l := by
  apply le_antisymm
  · exact Matrix.rank_le_width _
  · have h := Matrix.rank_mul_le_left
      (F.loopSchmidtFactorization l).rightFactor
      (F.loopSchmidtFactorization l).leftFactor
    rw [(F.loopSchmidtFactorization l).mul_eq] at h
    simpa [loopSchmidtRank, Matrix.schmidtRank] using h

private theorem loopSchmidtFactorization_leftFactor_rank
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    (F.loopSchmidtFactorization l).leftFactor.rank =
      F.loopSchmidtRank l := by
  apply le_antisymm
  · exact Matrix.rank_le_height _
  · have h := Matrix.rank_mul_le_right
      (F.loopSchmidtFactorization l).rightFactor
      (F.loopSchmidtFactorization l).leftFactor
    rw [(F.loopSchmidtFactorization l).mul_eq] at h
    simpa [loopSchmidtRank, Matrix.schmidtRank] using h

/-- The sector-coordinate loop tensor is injective on its Schmidt support.

The rank factors have maximal possible rank on their common Schmidt index.
Their columns and rows therefore span that index space, so their outer
products span the full matrix algebra.

Source context: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation),
and Section IV, equation (10) and the paragraph following it.  The
Schmidt-support consequence is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem minimalLoopCoordinateTensor_isInjective
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    IsInjective (F.minimalLoopCoordinateTensor l) := by
  classical
  have hleft : Submodule.span ℂ
      (Set.range (F.loopSchmidtFactorization l).leftFactor.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols,
      F.loopSchmidtFactorization_leftFactor_rank l]
    simp
  have hright : Submodule.span ℂ
      (Set.range (F.loopSchmidtFactorization l).rightFactor.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row,
      F.loopSchmidtFactorization_rightFactor_rank l]
    simp
  have houter := Matrix.span_range_vecMulVec_eq_top
    (F.loopSchmidtFactorization l).leftFactor.col
    (F.loopSchmidtFactorization l).rightFactor.row hleft hright
  rw [IsInjective, eq_top_iff]
  intro M _
  have hM : M ∈ Submodule.span ℂ
      (Set.range fun p : Fin (F.leftDim l.1) × Fin (F.rightDim l.1) ↦
        Matrix.vecMulVec
          ((F.loopSchmidtFactorization l).leftFactor.col p.1)
          ((F.loopSchmidtFactorization l).rightFactor.row p.2)) := by
    rw [houter]
    exact Submodule.mem_top
  apply (Submodule.span_le.mpr ?_) hM
  rintro _ ⟨⟨a, q⟩, rfl⟩
  have hletter := F.minimalLoopCoordinateTensor_sector_apply l q a
  have hmem : F.minimalLoopCoordinateTensor l
        (F.sectorEquiv ⟨l.1, (q, a)⟩) ∈
      Submodule.span ℂ (Set.range (F.minimalLoopCoordinateTensor l)) :=
    Submodule.subset_span ⟨F.sectorEquiv ⟨l.1, (q, a)⟩, rfl⟩
  rw [hletter] at hmem
  exact hmem

/-- The physical loop tensor is injective on its Schmidt support.

Source context: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation),
and Section IV, equation (10) and the paragraph following it.  The physical
unitary preserves the one-site spanning property. -/
theorem minimalLoopTensor_isInjective
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    IsInjective (F.minimalLoopTensor l) := by
  rw [minimalLoopTensor]
  apply isInjective_rotatePhysical _ F.unitary
  · simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem F.unitary_mem
  · exact F.minimalLoopCoordinateTensor_isInjective l

/-- The physical loop tensor is normal on its Schmidt support.

Source context: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation),
and Section IV, equation (10) and the paragraph following it.  This is the
one-site-injective consequence only; no normalization or transfer identity is
asserted. -/
theorem minimalLoopTensor_isNormal
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    IsNormal (F.minimalLoopTensor l) :=
  (F.minimalLoopTensor_isInjective l).isNormal

end BeigiSectorGraphData

end MPSTensor
