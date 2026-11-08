/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceUV

/-!
# Scalar transport of the actual normalized source factors

A nonzero scalar multiplies each source cut without changing its rank.
Keep the normalized left factors, multiply both right factors by the scalar,
and divide both right inverses by it. The unshifted source gate is multiplied
by the square of the scalar; the shifted source gate is unchanged. A sign
therefore disappears in the actual two-letter source gate, as needed for the
even-family comparison in arXiv:1703.09188, `PropChiral`, lines 1237–1252.
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- Nonzero scaling preserves both source-cut ranks. Source: CPSV17,
`II_SVD`, lines 463–486, applied to scalar-multiple source cuts. -/
theorem source_ranks_smul {d D : ℕ} (U : MPOTensor d D) {c : ℂ} (hc : c ≠ 0) :
    r[c • U] = r[U] ∧ ℓ[c • U] = ℓ[U] := by
  constructor
  · change (c • sourceCutM₁ U).rank = (sourceCutM₁ U).rank
    exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)
  · change (c • sourceCutM₂ U).rank = (sourceCutM₂ U).rank
    exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)

namespace SourceFactors

/-- Scale the right factors and inversely scale their right inverses, retaining
both normalized left factors and the recorded weight. Source: CPSV17,
`eq:sf-svd`, `Y1Y1X1X1` and `YZ=1`, lines 479–506. -/
noncomputable def smul {d D : ℕ} {U : MPOTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (c : ℂ) (hc : c ≠ 0) : SourceFactors (c • U) ρ := by
  let er := finCongr (source_ranks_smul U hc).1.symm
  let el := finCongr (source_ranks_smul U hc).2.symm
  refine {
    X₁ := Matrix.reindex (Equiv.refl _) er S.X₁
    Y₁ := Matrix.reindex er (Equiv.refl _) (c • S.Y₁)
    Z₁ := Matrix.reindex (Equiv.refl _) er (c⁻¹ • S.Z₁)
    X₂ := Matrix.reindex (Equiv.refl _) el S.X₂
    Y₂ := Matrix.reindex el (Equiv.refl _) (c • S.Y₂)
    Z₂ := Matrix.reindex (Equiv.refl _) el (c⁻¹ • S.Z₂)
    sourceCutM₁_eq := ?_
    sourceCutM₂_eq := ?_
    X₁_weighted_isometry := ?_
    X₂_isometry := ?_
    Y₁_mul_Z₁ := ?_
    Y₂_mul_Z₂ := ?_
  }
  · change c • sourceCutM₁ U = _
    rw [S.sourceCutM₁_eq, ← Matrix.mul_smul]
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) er (Equiv.refl _) _ _).symm
  · change c • sourceCutM₂ U = _
    rw [S.sourceCutM₂_eq, ← Matrix.mul_smul]
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) el (Equiv.refl _) _ _).symm
  · rw [Matrix.conjTranspose_reindex]
    change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _) S.X₁ᴴ *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _)
          (sourceWeight (d := d) ρ) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er S.X₁ = 1
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul,
      S.X₁_weighted_isometry]
    simp
  · exact Matrix.IsIsometry.reindex _ S.X₂_isometry (Equiv.refl _) el
  · change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl (Fin D × Fin d))
        (c • S.Y₁) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin D × Fin d)) er
        (c⁻¹ • S.Z₁) = 1
    rw [Matrix.reindexLinearEquiv_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, mul_inv_cancel₀ hc, one_smul, S.Y₁_mul_Z₁]
    simp
  · change Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl (Fin d × Fin D))
        (c • S.Y₂) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl (Fin d × Fin D)) el
        (c⁻¹ • S.Z₂) = 1
    rw [Matrix.reindexLinearEquiv_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, mul_inv_cancel₀ hc, one_smul, S.Y₂_mul_Z₂]
    simp

/-- The two right factors each contribute one scalar to the source gate.
In particular a scalar with square one disappears. Source: CPSV17,
`uvdef`, lines 513–524; its use in `PropChiral`, lines 1237–1252. -/
theorem sourceU_smul {d D : ℕ} {U : MPOTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (c : ℂ) (hc : c ≠ 0) :
    sourceU (c • U) (S.smul c hc) = c ^ 2 •
      Matrix.reindex
        (Equiv.prodCongr (finCongr (source_ranks_smul U hc).2.symm)
          (finCongr (source_ranks_smul U hc).1.symm)) (Equiv.refl _)
        (sourceU U S) := by
  let er := finCongr (source_ranks_smul U hc).1.symm
  let el := finCongr (source_ranks_smul U hc).2.symm
  ext ⟨l, r⟩ ⟨i, j⟩
  change (∑ β : Fin D,
      (c * S.Y₂ (el.symm l) (i, β)) * (c * S.Y₁ (er.symm r) (β, j))) =
    c ^ 2 * (∑ β : Fin D, S.Y₂ (el.symm l) (i, β) * S.Y₁ (er.symm r) (β, j))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- Scaling a tensor leaves the shifted source gate unchanged after the
canonical rank identification, since its normalized left factors are kept.
Source: CPSV17, `uvdef`, lines 513–524. -/
theorem sourceV_smul {d D : ℕ} {U : MPOTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (c : ℂ) (hc : c ≠ 0) :
    sourceV (c • U) (S.smul c hc) =
      Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr (source_ranks_smul U hc).1.symm)
          (finCongr (source_ranks_smul U hc).2.symm))
        (sourceV U S) := by
  rfl

end SourceFactors
end MPOTensor
