/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalBlockGroundSpaceAtInjectivityLength

/-!
# Uniform interaction range for canonical tensors on short rings

For a canonical tensor of positive bond dimension \(D\), the distinct normal
representatives have a simultaneous injectivity length \(S\) satisfying
\(S+1\leq 3D^5\). Consequently every parent interaction of range
\(3D^5\leq L\leq N\) has the ground space spanned by their periodic
matrix product vectors. The equality includes the ring \(N=L=3D^5\).

The local terms may be arbitrary positive operators with the prescribed
parent kernels. Repeated copies and the ambient reconstruction of the
canonical tensor require no additional assumptions.

The estimate follows from the blocking argument of arXiv:1606.00608,
lines 317--345. Its ground-space consequence is the block-injective
intersection and periodic closure theorem of arXiv:2011.12127,
Section IV.C, lines 2114--2129.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-- The distinct normal representatives of a canonical tensor have a
positive simultaneous injectivity length \(S\) for which the parent
interaction range \(S+1\) is at most \(3D^5\).

Source: arXiv:1606.00608, lines 317--345; the additional site is that of
the intersection argument in arXiv:2011.12127, lines 2087--2094. -/
theorem CPSVCanonicalFormData.exists_positive_wordTupleSpanTop_succ_le_three_bondDim_pow_five
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) :
    ∃ S : ℕ, 0 < S ∧ S + 1 ≤ 3 * D ^ 5 ∧
      WordTupleSpanTop (fun j ↦ data.blocks (data.representativeIndex j)) S := by
  exact IsCPSVBasisOfNormalTensors.exists_positive_wordTupleSpanTop_succ_le_three_cap_pow_five
    (NeZero.pos D) data.sum_representative_dim_le data.bntRefinement.representativesBNT

variable [NeZero d]

/-- Every canonical parent interaction of range \(L\geq 3D^5\) has
precisely the periodic BNT span as its kernel on every ring \(N\geq L\).
This includes \(N=L=3D^5\). Source: arXiv:1606.00608, lines 317--345,
and arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem CPSVCanonicalFormData.ker_parentHamiltonian_eq_of_three_bondDim_pow_five_le
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) {L N : ℕ}
    (hL : 3 * D ^ 5 ≤ L) (hLN : L ≤ N) :
    LinearMap.ker (parentHamiltonian A L N) =
      bntMPSVectorSpan (fun j ↦ data.blocks (data.representativeIndex j)) N := by
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    data.exists_positive_wordTupleSpanTop_succ_le_three_bondDim_pow_five
  exact data.ker_parentHamiltonian_eq_of_wordTupleSpanTop hS hSpan (hBound.trans hL) hLN

/-- A canonical tensor admits a basis of normal tensors and a positive
interaction range \(R\leq 3D^5\) such that, at every larger range
\(R\leq L\leq N\), every collection of positive local parent terms has
exactly the periodic BNT span as its kernel. In particular, the minimal
ring \(N=L=R\) is included.

This combines the blocking estimate of arXiv:1606.00608, lines 317--345,
with the block-injective ground-space theorem of arXiv:2011.12127,
Section IV.C, lines 2114--2129. -/
theorem IsCPSVCanonicalForm.exists_bnt_ker_sum_eq_of_bounded_range
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (B : (j : Fin g) → MPSTensor d (dim j)) (R : ℕ),
      IsCPSVBasisOfNormalTensors A (fun j ↦ ⟨dim j, B j⟩) ∧
      0 < R ∧ R ≤ 3 * D ^ 5 ∧
      ∀ {L N : ℕ}, R ≤ L → L ≤ N →
        ∀ H : Fin N → EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N),
          (∀ i, (H i).IsPositive) →
          (∀ i, LinearMap.ker (H i) = LinearMap.ker (localTermES A L i)) →
          LinearMap.ker (∑ i, H i) = (bntMPSVectorSpan B N).map
            (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap := by
  let data := Classical.choice hA
  obtain ⟨S, hS, hBound, hSpan⟩ :=
    data.exists_positive_wordTupleSpanTop_succ_le_three_bondDim_pow_five
  refine ⟨data.phaseClasses.g, (fun j ↦ data.dim (data.representativeIndex j)),
    (fun j ↦ data.blocks (data.representativeIndex j)), S + 1,
    data.bntRefinement.representativesBNT, by omega, hBound, ?_⟩
  exact fun {_L _N} hL hLN H hH hker ↦
    data.ker_sum_eq_of_wordTupleSpanTop hS hSpan hL hLN H hH hker

end MPSTensor
