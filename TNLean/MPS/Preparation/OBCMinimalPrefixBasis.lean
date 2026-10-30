/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCPrefixFactors

/-!
# Actual prefix bases of a prescribed minimal OBC representation

At a minimal bond, the actual physical prefix columns of a supplied OBC
representation are a basis of the physical cut column space. The rank
and column-space equalities follow from the actual prefix-suffix
factorization. Between two such cuts, physical coordinate slicing has
exactly the original supplied site matrix. No comparison gauge or local
matrix identity is supplied.

Source: PGVWC07, arXiv:quant-ph/0608197, the minimal Schmidt bonds in
Theorem thm:OBC-Vidal, lines 444--458, and the prescribed OBC window in
Theorem 8, lines 1139--1169.
-/

open Matrix MPSPreparation
open scoped BigOperators

namespace OBCChainTensor

variable {d Q N : ℕ} (B : OBCChainTensor d Q N)

/-- The actual prefix factor of a minimal bond has independent columns.
Source: PGVWC07, minimal Schmidt ranks, MPSarchive.tex lines 444--458. -/
theorem linearIndependent_physicalPrefixMatrix (k : Fin (N + 1))
    (hmin : B.bondDim k = cutCoefficientRank B.coeff k.val) :
    LinearIndependent ℂ (physicalPrefixMatrix B k).col := by
  classical
  have hrank : (physicalPrefixMatrix B k).rank = B.bondDim k := by
    apply le_antisymm
    · simpa only [Fintype.card_fin] using
        Matrix.rank_le_card_width (physicalPrefixMatrix B k)
    · rw [hmin]
      change (cutCoefficientMatrix B.coeff k.val).rank ≤ _
      rw [cutCoefficientMatrix_eq_physicalPrefix_mul_suffix B k]
      exact Matrix.rank_mul_le_left _ _
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols, hrank, Fintype.card_fin]

/-- Minimality forces equality between the prescribed physical prefix
range and the actual cut column space, not only their inclusion.
Source: PGVWC07, MPSarchive.tex lines 444--458 and 1139--1169. -/
theorem cutColumnSpace_eq_span_physicalPrefixMatrix (k : Fin (N + 1))
    (hmin : B.bondDim k = cutCoefficientRank B.coeff k.val) :
    cutColumnSpace B.coeff k.val =
      Submodule.span ℂ (Set.range (physicalPrefixMatrix B k).col) := by
  classical
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← Matrix.range_mulVecLin]
    exact cutColumnSpace_le_range_physicalPrefixMatrix B k
  · have hcard : Fintype.card (Fin (B.bondDim k)) =
        Module.finrank ℂ (Submodule.span ℂ (Set.range (physicalPrefixMatrix B k).col)) := by
      simpa only [Set.finrank] using linearIndependent_iff_card_eq_finrank_span.mp
        (linearIndependent_physicalPrefixMatrix B k hmin)
    rw [finrank_cutColumnSpace, ← hcard, Fintype.card_fin, hmin]

/-- The original physical prefix columns give a basis at every minimal
bond of the prescribed OBC representation. Source: PGVWC07, actual
Schmidt cut bases, MPSarchive.tex lines 444--458. -/
noncomputable def physicalPrefixBasis (k : Fin (N + 1))
    (hmin : B.bondDim k = cutCoefficientRank B.coeff k.val) :
    Module.Basis (Fin (B.bondDim k)) ℂ (cutColumnSpace B.coeff k.val) :=
  (Module.Basis.span (linearIndependent_physicalPrefixMatrix B k hmin)).map
    (LinearEquiv.ofEq _ _ (cutColumnSpace_eq_span_physicalPrefixMatrix B k hmin).symm)

/-- The derived basis retains exactly the original supplied prefix
coefficients. Source: PGVWC07, MPSarchive.tex lines 444--458. -/
@[simp] theorem physicalPrefixBasis_apply (k : Fin (N + 1))
    (hmin : B.bondDim k = cutCoefficientRank B.coeff k.val)
    (a : Fin (B.bondDim k)) (u : CutPrefixConfig d N k.val) :
    (physicalPrefixBasis B k hmin a).val u = physicalPrefixMatrix B k u a := by
  simp only [physicalPrefixBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply]

/-- Between two minimal cuts, the original prescribed OBC site matrix
is the matrix of the actual physical-coordinate slice. This identifies
the given window rather than selecting a different representation.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
theorem toMatrix_cutSlice_physicalPrefixBasis (p : Fin N)
    (hprev : B.bondDim p.castSucc = cutCoefficientRank B.coeff p.val)
    (hnext : B.bondDim p.succ = cutCoefficientRank B.coeff (p.val + 1)) (i : Fin d) :
    LinearMap.toMatrix (physicalPrefixBasis B p.succ hnext)
      (physicalPrefixBasis B p.castSucc hprev) (cutSlice B.coeff p.val i) = B.tensor p i := by
  classical
  let C := physicalPrefixBasis B p.castSucc hprev
  let C' := physicalPrefixBasis B p.succ hnext
  have hslice (a : Fin (B.bondDim p.succ)) :
      cutSlice B.coeff p.val i (C' a) =
        ∑ b : Fin (B.bondDim p.castSucc), B.tensor p i b a • C b := by
    apply Subtype.ext
    funext u
    change (C' a).val (extendCutPrefix p.val u i) = _
    simp only [C', C, physicalPrefixBasis_apply, Submodule.coe_sum,
      Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [physicalPrefixMatrix_step]
    simp only [Matrix.mul_apply, mul_comm]
  ext b a
  change C.repr (cutSlice B.coeff p.val i (C' a)) b = _
  rw [hslice]
  simp

end OBCChainTensor
