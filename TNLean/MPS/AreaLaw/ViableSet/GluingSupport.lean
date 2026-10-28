/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic
import TNLean.MPS.AreaLaw.ViableSet.Gluing
import QICLean.Channel.TrimmingEnergy

/-!
# Left support in three-way cut coordinates

A vector fixed by the left support projection in the three-way cut coordinates belongs to
the corresponding left-supported subspace when read on the chain. This is an auxiliary
coordinate statement for LVV13, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`,
lines 493–505.
-/

open Matrix
open scoped InnerProductSpace Kronecker

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- The left support condition of LVV13, `algo53.tex`, lines 493–505, read from the
three-way cut coordinates back on the chain. -/
theorem mem_leftSupportSubmodule_of_gluingCut_fixed
    (S : Set (LeftBlockVector L q k))
    (y : (CutLeft L q k × CutSite L q k) × CutRight L q k → ℂ)
    (hy : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ)) *ᵥ y = y) :
    WithLp.toLp 2 (y ∘ gluingCut L q k) ∈ leftSupportSubmodule S := by
  classical
  let e := Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (L := L) (Nat.sub_le k 1))
  let P := reindex e e (spanProjection S)
  let Y := Matrix.schmidtCoeffMatrix y
  have hleft : leftApply P (WithLp.toLp 2 y) = WithLp.toLp 2 y := by
    rw [← toEuclideanLin_kronecker_one_apply]
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp] using hy
  have hPY : P * Y = Y := by
    have h := congrArg (fun z ↦ schmidtCoeffMatrix (WithLp.ofLp z)) hleft
    simpa only [schmidtCoeffMatrix_ofLp_leftApply] using h
  have hcm : cutMatrix (WithLp.toLp 2 (y ∘ gluingCut L q k)) k = Y.submatrix e id := by
    ext p r
    rw [cutMatrix, Matrix.schmidtCoeffMatrix_apply]
    change y (gluingCut L q k ((Entropy.cutEquiv (fun _ : Fin L ↦ q)
      (leftBlock L k)).symm (p, r))) = y (e p, r)
    rw [gluingCut, Entropy.threeCutEquiv_eq_trans]
    simp [e]
  apply (spanProjection_mul_cutMatrix_eq_iff (S := S)).mp
  rw [hcm]
  have hP : P.submatrix e e = spanProjection S := by
    ext a b
    simp [P]
  have h := congrArg (fun M ↦ M.submatrix e id) hPY
  rw [← Matrix.submatrix_mul_equiv P Y e e id, hP] at h
  exact h

end TNLean.MPS.AreaLaw
