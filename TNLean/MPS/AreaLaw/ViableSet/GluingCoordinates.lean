/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Gluing
import TNLean.MPS.AreaLaw.ViableSet.Basic

/-!
# Left-block coordinates for gluing

The three-way cut separates the first `k - 1` sites from the intervening site when present.
Joining these two regions identifies their coordinates with configurations of the first `k`
sites. This identification preserves the norm, transports the projection onto a prescribed
left subspace, and commutes with every linear extension on the right bond.

These coordinate identities support the extraction of the left columns of the vector chosen
by the size-trimming program of Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`References/1307.5143/algo53.tex`, lines 472–478, and Lemma `l:leading`, lines 493–505.
They hold for all natural cut positions, with each left block intersected with the chain.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw

variable {L q k m : ℕ}

/-- At most one site lies between consecutive clipped left blocks, so its configurations
have dimension at most `q` when `1 ≤ q`. This includes the endpoint cuts used with the
boundary net of arXiv:1307.5143v1, `algo53.tex`, lines 456–464. -/
theorem card_cutSite_le (hq : 1 ≤ q) : Fintype.card (CutSite L q k) ≤ q := by
  classical
  have hc : (leftBlock L k \ leftBlock L (k - 1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_sdiff, mem_leftBlock, Fin.ext_iff] at *
    omega
  simpa only [CutSite, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, pow_one] using
    pow_le_pow_right' hq hc

/-- Joining the two left regions of the gluing cut, leaving the bond coordinate unchanged.
This is the coordinate identification for the vectors in arXiv:1307.5143v1, `algo53.tex`,
lines 477–478 and 493–505. -/
noncomputable def gluingLeftCoordinates (L q k m : ℕ) :
    EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
      (leftBlock_mono (Nat.sub_le k 1))).symm.prodCongr (Equiv.refl _))

/-- Extending the right bond in three-way coordinates agrees with the extension after joining
the left regions. This identifies the vector of Lemma `l:leading` with its left-block columns
(arXiv:1307.5143v1, `algo53.tex`, lines 477–478 and 493–505); the right matrix is arbitrary. -/
theorem gluingLeftCoordinates_rightApply
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k) =
      WithLp.toLp 2 (fun z ↦ rightApply W (gluingLeftCoordinates L q k m u)
        (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z)) := by
  classical
  ext z
  change (((1 : Matrix (CutLeft L q k × CutSite L q k)
      (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) (gluingCut L q k z) =
    schmidtCoeffMatrix (WithLp.ofLp (rightApply W (gluingLeftCoordinates L q k m u)))
      (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z).1
      (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z).2
  rw [schmidtCoeffMatrix_ofLp_rightApply]
  simp [gluingCut, Entropy.threeCutEquiv_eq_trans, gluingLeftCoordinates,
    mulVec, dotProduct, Fintype.sum_prod_type, one_apply, mul_apply, mul_comm]

/-- Being fixed by the projection onto a prescribed left span is unchanged by joining the
two left regions. This is the support condition in the size-trimming program
(arXiv:1307.5143v1, `algo53.tex`, lines 472–476). -/
theorem gluingLeftCoordinates_spanProjection_eq_iff (S : Set (LeftBlockVector L q k))
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    (reindex (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
          (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
          (leftBlock_mono (Nat.sub_le k 1))) (spanProjection S) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ↔
      (spanProjection S ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ
          WithLp.ofLp (gluingLeftCoordinates L q k m u) =
        WithLp.ofLp (gluingLeftCoordinates L q k m u) := by
  classical
  rw [kroneckerMap_reindex_left, reindex_apply, submatrix_mulVec_equiv]
  exact Equiv.comp_symm_eq _ _ _

end TNLean.MPS.AreaLaw
