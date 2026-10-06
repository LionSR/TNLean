/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualWindowRightSectorSum
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryCoordinates

/-!
# The joint right residual window is the terminal ground space

In the physical triple coordinates, each right residual window is the finite
direct sum of its residual boundary map over the free blocked prefix.
A virtual resolution and its blocked cointertwining therefore identify the
sum of the right sector ranges with the original terminal boundary space,
transported by the physical configuration isometry.

The configuration bijection has target `K * L + M * L + r`, matching the
original covering intervals. It is the full-window bijection followed by
the arithmetic identification `(K + M) * L = K * L + M * L`.
The range theorem includes zero lengths and requires neither primitivity,
isometric virtual embeddings, nor injectivity.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (i), lines 2442--2531; DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D L : ℕ}

/-- Decode the three physical configuration blocks into the original cover
length `K * L + M * L + r`. Source: the grouping in Nachtergaele,
arXiv:cond-mat/9410110, Section 6, and DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451. -/
noncomputable def residualCoverConfigEquiv (d L K M r : ℕ) :
    Cfg (blockPhysDim d L) K × (Cfg (blockPhysDim d L) M × Cfg d r) ≃
      Cfg d (K * L + M * L + r) :=
  (residualWindowConfigEquiv d L K M r).trans
    (Equiv.arrowCongr (finCongr (by rw [Nat.add_mul])) (Equiv.refl (Fin d)))

/-- The cover configuration consists of the decoded prefix, decoded middle,
and original tail, in that order. This includes zero lengths.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451. -/
theorem residualCoverConfigEquiv_apply (K M r : ℕ)
    (u : Cfg (blockPhysDim d L) K) (v : Cfg (blockPhysDim d L) M) (τ : Cfg d r) :
    residualCoverConfigEquiv d L K M r (u, v, τ) =
      Fin.append (Fin.append (blockedConfigEquiv d K L u) (blockedConfigEquiv d M L v)) τ := by
  apply List.ofFn_injective
  have hCast := List.ofFn_congr
    (show (K + M) * L + r = K * L + M * L + r by rw [Nat.add_mul])
    (Fin.append (blockedConfigEquiv d (K + M) L (Fin.append u v)) τ)
  calc
    _ = List.ofFn (Fin.append (blockedConfigEquiv d (K + M) L (Fin.append u v)) τ) :=
      hCast.symm
    _ = _ := by
      simp only [List.ofFn_fin_append, ofFn_blockedConfigEquiv, flattenBlockedWord,
        Kraus.flattenBlockedWord, List.map_append, List.flatten_append]

/-- Physical reindexing writes the terminal boundary map as independent
ordinary boundary maps on its prefix fibers. -/
private theorem reindex_reassocTailBoundaryMapES_eq_fiberwise
    (A : MPSTensor d D) (K M r : ℕ) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (residualCoverConfigEquiv d L K M r).symm).toContinuousLinearMap.comp
        (reassocTailBoundaryMapES A (K * L) (M * L) r) =
    (EuclideanSpace.fiberwiseMap (Cfg (blockPhysDim d L) K)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (residualBoundaryConfigEquiv d L M r).symm).toContinuousLinearMap.comp
          (groundSpaceMapES A (M * L + r)))).comp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr (blockedConfigEquiv d K L)
          (Equiv.refl (Fin D × Fin D))).symm).toContinuousLinearMap := by
  ext x ⟨u, v, τ⟩
  change reassocTailBoundaryMapES A (K * L) (M * L) r x
      (residualCoverConfigEquiv d L K M r (u, v, τ)) =
    groundSpaceMapES A (M * L + r)
      (WithLp.toLp 2 (fun p => x (blockedConfigEquiv d K L u, p)))
      (Fin.append (blockedConfigEquiv d M L v) τ)
  rw [residualCoverConfigEquiv_apply, reassocTailBoundaryMapES_apply_threeBlock]
  rfl

/-- The sum of the right residual sector ranges is exactly the original
terminal boundary space in the common physical cover coordinates. Only the
virtual resolution and blocked cointertwining are required.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (i), lines 2442--2531; DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451. -/
theorem iSup_range_residualWindowRightMapES_eq_reindex_reassocTailBoundaryMapES
    {ι : Type*} [Fintype ι] {dim : ι → ℕ}
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ) (K M r : ℕ) :
    (⨆ j, (residualWindowRightMapES A (B j) (V j) K M r).range) =
      (reassocTailBoundaryMapES A (K * L) (M * L) r).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (residualCoverConfigEquiv d L K M r).symm).toLinearEquiv.toLinearMap := by
  simp_rw [residualWindowRightMapES_eq_fiberwise]
  rw [EuclideanSpace.iSup_range_fiberwiseMap_eq]
  have hJoint :
      (⨆ j, ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (residualBoundaryConfigEquiv d L M r).symm).toContinuousLinearMap.comp
          (blockedResidualBoundaryMapES A L (B j) (V j) M r)).range) =
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (residualBoundaryConfigEquiv d L M r).symm).toContinuousLinearMap.comp
          (groundSpaceMapES A (M * L + r))).range := by
    simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      ← Submodule.map_iSup]
    rw [← groundSpaceES_eq_iSup_range_blockedResidualBoundaryMapES A B V hSum hInt M r,
      range_groundSpaceMapES]
  rw [hJoint, ← EuclideanSpace.fiberwiseMap_range_starProjection,
    Submodule.range_starProjection]
  simpa only [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
    LinearMap.coe_toContinuousLinearMap, LinearEquiv.range, Submodule.map_top] using
    (congrArg (fun T => T.toLinearMap.range)
      (reindex_reassocTailBoundaryMapES_eq_fiberwise (L := L) A K M r)).symm

end MPSTensor
