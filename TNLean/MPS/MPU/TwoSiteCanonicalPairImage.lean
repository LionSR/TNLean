/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.StarSubalgebraEquiv
import TNLean.QCA.ConsecutivePairCoordinates
import TNLean.MPS.MPU.TwoSiteBlockedLocalAction
import TNLean.MPS.MPU.TwoSiteOutputSupport
import TNLean.QCA.GNVWIndex
import TNLean.QCA.SupportAlgebraReindex

/-!
# The actual canonical QCA pair image of supplied MPU gates

The computed finite two-link family is identified with the canonical
ordered even-pair image of the actually blocked automorphism. This is
an equality of actual images; no support-factor presentation is supplied.

Source: arXiv:1703.09188, Appendix, lines 2313–2334.

**Local fix (Appendix gate orientation):** The finite factor uses the
actual forward direction of v stated in the main text. Its matrix size
and positive rational index are unchanged by correcting the printed
adjoint order; see `docs/paper-gaps/mpu_qca_index_normalization.tex`.
-/

open scoped Matrix

namespace SpinChain

private def leftPairZeroConfigEquiv (b : ℕ) :
    (Fin b × Fin b) ≃ Config b (leftPair 0) := consecutivePairConfigEquiv b (-1)

private def rightPairZeroConfigEquiv (b : ℕ) :
    (Fin b × Fin b) ≃ Config b (rightPair 0) := consecutivePairConfigEquiv b 1

private theorem intervalZeroPairRegion : finiteChainRegion 0 2 = evenPair 0 := by
  ext z
  simp only [finiteChainRegion, Finset.mem_Ico, evenPair, Finset.mem_insert,
    Finset.mem_singleton]
  omega

private theorem intervalFourSubsetPairUnion :
    finiteChainRegion (-1) 4 ⊆ leftPair 0 ∪ rightPair 0 := by
  intro z hz
  simp only [finiteChainRegion, Finset.mem_Ico] at hz
  simp only [leftPair, rightPair, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem pairUnionSubsetIntervalFour :
    leftPair 0 ∪ rightPair 0 ⊆ finiteChainRegion (-1) 4 := by
  intro z hz
  simp only [leftPair, rightPair, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hz
  simp only [finiteChainRegion, Finset.mem_Ico]
  omega

private theorem actualFourOutputConfig (b : ℕ)
    (x : Config b (leftPair 0) × Config b (rightPair 0)) :
    (finiteChainConfigEquiv b 4 (-1)).symm
      (Config.restrict intervalFourSubsetPairUnion
        ((Config.disjointUnionEquiv (disjoint_leftPair_rightPair 0)).symm x)) =
      MPOTensor.originalSiteHeisenbergOutputBlockEquiv b
        (((leftPairZeroConfigEquiv b).prodCongr (rightPairZeroConfigEquiv b)).symm x) := by
  funext i
  fin_cases i <;> rfl

private theorem bipartite_output_eq_interval (b : ℕ) [NeZero b]
    (A : Matrix ((Fin b × Fin b) × (Fin b × Fin b))
      ((Fin b × Fin b) × (Fin b × Fin b)) ℂ) :
    bipartiteMatrixToQuasiLocalObservable (disjoint_leftPair_rightPair 0)
      (Matrix.reindex ((leftPairZeroConfigEquiv b).prodCongr (rightPairZeroConfigEquiv b))
        ((leftPairZeroConfigEquiv b).prodCongr (rightPairZeroConfigEquiv b)) A) =
      quasiLocalIntervalObservable b (-1) 4
        (Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputBlockEquiv b)
          (MPOTensor.originalSiteHeisenbergOutputBlockEquiv b) A) := by
  classical
  rw [quasiLocalIntervalObservable_apply,
    ← quasiLocalObservable_localInclusion b intervalFourSubsetPairUnion]
  change quasiLocalObservable b (leftPair 0 ∪ rightPair 0) _ = _
  apply congrArg (quasiLocalObservable b (leftPair 0 ∪ rightPair 0))
  apply (bipartiteLocalAlgebraEquiv (disjoint_leftPair_rightPair 0)).injective
  rw [StarAlgEquiv.apply_symm_apply]
  ext row col
  have hcomp :
      (Config.splitEquiv intervalFourSubsetPairUnion
        ((Config.disjointUnionEquiv (disjoint_leftPair_rightPair 0)).symm row)).2 =
      (Config.splitEquiv intervalFourSubsetPairUnion
        ((Config.disjointUnionEquiv (disjoint_leftPair_rightPair 0)).symm col)).2 := by
    funext z
    exact ((Finset.mem_sdiff.mp z.property).2
      (pairUnionSubsetIntervalFour (Finset.mem_sdiff.mp z.property).1)).elim
  simp only [bipartiteLocalAlgebraEquiv_apply, localInclusion_apply, hcomp, ite_true, mul_one]
  change A _ _ = A
    ((MPOTensor.originalSiteHeisenbergOutputBlockEquiv b).symm
      ((finiteChainConfigEquiv b 4 (-1)).symm _))
    ((MPOTensor.originalSiteHeisenbergOutputBlockEquiv b).symm
      ((finiteChainConfigEquiv b 4 (-1)).symm _))
  rw [actualFourOutputConfig, actualFourOutputConfig,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
  (hU : U.IsMPU) (k : ℕ) (hk : 0 < k) [NeZero k]
  {u : Matrix (Fin ℓ × Fin r)
    (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
  {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (Fin r × Fin ℓ) ℂ}
  (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)

private theorem actual_evenPairLocalImage_zero :
    PropagatesWithin.evenPairLocalImage
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) 0 =
      (MPOTensor.twoLinkOutputMap u v S.u_unitary S.v_unitary).range.map
        (Matrix.matrixReindexStarAlgEquiv
          ((leftPairZeroConfigEquiv (MPSTensor.blockPhysDim d k)).prodCongr
            (rightPairZeroConfigEquiv (MPSTensor.blockPhysDim d k)))).toStarAlgHom := by
  classical
  let b := MPSTensor.blockPhysDim d k
  let ω := blockedAutomorphism d k (bufferedMPUQuasiLocalAut hU k hk S)
  let E₂ := (finTwoArrowEquiv (Fin b)).symm
  let F := (quasiLocalIntervalObservable b 0 2).comp
    (Matrix.matrixReindexStarAlgEquiv E₂).toStarAlgHom
  let E := (leftPairZeroConfigEquiv b).prodCongr (rightPairZeroConfigEquiv b)
  let Φ := MPOTensor.twoLinkOutputMap u v S.u_unitary S.v_unitary
  have hInputRange : F.range = (quasiLocalObservable b (evenPair 0)).range := by
    have hRaw : F.range = (quasiLocalObservable b (finiteChainRegion 0 2)).range := by
      ext z
      constructor
      · rintro ⟨A, rfl⟩
        exact ⟨(intervalCoordinates b 0 2).symm (Matrix.reindex E₂ E₂ A), rfl⟩
      · rintro ⟨B, rfl⟩
        refine ⟨(Matrix.matrixReindexStarAlgEquiv E₂).symm
          (intervalCoordinates b 0 2 B), ?_⟩
        change quasiLocalIntervalObservable b 0 2
          ((Matrix.matrixReindexStarAlgEquiv E₂)
            ((Matrix.matrixReindexStarAlgEquiv E₂).symm (intervalCoordinates b 0 2 B))) = _
        rw [StarAlgEquiv.apply_symm_apply, quasiLocalIntervalObservable_apply,
          StarAlgEquiv.symm_apply_apply]
    simpa only [intervalZeroPairRegion] using hRaw
  have hAction (A : Matrix (Fin b × Fin b) (Fin b × Fin b) ℂ) :
      ω (F A) = bipartiteMatrixToQuasiLocalObservable (disjoint_leftPair_rightPair 0)
        (Matrix.reindex E E (Φ A)) := by
    change ω (quasiLocalIntervalObservable b 0 2 (Matrix.reindex E₂ E₂ A)) = _
    rw [blocked_bufferedMPUQuasiLocalAut_pair_interval hU k hk S 0 A]
    change quasiLocalIntervalObservable b (-1) 4
      (Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputBlockEquiv b)
        (MPOTensor.originalSiteHeisenbergOutputBlockEquiv b)
        (MPOTensor.twoLinkOutputObservable u v A)) = _
    rw [MPOTensor.twoLinkOutputMap_apply]
    exact (bipartite_output_eq_interval b (MPOTensor.twoLinkOutputObservable u v A)).symm
  apply StarSubalgebra.map_injective
    (bipartiteMatrixToQuasiLocalObservable_injective (disjoint_leftPair_rightPair 0))
  rw [PropagatesWithin.evenPairLocalImage_map_bipartiteMatrixToQuasiLocalObservable]
  ext z
  constructor
  · rintro ⟨B, rfl⟩
    have hmem : quasiLocalObservable b (evenPair 0) B ∈ F.range := by
      rw [hInputRange]
      exact ⟨B, rfl⟩
    obtain ⟨A, hA⟩ := hmem
    refine ⟨Matrix.reindex E E (Φ A), ⟨Φ A, ⟨A, rfl⟩, rfl⟩, ?_⟩
    exact (hAction A).symm.trans (congrArg ω hA)
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨Z, hZ, rfl⟩ := hY
    obtain ⟨A, rfl⟩ := hZ
    have hmem : F A ∈ (quasiLocalObservable b (evenPair 0)).range := by
      rw [← hInputRange]
      exact ⟨A, rfl⟩
    obtain ⟨B, hB⟩ := hmem
    exact ⟨B, (congrArg ω hB).trans (hAction A)⟩

/-- The actual canonical even support factor of the blocked MPU action
has its derived ℓ-dimensional full-matrix presentation. Neither a
support-factor presentation nor a rank identity is supplied as a premise.
Source: arXiv:1703.09188, Appendix, lines 2322–2334. -/
noncomputable def blocked_bufferedMPUQuasiLocalAut_evenSupportEquiv_zero :
    ↥(PropagatesWithin.evenSupportAlgebra
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) 0) ≃⋆ₐ[ℂ]
      Matrix (Fin ℓ) (Fin ℓ) ℂ := by
  change ↥(Matrix.leftSupportAlgebra
    (PropagatesWithin.evenPairLocalImage
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) 0)) ≃⋆ₐ[ℂ] _
  rw [actual_evenPairLocalImage_zero hU k hk S,
    Matrix.leftSupportAlgebra_map_matrixReindexStarAlgEquiv]
  exact (StarSubalgebra.equivMapOfInjective _
    (Matrix.matrixReindexStarAlgEquiv (leftPairZeroConfigEquiv _)).toStarAlgHom
    (Matrix.matrixReindexStarAlgEquiv (leftPairZeroConfigEquiv _)).injective).symm.trans
      (MPOTensor.twoLinkLeftSupportEquiv u v S.u_unitary S.v_unitary S.phys_pos S.right_pos)

/-- The actual support matrix size at the fixed even cut is ℓ.
Source: arXiv:1703.09188, Appendix, line 2333. -/
theorem blocked_bufferedMPUQuasiLocalAut_supportAlgebraMatrixSize_zero :
    PropagatesWithin.supportAlgebraMatrixSize
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) 0 = ℓ := by
  simpa only [mul_zero] using
    PropagatesWithin.supportAlgebraMatrixSize_even_eq_of_equiv
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) 0
      (blocked_bufferedMPUQuasiLocalAut_evenSupportEquiv_zero hU k hk S)

/-- The positive rational GNVW index of the actually blocked MPU action
is ℓ/d^k. This uses the actual finite pair image and its derived least
support algebra, not an assumed support presentation.
Source: arXiv:1703.09188, Appendix eq:original-index, lines 2329–2334. -/
theorem coe_gnvwIndex_blocked_bufferedMPUQuasiLocalAut :
    (PropagatesWithin.gnvwIndex
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) : ℚ) =
        (ℓ : ℚ) / (MPSTensor.blockPhysDim d k : ℚ) :=
  PropagatesWithin.coe_gnvwIndex_eq_of_evenSupportAlgebra_equiv
    (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) 0
    (blocked_bufferedMPUQuasiLocalAut_evenSupportEquiv_zero hU k hk S)

/-- The same actual positive rational index is d^k/r, by the dimension
identity of the supplied unitary gate. Source: arXiv:1703.09188,
Definition def:index and Appendix, lines 681–688 and 2329–2334. -/
theorem coe_gnvwIndex_blocked_bufferedMPUQuasiLocalAut_eq_phys_div_right :
    (PropagatesWithin.gnvwIndex
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S) : ℚ) =
        (MPSTensor.blockPhysDim d k : ℚ) / (r : ℚ) := by
  rw [coe_gnvwIndex_blocked_bufferedMPUQuasiLocalAut hU k hk S]
  exact S.left_div_phys_eq_phys_div_right

end SpinChain
