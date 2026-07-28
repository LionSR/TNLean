/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTMarkovSectorProjectors
import TNLean.MPS.MPDO.BNTThreeSiteReducedClosure

/-!
# BNT sector projectors for the four-site SAL marginal

The normalized three-site marginal of a four-site tensor satisfying the strong
area law has two descriptions.  Its horizontal basis-of-normal-tensors
representation gives a family closure with nonzero closing matrices, while
equality in strong subadditivity gives a Hayashi--Markov decomposition.  A
simultaneous inverse for the normal tensors compares these descriptions and
assigns every positive-weight Markov sector to a unique normal sector.

The corresponding sums of Hayashi sector projections are orthogonal, mutually
disjoint, and resolve the positive-weight Markov support.  This is the
four-site specialization of the projector construction in arXiv:1606.00608,
Appendix C.2, equations `QkKjs` and `Pis`.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, lines 1666--1676 and 1714--1737.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Reindexing the four-site state's three-site marginal by the canonical
ordered-triple equivalence is the submatrix convention used by the
SAL-to-Hayashi theorem.

Source: arXiv:1606.00608, Appendix C.2, Lemma `Lsigma3`, lines 1351--1363. -/
theorem reducedBlockState_four_reindex_eq_submatrix (M : MPOTensor d D) :
    Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
        (_root_.finThreeArrowEquiv (Fin d))
        (M.reducedBlockState 4 3 (by omega)) =
      (M.reducedBlockState 4 3 (by omega)).submatrix
        (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2])
        (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2]) := by
  ext p q
  simp

/-- SAL supplies a Hayashi--Markov decomposition in the same ordered-triple
coordinates as the BNT family closure.

This statement uses the proved forward Hayashi equality characterization
`hayashi_ssa_equality_characterization_forward`.

Source: arXiv:1606.00608, Appendix C.2, Lemma `Lsigma3`, lines 1351--1363,
and the Case II use at lines 1698--1737. -/
theorem exists_etaStructure_reducedBlockState_four_reindex_of_isSAL
    (M : MPOTensor d D) (hSAL : IsSAL M) :
    Nonempty
      (EtaStructure
        (Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
          (_root_.finThreeArrowEquiv (Fin d))
          (M.reducedBlockState 4 3 (by omega)))) := by
  rw [reducedBlockState_four_reindex_eq_submatrix]
  exact exists_etaStructure_reducedBlockState_of_isSAL M hSAL

/-- For the normalized four-site SAL marginal, every positive-weight
Hayashi--Markov sector has a unique BNT label.  The resulting BNT-labelled
sums of Hayashi projections are orthogonal, mutually disjoint, and resolve the
positive-weight Markov support.

There is no independent nonzero-closing-matrix hypothesis: the normalized BNT
closure supplies it from SAL, copy independence, and nonnilpotence.

The Hayashi decomposition uses the proved forward
Hayashi--Ruskai--Hayden--Jozsa--Petz--Winter characterization of equality in
strong subadditivity, `hayashi_ssa_equality_characterization_forward`.

**Source hypothesis (biCF):** the one-letter simultaneous span is precisely
the block-injective canonical-form assumption imposed at the start of Case II
in arXiv:1606.00608, line 1628.  It supplies the simultaneous inverse used in
the source proof.  Its relation with finite physical blocking is recorded in
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1666--1676 and equations
`QkKjs` and `Pis`, lines 1714--1737. -/
theorem exists_bntSectorProjectors_four_of_sameMPV₂Pos_isSAL
    (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M) :
    let ρ := Matrix.reindex (_root_.finThreeArrowEquiv (Fin d))
      (_root_.finThreeArrowEquiv (Fin d))
      (M.reducedBlockState 4 3 (by omega))
    ∃ (C : Matrix (MPSTensor.BlockEntryIndex S.basisDim)
        (Fin d × Fin d) ℂ),
      ∃ hC : MPSTensor.IsMPOBlockLeftInverse
          (fun j ↦ S.basisMPOTensor j) C,
        ∃ hη : EtaStructure ρ,
          let hρ : IsThreeSiteFamilyClosure
              (fun j ↦ S.basisMPOTensor j)
              (S.normalizedThreeSiteClosingMatrix M 1) ρ :=
            (reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
              M S hM hWeight hnonNil hSAL).1
          let hR : ∀ j : Fin S.basisCount,
              S.normalizedThreeSiteClosingMatrix M 1 j ≠ 0 :=
            (reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
              M S hM hWeight hnonNil hSAL).2
          (∀ k : {k : Fin hη.m // hη.p k ≠ 0},
              ∃! s : Fin S.basisCount,
                BNTMarkovBlockNonzero (S.basisMPOTensor s) hη k) ∧
            (∀ s : Fin S.basisCount,
              IsOrthogonalProjection
                (bntSectorProjection hC hρ hη hR s)) ∧
            (∀ s t : Fin S.basisCount, s ≠ t →
              bntSectorProjection hC hρ hη hR s *
                bntSectorProjection hC hρ hη hR t = 0) ∧
            (∑ s : Fin S.basisCount,
              bntSectorProjection hC hρ hη hR s) =
                activeMarkovProjection hη := by
  dsimp only
  have hSpan' : MPSTensor.WordTupleSpanTop
      (fun j ↦ (S.basisMPOTensor j).toMPSTensor) 1 := by
    simpa using hSpan
  obtain ⟨C, hC⟩ := hSpan'.exists_mpo_block_left_inverse
  obtain ⟨hη⟩ :=
    exists_etaStructure_reducedBlockState_four_reindex_of_isSAL M hSAL
  let hClosure :=
    reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
      M S hM hWeight hnonNil hSAL
  let hρ := hClosure.1
  let hR := hClosure.2
  refine ⟨C, hC, hη, ?_, ?_, ?_, ?_⟩
  · intro k
    exact existsUnique_bntMarkovBlockNonzero_of_probability_ne_zero
      hC hρ hη hR k k.property
  · intro s
    exact bntSectorProjection_isOrthogonal hC hρ hη hR s
  · intro s t hst
    exact bntSectorProjection_mul_eq_zero hC hρ hη hR hst
  · exact sum_bntSectorProjection hC hρ hη hR

end MPOTensor
