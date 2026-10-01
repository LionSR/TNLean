/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.PhaseClasses
import TNLean.MPS.Periodic.EqualCaseGlobal

/-!
# Unitary assembly of periodic phase classes

Group a weighted family of left-canonical periodic blocks into a non-repeated
basis, retaining the original copy indices. The phases in the blockwise
unitary identifications are absorbed into the corresponding weights, so every
weight modulus and the total bond dimension are preserved.

The resulting sector decomposition is related to the original block sum by a
single unitary similarity. This is the grouping in arXiv:1708.00029,
`eq:bdnr`, lines 286–305, in the trace-preserving gauge of line 625.
-/

open scoped BigOperators Matrix
namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}
variable {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- Group the original weights by phase class, absorbing a chosen unit phase
into each copy. This is the multiplicity formula of arXiv:1708.00029,
`eq:bdnr`, lines 286–305. The matching phases are supplied by
`MPVPhaseClassData.exists_unitary_sectorDecomposition`. -/
def MPVPhaseClassData.toSectorDecomposition (classes : MPVPhaseClassData blocks)
    (μ : Fin r → ℂ) (ξ : (j : Fin classes.g) → Fin (classes.copies j) → ℂ)
    (hμ : ∀ k, μ k ≠ 0) (hξ : ∀ j q, ‖ξ j q‖ = 1) : SectorDecomposition d where
  basisCount := classes.g
  basisDim := fun j ↦ dim (classes.repr j)
  basis := fun j ↦ blocks (classes.repr j)
  sectors := {
    copies := classes.copies
    copies_pos := classes.copies_pos
    weight := fun j q ↦ μ (classes.enum j q) * ξ j q
    weight_ne_zero := fun j q ↦ mul_ne_zero (hμ _) (Complex.ne_zero_of_norm_eq_one (hξ j q)) }

/-- A weighted periodic block family admits a non-repeated sector decomposition
with the same weight moduli and total dimension, related by a unitary similarity.
Each grouped copy remains identified with `classes.enum j q` in the original
family. This realizes arXiv:1708.00029, `eq:bdnr`, lines 286–305, with the
unitary gauge specified after `thm:bd`, line 625. -/
theorem MPVPhaseClassData.exists_unitary_sectorDecomposition
    (classes : MPVPhaseClassData blocks) (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (period : Fin r → ℕ) (hper : ∀ k, IsPeriodic (period k) (blocks k)) :
    ∃ (ξ : (j : Fin classes.g) → Fin (classes.copies j) → ℂ) (hξ : ∀ j q, ‖ξ j q‖ = 1),
      let P := classes.toSectorDecomposition μ ξ hμ hξ
      P.totalDim = ∑ k, dim k ∧
      (∀ j : Fin classes.g, IsPeriodic (period (classes.repr j)) (P.basis j)) ∧
      (∀ i j : Fin classes.g, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j)) ∧
      (∀ (j : Fin classes.g) (q : Fin (classes.copies j)),
        ‖P.weight j q‖ = ‖μ (classes.enum j q)‖) ∧
      SameMPV₂Pos (toTensorFromBlocks μ blocks) P.toTensor ∧
      ∃ Y : Matrix (Fin (∑ k, dim k)) (Fin P.totalDim) ℂ,
        Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
        ∀ i, toTensorFromBlocks μ blocks i = Y * P.toTensor i * Yᴴ := by
  classical
  choose hd ξ U hξ hrel using fun j q ↦ (classes.periodic_unitary_match period hper j q).2
  let P := classes.toSectorDecomposition μ ξ hμ hξ
  let f : Fin P.totalCopies ≃ Fin r := P.flatIndexEquiv.symm.trans classes.enumEquiv
  have hdim (t : Fin P.totalCopies) : dim (f t) = P.flatDim t :=
    hd (P.flatIndexEquiv.symm t).1 (P.flatIndexEquiv.symm t).2
  let V : (t : Fin P.totalCopies) → Matrix.unitaryGroup (Fin (P.flatDim t)) ℂ :=
    fun t ↦ U (P.flatIndexEquiv.symm t).1 (P.flatIndexEquiv.symm t).2
  have hflat (t : Fin P.totalCopies) (i : Fin d) :
      Matrix.reindex (finCongr (hdim t)) (finCongr (hdim t)) (μ (f t) • blocks (f t) i) =
        P.flatWeight t • ((V t : Matrix _ _ ℂ) * P.flatBasis t i * (V t : Matrix _ _ ℂ)ᴴ) := by
    have hs : Matrix.reindex (finCongr (hdim t)) (finCongr (hdim t))
        (μ (f t) • blocks (f t) i) =
        μ (f t) • Matrix.reindex (finCongr (hdim t)) (finCongr (hdim t)) (blocks (f t) i) := rfl
    rw [hs, reindex_finCongr_apply_eq_cast]
    let jq : (j : Fin classes.g) × Fin (classes.copies j) := P.flatIndexEquiv.symm t
    change μ (classes.enum jq.1 jq.2) •
      (cast (congr_arg (MPSTensor d) (hd jq.1 jq.2)) (blocks (classes.enum jq.1 jq.2))) i =
      (μ (classes.enum jq.1 jq.2) * ξ jq.1 jq.2) •
        ((U jq.1 jq.2 : Matrix _ _ ℂ) * blocks (classes.repr jq.1) i *
          (U jq.1 jq.2 : Matrix _ _ ℂ)ᴴ)
    rw [hrel, smul_smul]
  have hd' (k : Fin r) : dim k = P.flatDim (f.symm k) := by
    simpa only [f.apply_symm_apply] using hdim (f.symm k)
  have hmatched (k : Fin r) (i : Fin d) :
      Matrix.reindex (finCongr (hd' k)) (finCongr (hd' k)) (μ k • blocks k i) =
        P.flatWeight (f.symm k) •
          ((unitaryGL (V (f.symm k)) : Matrix _ _ ℂ) * P.flatBasis (f.symm k) i *
            (((unitaryGL (V (f.symm k)))⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) := by
    have he (k' : Fin r) (hk : k' = k) (hdk : dim k' = P.flatDim (f.symm k)) :
        Matrix.reindex (finCongr hdk) (finCongr hdk) (μ k' • blocks k' i) =
          Matrix.reindex (finCongr (hd' k)) (finCongr (hd' k)) (μ k • blocks k i) := by
      subst k'
      rfl
    have ht := hflat (f.symm k) i
    rw [he _ (f.apply_symm_apply k)] at ht
    simpa only [unitaryGL_val, unitaryGL_inv_val] using ht
  obtain ⟨Y, Y', hYY', hY'Y, hunit, hconj⟩ :=
    toTensorFromBlocks_conj_of_matched_blocks μ blocks P.flatWeight P.flatBasis
      f.symm hd' (fun t ↦ unitaryGL (V t)) hmatched
  have hAdj := hunit (fun t ↦ (V t).property)
  refine ⟨ξ, hξ, ?_, ?_, ?_, ?_, ?_, Y, ?_, ?_, ?_⟩
  · exact Fintype.sum_equiv f P.flatDim dim (fun t ↦ (hdim t).symm)
  · exact fun j ↦ hper (classes.repr j)
  · exact classes.not_hetRepeatedBlocks
  · intro j q
    change ‖μ (classes.enum j q) * ξ j q‖ = _
    rw [norm_mul, hξ, mul_one]
  · apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Yᴴ
    · simpa only [Matrix.conjTranspose_conjTranspose, hAdj] using hY'Y
    · intro i
      change _ = (Yᴴ)ᴴ * P.toTensor i * Yᴴ
      rw [Matrix.conjTranspose_conjTranspose, P.toTensor_eq_toTensorFromBlocks_flat]
      simpa only [hAdj] using hconj i
  · simpa only [hAdj] using hYY'
  · simpa only [hAdj] using hY'Y
  · intro i
    change _ = Y * P.toTensor i * Yᴴ
    rw [P.toTensor_eq_toTensorFromBlocks_flat]
    simpa only [hAdj] using hconj i

/-- If a weighted sum of left-canonical periodic blocks has the same positive-length
vectors as a non-repeated periodic decomposition with unit-modulus weights, all
original weights have modulus one. Grouping repeated blocks is constructed here,
not assumed as extra input.

This is the multiplicity normalization step for the corrected forward direction
of arXiv:1708.00029, Theorem 4.1, lines 743–756.

**Scope restriction (unit-modulus target weights):** the premise `hQweight` is the
trace-preservation correction to the forward direction of Theorem 4.1, which is
false as printed without it; see
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem weight_norm_eq_one_of_block_sum_sameMPV₂Pos (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (period : Fin r → ℕ) (hper : ∀ k, IsPeriodic (period k) (blocks k))
    (Q : SectorDecomposition d) (periodQ : Fin Q.basisCount → ℕ)
    (hPerQ : ∀ j, IsPeriodic (periodQ j) (Q.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos (toTensorFromBlocks μ blocks) Q.toTensor)
    (hQweight : ∀ j q, ‖Q.weight j q‖ = 1) : ∀ k, ‖μ k‖ = 1 := by
  let classes := mpvPhaseClassData blocks
  obtain ⟨ξ, hξ, _, hP, hNonRepP, hweight, hgroup, _⟩ :=
    classes.exists_unitary_sectorDecomposition μ hμ period hper
  let P := classes.toSectorDecomposition μ ξ hμ hξ
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor := by
    intro N hN σ
    exact (hgroup N hN σ).symm.trans (hSame N hN σ)
  have hnorm := weight_norm_eq_one_of_sameMPV₂Pos P Q
    (fun j ↦ period (classes.repr j)) periodQ hP hPerQ hNonRepP hNonRepQ hPQ hQweight
  intro k
  obtain ⟨j, q, rfl⟩ := classes.exists_enum_eq k
  exact (hweight j q).symm.trans (hnorm j q)

end MPSTensor
