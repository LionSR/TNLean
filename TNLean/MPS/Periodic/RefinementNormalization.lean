/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockDecomposition
import TNLean.MPS.Periodic.IrreducibleFormBlocking
import TNLean.MPS.Periodic.PhaseClassAssembly
import TNLean.MPS.Periodic.PrescribedBlocking

/-!
# Normalizing a tensor from a unit-weight blocked comparison

Start with the positive-weight periodic decomposition of an arbitrary tensor.
If a positive blocking has the same positive-length MPVs as a periodic sector
decomposition with unit-modulus multiplicities, the original block weights have
modulus one. The multiplicity-bearing equal-case fundamental theorem also
recovers the exact total bond dimension.

Absorbing the original weight phases into the blocks gives a unit-weight periodic
presentation without assuming an initial canonical form or empty-word equality.
This is the normalization step in arXiv:1708.00029, Theorem 4.1, lines 750–756.
The subsequent orbit-phase matching and root construction are separate steps.

**Scope restriction (positive lengths):**
`exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos` asserts equality
of MPVs only at positive lengths, since discarding zero blocks may lower the bond
dimension. The convention is inherited from `exists_periodic_blockDecomposition`
and recorded in `docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`.

**Scope restriction (unit-modulus target weights):** both blocked-comparison
theorems assume the target multiplicities have modulus one (`hQweight`). This is
the trace-preservation correction to the forward direction of Theorem 4.1, which
is false as printed without it; see
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

section Blocked

variable {r : ℕ} {dim : Fin r → ℕ}

private theorem sum_dim_eq_of_sameMPV₂Pos (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ) (hper : ∀ k, IsPeriodic (period k) (A k))
    (Q : SectorDecomposition d) (periodQ : Fin Q.basisCount → ℕ)
    (hPerQ : ∀ j, IsPeriodic (periodQ j) (Q.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos (toTensorFromBlocks μ A) Q.toTensor) :
    (∑ k, dim k) = Q.totalDim := by
  let classes := mpvPhaseClassData A
  obtain ⟨ξ, hξ, hdim, hP, hNonRepP, _, hgroup, _⟩ :=
    classes.exists_unitary_sectorDecomposition μ hμ period hper
  let P := classes.toSectorDecomposition μ ξ hμ hξ
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor := hgroup.symm.trans hSame
  obtain ⟨_, _, _, _, _, _, _, _, _, Y, Y', hYY', hY'Y, _⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition P Q
      (fun j ↦ period (classes.repr j)) periodQ hP hPerQ hNonRepP hNonRepQ hPQ
  exact hdim.symm.trans (by simpa using Matrix.square_of_invertible Y Y' hYY' hY'Y)

/-- A blocked comparison with unit-modulus multiplicities forces every original
periodic-block weight to have modulus one and recovers the target bond dimension.
Source: arXiv:1708.00029, Theorem 4.1, lines 750–756, using `lem:blocking-arbitrary`
and the multiplicity matching in `thm:bdequal`. The unit-modulus target condition
is the trace-preservation correction recorded in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem weight_norm_and_dim_eq_of_blocked_sameMPV₂Pos (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ) (hper : ∀ k, IsPeriodic (period k) (A k))
    {p : ℕ} (hp : 0 < p)
    (Q : SectorDecomposition (blockPhysDim d p)) (periodQ : Fin Q.basisCount → ℕ)
    (hPerQ : ∀ j, IsPeriodic (periodQ j) (Q.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos (blockTensor (toTensorFromBlocks μ A) p) Q.toTensor)
    (hQweight : ∀ j q, ‖Q.weight j q‖ = 1) :
    (∀ k, ‖μ k‖ = 1) ∧ (∑ k, dim k) = Q.totalDim := by
  classical
  let n : Fin r → ℕ := fun k ↦ (period k).gcd p
  have hex (k : Fin r) :
      ∃ (sd : Fin (n k) → ℕ)
        (B : (a : Fin (n k)) → MPSTensor (blockPhysDim d p) (sd a)),
        (∑ a, sd a) = dim k ∧
        (∀ a, IsPeriodic (period k / n k) (B a)) ∧
        SameMPV₂ (blockTensor (A k) p) (toTensorFromBlocks (fun _ ↦ 1) B) := by
    obtain ⟨_, sd, B, _, _, _, _, _, _, hd, _, hSame, _, _, _, hperB⟩ :=
      (hper k).exists_stepOrbit_blockDecomposition p
    exact ⟨sd, B, hd, hperB hp, hSame⟩
  choose sd B hdimB hperB hSameB using hex
  let e := (finSigmaFinEquiv (n := n)).symm
  have hflat := sameMPV₂_toTensorFromBlocks_refinement (fun k ↦ μ k ^ p)
    (fun k ↦ blockTensor (A k) p) n sd B hSameB
  have hbase := sameMPV₂_blockTensor_toTensorFromBlocks μ A p
  have hPQ : SameMPV₂Pos
      (toTensorFromBlocks (fun j ↦ μ (e j).1 ^ p) (fun j ↦ B (e j).1 (e j).2))
      Q.toTensor := by
    intro N hN σ
    exact (hflat N σ).symm.trans ((hbase N σ).symm.trans (hSame N hN σ))
  have hw := weight_norm_eq_one_of_block_sum_sameMPV₂Pos
    (fun j ↦ μ (e j).1 ^ p) (fun j ↦ pow_ne_zero _ (hμ _))
    (fun j ↦ period (e j).1 / n (e j).1) (fun j ↦ hperB (e j).1 (e j).2)
    Q periodQ hPerQ hNonRepQ hPQ hQweight
  have hdimFlat := sum_dim_eq_of_sameMPV₂Pos (fun j ↦ μ (e j).1 ^ p)
    (fun j ↦ pow_ne_zero _ (hμ _)) (fun j ↦ B (e j).1 (e j).2)
    (fun j ↦ period (e j).1 / n (e j).1) (fun j ↦ hperB (e j).1 (e j).2)
    Q periodQ hPerQ hNonRepQ hPQ
  constructor
  · intro k
    let a : Fin (n k) := ⟨0, Nat.gcd_pos_of_pos_right _ hp⟩
    have hh := hw (finSigmaFinEquiv ⟨k, a⟩)
    change ‖μ ((finSigmaFinEquiv (n := n)).symm (finSigmaFinEquiv ⟨k, a⟩)).1 ^ p‖ = 1 at hh
    rw [Equiv.symm_apply_apply, norm_pow] at hh
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.ne_of_gt hp)).mp hh
  · have hdimSum : (∑ j, sd (e j).1 (e j).2) = ∑ k, dim k := by
      rw [Equiv.sum_comp e (fun ka ↦ sd ka.1 ka.2), Fintype.sum_sigma]
      simp only [hdimB]
    exact hdimSum.symm.trans hdimFlat

end Blocked

/-- Normalize an arbitrary tensor whose positive blocking matches a periodic
sector decomposition with unit-modulus weights. The resulting unit-weight blocks
have total dimension exactly that of the target. Source: arXiv:1708.00029,
Theorem 4.1, lines 750–756. This is a positive-length presentation, not a claimed
unitary similarity of the original arbitrary tensor; the corrected forward proof
continues with the presented blocks. -/
theorem exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos
    (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (Q : SectorDecomposition (blockPhysDim d p)) (periodQ : Fin Q.basisCount → ℕ)
    (hPerQ : ∀ j, IsPeriodic (periodQ j) (Q.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos (blockTensor A p) Q.toTensor)
    (hQweight : ∀ j q, ‖Q.weight j q‖ = 1) :
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (B : (k : Fin r) → MPSTensor d (dim k)) (period : Fin r → ℕ),
      (∀ k, IsPeriodic (period k) (B k)) ∧
      (∑ k, dim k) = Q.totalDim ∧ (∑ k, dim k) ≤ D ∧
      SameMPV₂Pos A (toTensorFromBlocks (fun _ ↦ 1) B) := by
  obtain ⟨r, dim, μ, B, period, hper, hμpos, _, hAB, hbound⟩ :=
    exists_periodic_blockDecomposition A
  have hμ (k : Fin r) : μ k ≠ 0 := (hμpos k).ne'
  have hBlock := sameMPV₂Pos_blockTensor A (toTensorFromBlocks μ B) hAB p hp
  obtain ⟨hw, hdim⟩ := weight_norm_and_dim_eq_of_blocked_sameMPV₂Pos
    μ hμ B period hper hp Q periodQ hPerQ hNonRepQ
    (hBlock.symm.trans hSame) hQweight
  refine ⟨r, dim, (fun k i ↦ μ k • B k i), period,
    (fun k ↦ isPeriodic_smul_of_norm_one (hw k) (B k) (hper k)), hdim, hbound, ?_⟩
  have he : toTensorFromBlocks (fun _ ↦ 1) (fun k i ↦ μ k • B k i) =
      toTensorFromBlocks μ B := by
    unfold toTensorFromBlocks
    simp only [one_smul]
  rw [he]
  exact hAB

end MPSTensor
