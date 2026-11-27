/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BoundaryMatrix.BlockIntersectionProperty
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockSumGroundSpace
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.FundamentalTheorem.SectorBNT.PrimitiveBlockWordSpan
import TNLean.MPS.CanonicalForm.BlockSeparation.BlockWordSpanPropagation

/-!
# Open-chain ground spaces for a direct sum of blocks

The simultaneous word-span condition gives the intersection property for a
finite family of trace-preserving blocks. Iterating that property identifies
the kernel of their open-chain parent Hamiltonian with the sum of their
boundary-condition spaces.

The argument is the open-segment part of PGVWC07, arXiv:quant-ph/0608197,
Theorem 12, proof lines 1442--1452. For the trace-preserving normalization,
the boundary matrix is obtained by multiplying the compatibility relation on
the left by the adjoint and summing over the physical letter.

## Open-chain ground spaces of primitive block sums

For a finite family of pairwise inequivalent normalized primitive blocks,
one interaction threshold identifies every longer open-chain ground space
with the space of boundary-condition vectors of the weighted direct sum.
This is the open-chain part of PGVWC07, arXiv:quant-ph/0608197, Theorem 12,
and the finite-volume ground-space input in Nachtergaele,
arXiv:cond-mat/9410110, equations (3.12)--(3.16).

## The printed open-chain threshold for primitive blocks

For at least two inequivalent primitive blocks with a common injective length
\(L_0>0\), the simultaneous word span is full from length
\(3(r-1)(L_0+1)\) onwards. Thus the open-chain kernel identity holds at every
interaction range at least \(3(r-1)(L_0+1)+1\).

This retains the threshold of PGVWC07, arXiv:quant-ph/0608197, Theorem 12
(label `2blocks.2`), lines 1424--1454, using the simultaneous-span estimate
of the direct-sum lemma (label lem:direct-sum), lines 1346--1408. No larger
injective length is chosen.
-/

open MPTensor

section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- In the trace-preserving normalization, the boundary compatibility relation
\(A_b C_a=D_b A_a\) gives \(C_a=E A_a\), where
\(E=\sum_b A_b^\dagger D_b\). This is the left-normalized form of the
boundary argument in PGVWC07, Theorem 12, lines 1446--1451. The cited lines use
the dual normalization \(\sum_a A_aA_a^\dagger=I\) of the canonical form
(line 754), set \(E=\sum_a C_aA_a\), and conclude only
\(A_bC_a=A_bEA_a\); the normalization \(\sum_a A_a^\dagger A_a=I\) used
here gives \(C_a=EA_a\) directly. -/
theorem boundary_matrix_eq_of_compatibility_of_tracePreserving
    {D : ℕ} (A : MPSTensor d D)
    (C Dmat : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hTP : ∑ b, (A b)ᴴ * A b = 1)
    (hCompat : ∀ a b, A b * C a = Dmat b * A a) (a : Fin d) :
    C a = (∑ b, (A b)ᴴ * Dmat b) * A a := by
  calc
    C a = (∑ b, (A b)ᴴ * A b) * C a := by rw [hTP, one_mul]
    _ = (∑ b, (A b)ᴴ * Dmat b) * A a := by
      simp_rw [Finset.sum_mul, Matrix.mul_assoc, hCompat]

/-- The common word span gives the block intersection property in the
trace-preserving normalization. This is the one-step open-chain argument of
PGVWC07, Theorem 12, lines 1442--1452. -/
theorem mem_iSup_groundSpace_of_iSup_restrictions_of_tracePreserving
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1)
    (ψ : NSiteSpace d (n + 2))
    (hLeft : ∀ b, restrictLast ψ b ∈ ⨆ j, groundSpace (A j) (n + 1))
    (hRight : ∀ a, restrictFirst ψ a ∈ ⨆ j, groundSpace (A j) (n + 1)) :
    ψ ∈ ⨆ j, groundSpace (A j) (n + 2) := by
  obtain ⟨C, Dmat, hψ, hCoeff⟩ :=
    pgvwc07_trace_decompositions_of_iSup_restrictions A ψ hLeft hRight
  have hCompat := pgvwc07_blockwise_compatibility_of_trace_decomposition
    A hSpan C Dmat hCoeff
  rw [hψ]
  apply pgvwc07_sum_leftBoundaryComponents_mem_iSup_groundSpace A C
    (fun j ↦ ∑ b, (A j b)ᴴ * Dmat j b) n
  intro j a b
  simpa only [Matrix.mul_assoc] using congrArg (A j b * ·)
    (boundary_matrix_eq_of_compatibility_of_tracePreserving
      (A j) (C j) (Dmat j) (hTP j) (hCompat j) a)

/-- The sum of the block ground spaces satisfies the one-step restriction
intersection identity for trace-preserving blocks with full simultaneous
word span. This is PGVWC07, Theorem 12, lines 1442--1452. -/
theorem iSup_groundSpace_eq_restriction_intersection_of_tracePreserving
    (A : (j : Fin r) → MPSTensor d (dim j))
    {n : ℕ} (hSpan : WordTupleSpanTop A n)
    (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1) :
    ((⨅ b, (⨆ j, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a, (⨆ j, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j, groundSpace (A j) (n + 2) := by
  refine le_antisymm ?_ (iSup_le fun j ↦ le_inf ?_ ?_)
  · intro ψ hψ
    exact mem_iSup_groundSpace_of_iSup_restrictions_of_tracePreserving A hSpan hTP ψ
      (fun b ↦ (Submodule.mem_iInf _).mp hψ.1 b)
      (fun a ↦ (Submodule.mem_iInf _).mp hψ.2 a)
  · exact le_iInf fun b ψ hψ ↦ Submodule.mem_iSup_of_mem j
      (groundSpace_inLeftGround (A j) (n + 1) hψ b)
  · exact le_iInf fun a ψ hψ ↦ Submodule.mem_iSup_of_mem j
      (groundSpace_inRightGround (A j) (n + 1) hψ a)

/-- Contiguous local constraints determine the full boundary-condition space
of a weighted direct sum. The common word span is assumed at every length
at least \(L_0\), and the interaction range is at least \(L_0+1\).
This is the open-segment iteration in PGVWC07, Theorem 12, lines 1430--1454. -/
theorem contiguous_mem_groundSpace_toTensorFromBlocks
    [NeZero d] (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1)
    {L₀ L N : ℕ} (hSpan : ∀ n ≥ L₀, WordTupleSpanTop A n)
    (hL : L₀ + 1 ≤ L) (hLN : L ≤ N)
    {ψ : NSiteSpace d N}
    (hwindow : ∀ (s : ℕ) (hs : s + L ≤ N) (τ : Fin N → Fin d),
      contiguousRestrictₗ s L hs τ ψ ∈
        groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) L) :
    ψ ∈ groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) N := by
  apply contiguous_mem_of_restriction_intersection_submodules
    (fun M ↦ groundSpace (toTensorFromBlocks (α := Fin d) (μ := μ) A) M)
    (by omega : 0 < L) hLN ?_ hwindow
  rintro (_ | n) hM
  · omega
  · simpa only [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ] using
      iSup_groundSpace_eq_restriction_intersection_of_tracePreserving
        A (hSpan n (by omega)) hTP

/-- The kernel of the Hamiltonian of the parent interaction on the open chain of a weighted
direct sum is its full boundary-condition space once the interaction range exceeds the
simultaneous word-span threshold. This is the open-chain conclusion of PGVWC07, Theorem 12,
proof lines 1430--1454, used in Nachtergaele, arXiv:cond-mat/9410110,
equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_map_groundSpace
    [NeZero d] (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1)
    {L₀ L N : ℕ} (hSpan : ∀ n ≥ L₀, WordTupleSpanTop A n)
    (hL : L₀ + 1 ≤ L) (hLN : L ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks μ A) L N).hamiltonian) =
      ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  apply le_antisymm ?_ (map_groundSpace_le_ker_hamiltonian_parentChainInteraction _ L N)
  exact fun v hv ↦ (mem_map_groundSpace_iff _ N v).mpr
    (contiguous_mem_groundSpace_toTensorFromBlocks μ A hμ hTP hSpan hL hLN fun s hs τ ↦
      contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction _ hv
        s hs τ)

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- Every sufficiently long interaction gives the full boundary-condition space as the kernel of
the Hamiltonian of the parent interaction on the open chain for a direct sum of inequivalent
primitive blocks. The threshold is independent of the chain length. This is the open-segment
conclusion of PGVWC07, Theorem 12, lines 1430--1454. -/
theorem exists_ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_map_groundSpace
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L N : ℕ, L₀ ≤ L → L ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks μ A) L N).hamiltonian) =
        ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  exact
    (exists_eventually_wordTupleSpanTop_of_hasComplementaryFixedPointGap A ρ hP hρ hDistinct).elim
    fun L₀ hSpan ↦ ⟨L₀ + 1, Nat.succ_pos L₀, fun L N hL hLN ↦
      ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_map_groundSpace
        μ A hμ (fun j ↦ (hP j).norm) hSpan hL hLN⟩

end MPSTensor

end

section

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- The kernel of the Hamiltonian of the parent interaction on the open chain of a primitive
block sum equals its boundary space at the printed PGVWC07 interaction threshold. The common
injective length is supplied, rather than replaced by a larger one. Source: PGVWC07, Theorem 12,
label `2blocks.2`, lines 1424--1454. -/
theorem ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_threeBlock_bound
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {L₀ R N : ℕ} (hL₀ : 0 < L₀)
    (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀) (hr : 2 ≤ r)
    (hR : 3 * (r - 1) * (L₀ + 1) + 1 ≤ R) (hRN : R ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks μ A) R N).hamiltonian) =
      ((groundSpace (toTensorFromBlocks μ A) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  have hSpan := wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1
    A (fun j ↦ (hP j).isIrreducibleFamily_of_posDef (hρ j))
    (fun j ↦ (hP j).norm)
    (fun j ↦
      overlap_tendsto_one_of_peripheralPrimitive_of_irreducible (A j)
        ((hP j).isIrreducibleFamily_of_posDef (hρ j)) (hP j).norm (hP j).isPrimitive)
    (show BlocksNotGaugePhaseEquiv A from fun i j hij hdim ↦ by
      simpa only [eqRec_eq_cast] using hDistinct j i hij.symm hdim)
    hBlk (fun j ↦ Kraus.isNBlkInjective_of_le hL₀ (hBlk j) (Nat.le_succ L₀))
    (fun j ↦ Kraus.isNBlkInjective_of_le hL₀ (hBlk j) (by omega)) hL₀ hr
  exact ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_map_groundSpace
    μ A hμ (fun j ↦ (hP j).norm)
    (fun n hn ↦ wordTupleSpanTop_of_ge_of_tracePreserving A hSpan
      (fun j ↦ (hP j).norm) hn) (by nlinarith) hRN

end MPSTensor

end
