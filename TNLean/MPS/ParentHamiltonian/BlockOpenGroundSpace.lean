/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian

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
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- In the trace-preserving normalization, the boundary compatibility relation
\(A_b C_a=D_b A_a\) gives \(C_a=E A_a\), where
\(E=\sum_b A_b^\dagger D_b\). This is the left-normalized form of the
boundary argument in PGVWC07, Theorem 12, lines 1446--1451. -/
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
        groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L) :
    ψ ∈ groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) N := by
  apply contiguous_mem_of_restriction_intersection_submodules
    (fun M ↦ groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) M)
    (by omega : 0 < L) hLN ?_ hwindow
  rintro (_ | n) hM
  · omega
  · simpa only [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ] using
      iSup_groundSpace_eq_restriction_intersection_of_tracePreserving
        A (hSpan n (by omega)) hTP

/-- The kernel of the open parent Hamiltonian of a weighted direct sum is
its full boundary-condition space once the interaction range exceeds the
simultaneous word-span threshold. This is the open-chain conclusion of
PGVWC07, Theorem 12, proof lines 1430--1454, used in Nachtergaele,
arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES
    [NeZero d] (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) (hTP : ∀ j, ∑ a, (A j a)ᴴ * A j a = 1)
    {L₀ L N : ℕ} (hSpan : ∀ n ≥ L₀, WordTupleSpanTop A n)
    (hL : L₀ + 1 ≤ L) (hLN : L ≤ N) :
    LinearMap.ker
        (openParentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) L N) =
      groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N := by
  apply le_antisymm ?_ (groundSpaceES_le_ker_openParentHamiltonianES _ L N)
  refine fun v hv ↦ (mem_groundSpaceES_iff _ N v).mpr
    (contiguous_mem_groundSpace_toTensorFromBlocks μ A hμ hTP hSpan hL hLN
      (fun s hs τ ↦ ?_))
  let i : NonwrappingStart L N := ⟨⟨s, by omega⟩, hs⟩
  have hrestrictES := cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero
    (toTensorFromBlocks (d := d) (μ := μ) A) hLN i.1
    (localTermES_eq_zero_of_openParentHamiltonianES_eq_zero _ L N
      (LinearMap.mem_ker.mp hv) i) τ
  simpa [cyclicRestrictES,
    cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i.1) hLN i.2] using
    (mem_groundSpaceES_iff _ L _).mp hrestrictES

end MPSTensor
