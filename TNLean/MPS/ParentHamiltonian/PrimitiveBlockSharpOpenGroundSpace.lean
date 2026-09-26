/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.BlockWordSpanPropagation
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockWordSpan

/-!
# The printed open-chain threshold for primitive blocks

For at least two inequivalent primitive blocks with a common injective length
\(L_0>0\), the simultaneous word span is full from length
\(3(r-1)(L_0+1)\) onwards. Thus the open-chain kernel identity holds at every
interaction range at least \(3(r-1)(L_0+1)+1\).

This retains the threshold of PGVWC07, arXiv:quant-ph/0608197, Theorem 12
(label `2blocks.2`), lines 1424--1454, using the simultaneous-span estimate
of the direct-sum lemma (label lem:direct-sum), lines 1346--1408. No larger injective length is chosen.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [NeZero d] [∀ j, NeZero (dim j)]

/-- The open-chain kernel of a primitive block sum equals its boundary space
at the printed PGVWC07 interaction threshold. The common injective length is
supplied, rather than replaced by a larger one. Source: PGVWC07, Theorem 12,
label `2blocks.2`, lines 1424--1454. -/
theorem ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_threeBlock_bound
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {L₀ R N : ℕ} (hL₀ : 0 < L₀)
    (hBlk : ∀ j, Kraus.IsNBlkInjective (A j) L₀) (hr : 2 ≤ r)
    (hR : 3 * (r - 1) * (L₀ + 1) + 1 ≤ R) (hRN : R ≤ N) :
    LinearMap.ker
        (openParentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ) A) R N) =
      groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N := by
  have hSpan := wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1
    A (HasIrreducibleBlocks.ofForall fun j ↦ (hP j).isIrreducibleFamily_of_posDef (hρ j))
    (IsLeftCanonicalBlockFamily.ofForall fun j ↦ (hP j).norm)
    (HasNormalizedSelfOverlap.ofForall fun j ↦
      overlap_tendsto_one_of_peripheralPrimitive_of_irreducible (A j)
        ((hP j).isIrreducibleFamily_of_posDef (hρ j)) (hP j).norm (hP j).isPrimitive)
    (show BlocksNotGaugePhaseEquiv A from fun i j hij hdim ↦ by
      simpa only [eqRec_eq_cast] using hDistinct j i hij.symm hdim)
    hBlk (fun j ↦ isNBlkInjective_of_le hL₀ (hBlk j) (Nat.le_succ L₀))
    (fun j ↦ isNBlkInjective_of_le hL₀ (hBlk j) (by omega)) hL₀ hr
  exact ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES
    μ A hμ (fun j ↦ (hP j).norm)
    (fun n hn ↦ wordTupleSpanTop_of_ge_of_tracePreserving A hSpan
      (fun j ↦ (hP j).norm) hn) (by nlinarith) hRN

end MPSTensor
