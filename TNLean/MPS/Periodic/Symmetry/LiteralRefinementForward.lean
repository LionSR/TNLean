/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.TracePreservingRefinementRoot
import TNLean.MPS.Periodic.Symmetry.Theorem41Forward

/-!
# Refinability implies divisibility for normalized literal block forms

The physical isometry of a refinement acts on each periodic block. The
resulting literal blocked target has an exact trace-preserving root, so its
transfer map, which equals the original transfer map, is a power of a channel.

**Local fix (trace preservation):** This is the forward implication of
arXiv:1708.00029, Theorem 4.1, lines 735--810, for the literal irreducible
block form with unit-modulus weights. The omitted normalization in the
printed statement is necessary, as documented in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Physical mixing commutes with a weighted direct sum, letter by letter.
Source: arXiv:1708.00029, Theorem 4.1, lines 735--745. -/
theorem toTensorFromBlocks_sum_smul
    {d m r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (B : (k : Fin r) → MPSTensor d (dim k))
    (W : Matrix (Fin m) (Fin d) ℂ) (τ : Fin m) :
    (∑ σ, W τ σ • toTensorFromBlocks μ B σ) =
      toTensorFromBlocks μ (fun k τ => ∑ σ, W τ σ • B k σ) τ := by
  classical
  simp only [toTensorFromBlocks_eq_sum_blockInclusion, Finset.smul_sum,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [Finset.sum_comm]
  congr 1
  funext k
  congr 1
  funext σ
  rw [mul_comm]

/-- A refinable literal direct sum of normalized periodic blocks admits a
left-canonical tensor root on the original physical alphabet. No
root-normalization or reconstruction hypothesis is assumed. Source: arXiv:1708.00029, Theorem 4.1,
lines 735--810, with the normalization correction described above. -/
theorem exists_leftCanonical_root_of_isPRefinable_periodic_block_family
    {d r p : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → MPSTensor d (dim k))
    (μ : Fin r → ℂ) (hμ : ∀ k, ‖μ k‖ = 1)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hp : 0 < p) (hRefine : IsPRefinable (toTensorFromBlocks μ B) p) :
    ∃ R : MPSTensor d (∑ k, dim k), IsLeftCanonical R ∧
      Kraus.transferMap (toTensorFromBlocks μ B) = Kraus.transferMap R ^ p := by
  classical
  obtain ⟨A, W, hW, hTransfer, hSame⟩ :=
    pRefinementCanonicalization_pullback (toTensorFromBlocks μ B) p hRefine
  let C := fun k τ => ∑ σ, W τ σ • B k σ
  have hLiteral : (fun τ => ∑ σ, W τ σ • toTensorFromBlocks μ B σ) =
      toTensorFromBlocks μ C := funext (toTensorFromBlocks_sum_smul μ B W)
  have hTarget : SameMPV₂Pos (blockTensor A p) (toTensorFromBlocks μ C) := by
    rw [← hLiteral]
    exact fun N _ σ => (hSame N σ).symm
  obtain ⟨R, hR, hRoot⟩ := exists_leftCanonical_root_of_sameMPV₂Pos_blockTensor
    A hp C μ hμ period (fun k => isPeriodic_kraus_isometry (B k) W hW (hPer k)) hTarget
  refine ⟨R, hR, ?_⟩
  rw [← transferMap_blockTensor, hRoot]
  rw [hLiteral] at hTransfer
  exact hTransfer.symm

/-- A refinable literal direct sum of normalized periodic blocks has a
$p$-divisible transfer channel. Source: arXiv:1708.00029, Theorem 4.1,
lines 735--810, with the normalization correction described above. -/
theorem isPDivisibleChannel_of_isPRefinable_periodic_block_family
    {d r p : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → MPSTensor d (dim k))
    (μ : Fin r → ℂ) (hμ : ∀ k, ‖μ k‖ = 1)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hp : 0 < p) (hRefine : IsPRefinable (toTensorFromBlocks μ B) p) :
    IsPDivisibleChannel (Kraus.transferMap (toTensorFromBlocks μ B)) p := by
  obtain ⟨R, hR, hRoot⟩ :=
    exists_leftCanonical_root_of_isPRefinable_periodic_block_family B μ hμ period hPer hp
      hRefine
  exact ⟨Kraus.transferMap R, Kraus.isChannel_mapLM R hR, hRoot⟩

end MPSTensor
