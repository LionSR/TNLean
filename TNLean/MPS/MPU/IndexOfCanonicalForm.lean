/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.VirtualSandwichBlocking
import TNLean.MPS.MPU.CanonicalFormGauge
import TNLean.MPS.MPU.Index
import TNLean.MPS.MPU.RepresentativeIndex
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.BlockingRanks

/-!
# The index of an MPU tensor in canonical form from its own cuts

Let `U` be an MPU tensor in canonical form and let `L ≥ 1` be such that the blocking `U_L` is
simple, with source-cut ranks `r_L` and `ℓ_L`. Then
$$
  r_L\ell_L=d^{2L},\qquad \operatorname{ind}U=\tfrac12(\log_2r_L-\log_2\ell_L)=\log_2(r_L/d^L),
$$
and for every `s` the blocking `U_{L+s}` is simple with `r_{L+s}=d^s r_L` and
`ℓ_{L+s}=d^s ℓ_L`.

The proof passes to a similar tensor `V = X U X⁻¹` in canonical form II. A bond similarity
commutes with blocking, preserves simplicity and the two cut ranks, and leaves every periodic
operator unchanged, so the canonical-form-II statements for `V` transfer to `U`.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Definition IV.1 and
  Proposition IV.2, lines 681--704.
* The chapter's Definition 7.2 and Lemma 7.1(b), restated for canonical form; MPU programme
  notes, milestone M-D (`MD.tex`), Theorem 1.3.

**Local fix (rank-product exponent):** Source line 703 prints $d^k$ for the rank product of a
simple blocking; the product is $d^{2k}$. See
`docs/paper-gaps/mpu_blocking_rank_product_exponent.tex`.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- A tensor in canonical form with a simple positive blocking is similar to a tensor `V` in
canonical form II whose blocking of the same length is simple. -/
private theorem IsMPU.exists_gauge_isMPUSimple_blockTensor [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {L : ℕ} (hS : IsMPUSimple (MPOTensor.blockTensor U L)) :
    ∃ X : GL (Fin D) ℂ,
      ∃ _ : IsMPUCanonicalFormII (MPOTensor.virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)),
      IsMPUSimple (MPOTensor.blockTensor
        (MPOTensor.virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) L) := by
  obtain ⟨X, ⟨hV⟩⟩ := hU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm hcf
  refine ⟨X, hV, ?_⟩
  rw [blockTensor_virtualSandwich_gl]
  exact hS.virtualSandwich_gl X

/-- **Rank product of a simple blocking in canonical form.** If `U` is an MPU tensor in
canonical form and its blocking `U_L`, `L ≥ 1`, is simple, then `r_L ℓ_L = d^{2L}`.

Source: arXiv:1703.09188, Proposition IV.2, lines 690--704, with the exponent `2L` (the
**Local fix** of the module docstring); the chapter's Lemma 7.1(b) restated for canonical form;
MD.tex Theorem 1.3. -/
theorem IsMPU.rightRank_mul_leftRank_blockTensor_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {L : ℕ} (hL : 0 < L) (hS : IsMPUSimple (MPOTensor.blockTensor U L)) :
    r[MPOTensor.blockTensor U L] * ℓ[MPOTensor.blockTensor U L] = d ^ (2 * L) := by
  obtain ⟨X, hV, hSV⟩ := hU.exists_gauge_isMPUSimple_blockTensor hcf hS
  rw [← rightRank_blockTensor_virtualSandwich_gl X U L,
    ← leftRank_blockTensor_virtualSandwich_gl X U L]
  exact hV.rightRank_mul_leftRank_blockTensor hL hSV

/-- **The index from the tensor's own cuts.** If `U` is an MPU tensor in canonical form and its
blocking `U_L`, `L ≥ 1`, is simple, then `ind U = ½ (log₂ r_L - log₂ ℓ_L)`.

Source: arXiv:1703.09188, Definition IV.1 and Proposition IV.2, lines 681--704; the chapter's
Definition 7.2 restated for canonical form; MD.tex Theorem 1.3. -/
theorem IsMPU.index_eq_logb_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {L : ℕ} (hL : 0 < L) (hS : IsMPUSimple (MPOTensor.blockTensor U L)) :
    hU.index = (1 / 2 : ℝ) *
      (Real.logb 2 r[MPOTensor.blockTensor U L] - Real.logb 2 ℓ[MPOTensor.blockTensor U L]) := by
  obtain ⟨X, hV, hSV⟩ := hU.exists_gauge_isMPUSimple_blockTensor hcf hS
  rw [hU.index_eq_canonical_representative hV
      (fun N _ ↦ mpo_virtualSandwich _ U _ (Units.inv_mul X) N),
    hV.index_eq_logb_of_isMPUSimple_blockTensor hL hSV,
    rightRank_blockTensor_virtualSandwich_gl, leftRank_blockTensor_virtualSandwich_gl]

/-- **The index from the right cut.** If `U` is an MPU tensor in canonical form and its
blocking `U_L`, `L ≥ 1`, is simple, then `ind U = log₂ (r_L / d^L)`.

Source: arXiv:1703.09188, Definition IV.1, lines 681--688, and Proposition IV.2,
lines 690--704; the chapter's Definition 7.2 restated for canonical form; MD.tex Theorem 1.3. -/
theorem IsMPU.index_eq_logb_rightRank_div_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {L : ℕ} (hL : 0 < L) (hS : IsMPUSimple (MPOTensor.blockTensor U L)) :
    hU.index = Real.logb 2 ((r[MPOTensor.blockTensor U L] : ℝ) / (d ^ L : ℕ)) := by
  obtain ⟨X, hV, hSV⟩ := hU.exists_gauge_isMPUSimple_blockTensor hcf hS
  rw [hU.index_eq_canonical_representative hV
      (fun N _ ↦ mpo_virtualSandwich _ U _ (Units.inv_mul X) N),
    hV.index_eq_logb_rightRank_div hL hSV, rightRank_blockTensor_virtualSandwich_gl]

/-- **Further blockings in canonical form.** If `U` is an MPU tensor in canonical form and its
blocking `U_L`, `L ≥ 1`, is simple, then for every `s` the blocking `U_{L+s}` is simple with
`r_{L+s} = d^s r_L` and `ℓ_{L+s} = d^s ℓ_L`.

Source: arXiv:1703.09188, Proposition IV.2, lines 690--704, with the exponent `2L` (the
**Local fix** of the module docstring); the chapter's Lemma 7.1(b) restated for canonical form;
MD.tex Theorem 1.3. -/
theorem IsMPU.blockTensor_add_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {L : ℕ} (hL : 0 < L) (hS : IsMPUSimple (MPOTensor.blockTensor U L)) (s : ℕ) :
    IsMPUSimple (MPOTensor.blockTensor U (L + s)) ∧
      r[MPOTensor.blockTensor U (L + s)] = d ^ s * r[MPOTensor.blockTensor U L] ∧
      ℓ[MPOTensor.blockTensor U (L + s)] = d ^ s * ℓ[MPOTensor.blockTensor U L] := by
  have hS' : IsMPUSimple (MPOTensor.blockTensor U (L + s)) :=
    hU.blockTensor_isMPUSimple_of_le hL (Nat.le_add_right L s) hS
  have hranks := blockingRanks_eq_pow_mul_of_products U (Nat.le_add_right L s)
    (Nat.pos_of_ne_zero (NeZero.ne d))
    (hU.rightRank_mul_leftRank_blockTensor_of_isMPUCanonicalForm hcf hL hS)
    (hU.rightRank_mul_leftRank_blockTensor_of_isMPUCanonicalForm hcf (by omega) hS')
  rw [Nat.add_sub_cancel_left] at hranks
  exact ⟨hS', hranks⟩

/-- **Simplicity of further blockings in canonical form.** If `U` is an MPU tensor in canonical
form and its blocking `U_L`, `L ≥ 1`, is simple, then `U_{L+s}` is simple for every `s`.

Source: arXiv:1703.09188, corollary following Proposition III.3, lines 442--446, used in
Proposition IV.2, lines 690--704; MD.tex Theorem 1.3. -/
theorem IsMPU.blockTensor_isMPUSimple_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {L : ℕ} (hL : 0 < L) (hS : IsMPUSimple (MPOTensor.blockTensor U L)) (s : ℕ) :
    IsMPUSimple (MPOTensor.blockTensor U (L + s)) :=
  (hU.blockTensor_add_of_isMPUCanonicalForm hcf hL hS s).1

/-- **Left ranks of further blockings in canonical form.** If `U` is an MPU tensor in canonical
form and its blocking `U_L`, `L ≥ 1`, is simple, then `ℓ_{L+s} = d^s ℓ_L` for every `s`.

Source: arXiv:1703.09188, Proposition IV.2, lines 690--704, with the exponent `2L` (the
**Local fix** of the module docstring); the chapter's Lemma 7.1(b) restated for canonical form;
MD.tex Theorem 1.3. -/
theorem IsMPU.leftRank_blockTensor_add_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor)
    {L : ℕ} (hL : 0 < L) (hS : IsMPUSimple (MPOTensor.blockTensor U L)) (s : ℕ) :
    ℓ[MPOTensor.blockTensor U (L + s)] = d ^ s * ℓ[MPOTensor.blockTensor U L] :=
  (hU.blockTensor_add_of_isMPUCanonicalForm hcf hL hS s).2.2

end MPOTensor
