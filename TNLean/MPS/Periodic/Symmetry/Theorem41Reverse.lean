/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausRank
import TNLean.MPS.Periodic.Symmetry.Theorem41Forward

/-!
# Theorem 4.1, reverse direction

A root represented by at most the physical dimension's number of Kraus
operators yields a refinement tensor. The remaining selection problem is
recorded in `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Theorem 4.1 — reverse direction (`p`-divisibility ⇒ `p`-refinability) -/

section Theorem41Reverse

variable {d D : ℕ}


/-- A bounded Kraus-rank witness for a channel root can be expressed as an
`MPSTensor` with the ambient physical dimension by zero-padding the Kraus family. -/
theorem exists_tensor_of_hasKrausRankLE
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE : Channel.HasKrausRankLE E d) :
    ∃ A : MPSTensor d D, Kraus.transferMap A = E := by
  rcases hE with ⟨s, hs, hE⟩
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono hE hs
  refine ⟨K, ?_⟩
  ext X i j
  simpa [Kraus.transferMap_apply] using congrArg (fun M => M i j) (hK X).symm

/-- Equality with a blocked transfer map gives a refinement isometry.
No irreducible-form assumption is needed for this Kraus representation step.
Source: arXiv:1708.00029, Theorem 4.1, converse paragraph, lines 812--818;
Wolf Theorem 2.1(4). -/
theorem isPRefinable_of_transferMap_eq_blockTensor
    (B A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hTransferEq : Kraus.transferMap B = Kraus.transferMap (blockTensor A p)) :
    IsPRefinable B p := by
  classical
  -- `d ≤ d^p = blockPhysDim d p` whenever `p ≥ 1`: the Kraus-rank comparison needed by
  -- Wolf Theorem 2.1(4).
  have hCard : Fintype.card (Fin d) ≤ Fintype.card (Fin (blockPhysDim d p)) := by
    simp only [Fintype.card_fin, blockPhysDim_eq_pow]
    exact Nat.le_self_pow hp.ne' d
  -- Translate the linear-map equality into the Kraus-family equality needed by the freedom
  -- lemma.
  have hKraus :
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        ∑ α : Fin (blockPhysDim d p), blockTensor A p α * X * (blockTensor A p α)ᴴ =
          ∑ j : Fin d, B j * X * (B j)ᴴ := by
    intro X
    have hEq : Kraus.transferMap (blockTensor A p) X = Kraus.transferMap B X := by
      rw [← hTransferEq]
    simpa [Kraus.transferMap_apply] using hEq
  -- Extract the isometric mixing matrix `V` from Wolf Theorem 2.1(4).
  obtain ⟨V, hV, hBA⟩ :=
    (kraus_isometry_freedom_iff (blockTensor A p) B hCard).mp hKraus
  refine ⟨A, V, hV, ?_⟩
  intro N τ
  simp only [coeff_eq]
  -- Pointwise rewrite `blockTensor A p` as the `V`-mixing of `B`.
  have hAeq : (blockTensor A p : MPSTensor (blockPhysDim d p) D) =
      fun α => ∑ j : Fin d, V α j • B j := funext hBA
  rw [hAeq, evalWord_sum_smul_ofFn B V N τ, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [Matrix.trace_smul]
  rfl

/-- A selected channel root with at most the physical dimension's number
of Kraus operators gives a refinement tensor.

**Scope restriction (bounded root):** This proves the converse step of
arXiv:1708.00029, Theorem 4.1, lines 812--818, when the selected root has
Kraus rank at most `d`. Existence of such a root from divisibility alone is
not proved; see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`. -/
theorem isPRefinable_of_channel_root_hasKrausRankLE
    (B : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpow : Kraus.transferMap B = E ^ p)
    (hRank : Channel.HasKrausRankLE E d) :
    IsPRefinable B p := by
  obtain ⟨A, hA⟩ := exists_tensor_of_hasKrausRankLE hRank
  apply isPRefinable_of_transferMap_eq_blockTensor B A hp
  rw [transferMap_blockTensor, hA]
  exact hpow

end Theorem41Reverse

end MPSTensor
