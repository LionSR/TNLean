/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse
import TNLean.MPS.Periodic.Symmetry.LiteralRefinementForward

/-!
# Refinability and bounded-rank channel roots

For normalized literal periodic block forms, refinement is equivalent to
existence of a channel root on the original physical alphabet. The unbounded
channel-root condition in the source remains a separate selection problem.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- A normalized literal periodic block family is refinable precisely when
its transfer channel admits a root with at most the original number of Kraus
operators.

**Scope restriction (bounded root):** This characterizes the tensor refinement
condition of arXiv:1708.00029, Theorem 4.1, lines 717--731 and 812--818, by a
bounded-rank root. Removing that bound from the right side requires the
selection argument recorded in
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`. The normalization correction
is recorded in `docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem isPRefinable_iff_exists_channel_root_hasKrausRankLE
    {d r p : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → MPSTensor d (dim k))
    (μ : Fin r → ℂ) (hμ : ∀ k, ‖μ k‖ = 1)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hp : 0 < p) :
    IsPRefinable (toTensorFromBlocks μ B) p ↔
      ∃ E : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ →ₗ[ℂ]
          Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ,
        IsChannel E ∧ Kraus.transferMap (toTensorFromBlocks μ B) = E ^ p ∧
          Channel.HasKrausRankLE E d := by
  constructor
  · intro hRefine
    obtain ⟨R, hR, hRoot⟩ :=
      exists_leftCanonical_root_of_isPRefinable_periodic_block_family B μ hμ period hPer hp
        hRefine
    refine ⟨Kraus.transferMap R, Kraus.isChannel_mapLM R hR, hRoot, ?_⟩
    exact Channel.hasKrausRankLE_of_hasKrausCard ⟨R, fun _ => rfl⟩
  · rintro ⟨E, _, hpow, hRank⟩
    exact isPRefinable_of_channel_root_hasKrausRankLE
      (toTensorFromBlocks μ B) hp E hpow hRank

end MPSTensor
