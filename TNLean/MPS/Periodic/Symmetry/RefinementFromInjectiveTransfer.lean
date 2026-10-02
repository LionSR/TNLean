/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.InjectivePositiveMapRank
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# Refinement of tensors with invertible transfer maps

Every completely positive root of an invertible transfer map has Choi rank
at most that of the transfer map. Thus channel divisibility gives tensor
refinement without a separate choice of a bounded-rank root.

**Scope restriction (invertible transfer map):** This proves the converse
of arXiv:1708.00029, Theorem 4.1, lines 812--818, for transfer maps that are
invertible as linear maps. The singular case remains the selection problem
recorded in `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- Channel divisibility implies refinement when the target transfer map is
injective, hence invertible in finite dimension. No canonical-form assumption
is required. Source context: arXiv:1708.00029, Theorem 4.1, converse,
lines 812--818. -/
theorem isPRefinable_of_isPDivisibleChannel_of_injective
    {d D p : ℕ} (B : MPSTensor d D) (hp : 0 < p)
    (hB : Function.Injective (Kraus.transferMap B))
    (hDiv : IsPDivisibleChannel (Kraus.transferMap B) p) :
    IsPRefinable B p := by
  obtain ⟨F, hF, hpow⟩ := hDiv
  have hPowInjective : Function.Injective (F ^ p) := hpow ▸ hB
  have hFInjective : Function.Injective F := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    intro X Y hXY
    apply hPowInjective
    simp only [pow_succ, Module.End.mul_apply, hXY]
  have hRank : Channel.choiRank F ≤ d := by
    calc
      Channel.choiRank F ≤ Channel.choiRank (F ^ p) :=
        Channel.choiRank_le_pow_of_injective hF.cp hFInjective hp
      _ = Channel.choiRank (Kraus.transferMap B) := congrArg Channel.choiRank hpow.symm
      _ ≤ d := Channel.choiRank_le_of_hasKrausCard ⟨B, by intro X; simp⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE B hp F hpow
    ⟨Channel.choiRank F, hRank, Channel.hasKrausCard_choiRank_of_cp hF.cp⟩

end MPSTensor
