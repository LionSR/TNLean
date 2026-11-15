/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitalChannelRank
import QICLean.Channel.Irreducible.CollatzWielandt
import QICLean.Channel.Schwarz.Closure
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# Refinement of irreducible tensors with unital transfer maps

Every channel root of an irreducible unital channel is unital. The rank
comparison for unital channels therefore bounds every supplied root by
the target's Choi rank, including singular targets in any bond dimension.
This proves a unital single-block case of arXiv:1708.00029, Theorem 4.1,
converse. The singular nonunital case remains open; see
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix ComplexOrder BigOperators

/-- Every channel whose power is irreducible and unital is itself unital.
The root fixes the identity because its image of the identity belongs to
the power's one-dimensional fixed space and has the same trace.
Source context: arXiv:1708.00029, Theorem 4.1, converse. -/
theorem IsChannel.map_one_eq_one_of_irreducible_pow {D : ℕ}
    {F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)} (hF : IsChannel F)
    (p : ℕ) (hIrr : IsIrreducibleMap (F ^ p)) (hOne : (F ^ p) 1 = 1) : F 1 = 1 := by
  by_cases hD : D = 0
  · subst D
    exact Subsingleton.elim _ _
  let : NeZero D := ⟨hD⟩
  have hFixed : (F ^ p) (F 1) = F 1 := by
    have h := congrArg (fun T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) => T 1)
      ((Commute.refl F).pow_left p).eq
    simpa only [Module.End.mul_apply, hOne] using h
  obtain ⟨c, hc⟩ := eigenvector_eq_smul_of_irreducible_positive
    (F ^ p) (hF.pos.pow p) hIrr (r := 1) zero_le_one Matrix.PosDef.one
      (by simpa using hOne) (by simpa using hFixed)
  have hTrace : c * (D : ℂ) = D := by
    have h := hF.tp 1
    rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at h
    simpa only [smul_eq_mul] using h
  have hcOne : c = 1 := by
    have h : (c - 1) * (D : ℂ) = 0 := by linear_combination hTrace
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (Nat.cast_ne_zero.mpr hD))
  simpa only [hcOne, one_smul] using hc

namespace Channel

/-- Every channel root of an irreducible unital target has Choi rank at
most that of the target. The target may be singular and the bond dimension
is arbitrary. The unital hypothesis is an explicit restriction relative
to the general root-selection problem in arXiv:1708.00029, Theorem 4.1. -/
theorem choiRank_le_pow_of_irreducible_unital {D : ℕ}
    {F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)} (hF : IsChannel F)
    {p : ℕ} (hp : 0 < p) (hIrr : IsIrreducibleMap (F ^ p))
    (hOne : (F ^ p) 1 = 1) : choiRank F ≤ choiRank (F ^ p) :=
  choiRank_le_pow_of_unital hF (hF.map_one_eq_one_of_irreducible_pow p hIrr hOne) hp

end Channel

namespace MPSTensor

/-- Channel divisibility gives a refinement when the target transfer map
is irreducible and unital, in any bond dimension and including singular
targets. These two explicit target hypotheses restrict the converse of
arXiv:1708.00029, Theorem 4.1; no bounded-root assumption is made. -/
theorem isPRefinable_of_isPDivisibleChannel_of_irreducible_unital
    {d D p : ℕ} (B : MPSTensor d D) (hp : 0 < p)
    (hIrr : IsIrreducibleMap (Kraus.transferMap B))
    (hOne : Kraus.transferMap B 1 = 1)
    (hDiv : IsPDivisibleChannel (Kraus.transferMap B) p) : IsPRefinable B p := by
  obtain ⟨F, hF, hpow⟩ := hDiv
  have hIrrF : IsIrreducibleMap (F ^ p) := hpow ▸ hIrr
  have hOneF : (F ^ p) 1 = 1 := by rwa [← hpow]
  have hRank : Channel.choiRank F ≤ d := by
    calc
      Channel.choiRank F ≤ Channel.choiRank (F ^ p) :=
        Channel.choiRank_le_pow_of_irreducible_unital hF hp hIrrF hOneF
      _ = Channel.choiRank (Kraus.transferMap B) := congrArg Channel.choiRank hpow.symm
      _ ≤ d := Channel.choiRank_le_of_hasKrausCard ⟨B, by intro X; simp⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE B hp F hpow
    ⟨Channel.choiRank F, hRank, Channel.hasKrausCard_choiRank_of_cp hF.cp⟩

end MPSTensor
