/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.RefinementRootRankIrreducibility
import TNLean.MPS.Periodic.RefinementRootRankChannelSquare
import TNLean.MPS.Periodic.PeriodExistence
import TNLean.MPS.Periodic.Symmetry.Theorem41Defs
import TNLean.MPS.CanonicalForm.Definitions
import QICLean.Channel.Peripheral.SpectralRadius

/-!
# A supplied root need not fit the target's physical dimension

The seven-dimensional cyclic-reset channel has ten independent Kraus
operators, while its square has nine. The square's nine-letter tensor is
irreducible and trace preserving, so it is a single normalized periodic
block. Thus a root supplied by channel divisibility cannot always be
compressed to the target's physical alphabet.

This concerns the stronger universal-root claim discussed in the converse
of arXiv:1708.00029, Theorem 4.1; it does not refute the existential
root-selection claim in that theorem. See
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- A trace-preserving irreducible tensor has a positive period.
Source: arXiv:1708.00029, lines 248--261 and 313--332. -/
private theorem exists_periodic_of_irreducible_leftCanonical
    {d D : ℕ} [NeZero D] (B : MPSTensor d D)
    (hB : Kraus.IsIrreducibleFamily B) (hTP : IsLeftCanonical B) :
    ∃ m, IsPeriodic m B := by
  have hRad := (Kraus.isPositiveMap_mapLM B).spectralRadius_eq_one_of_tracePreserving
    (Kraus.isChannel_mapLM B hTP).tp
  obtain ⟨m, hm⟩ := exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one hB hRad
  exact ⟨m, hB, hTP, hm.period_pos, hm.peripheral_eq⟩

/-- A periodic tensor is its own one-block irreducible form, with weight one.
Source: arXiv:1708.00029, equation `eq:irreducible-form`. -/
private noncomputable def oneBlockForm {d D m : ℕ}
    (B : MPSTensor d D) (hB : IsPeriodic m B) : IsIrreducibleForm B := by
  refine {
    r := 1
    dim := fun _ => D
    blocks := fun _ => B
    μ := fun _ => 1
    period := fun _ => m
    periodic := fun _ => hB
    weight_pos := ?_
    sameMPV := ?_ }
  · intro k
    norm_num
  · intro N σ
    rw [mpv_toTensorFromBlocks_eq_sum]
    simp

open CyclicResetCounterexample in
/-- A normalized irreducible nine-letter tensor has a supplied channel
square root of Kraus rank ten. That root has no nine-term Kraus
representation. This refutes the universal supplied-root bound, not the
existential root-selection claim in arXiv:1708.00029, Theorem 4.1,
lines 812--818. See `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`. -/
theorem supplied_root_rank_counterexample :
    Nonempty (IsIrreducibleForm square) ∧
      (∃ m, IsPeriodic m square) ∧
      IsPDivisibleChannel (Kraus.transferMap square) 2 ∧
      IsChannel (Kraus.transferMap root) ∧
      Channel.choiRank (Kraus.transferMap square) = 9 ∧
      Channel.choiRank (Kraus.transferMap root) = 10 ∧
      Kraus.transferMap square = (Kraus.transferMap root) ^ 2 ∧
      ¬ Channel.HasKrausRankLE (Kraus.transferMap root) 9 := by
  obtain ⟨m, hm⟩ := exists_periodic_of_irreducible_leftCanonical square
    square_isIrreducibleFamily square_isTP
  refine ⟨⟨oneBlockForm square hm⟩, ⟨m, hm⟩,
    ⟨Kraus.transferMap root, root_isChannel, transferMap_square_eq_pow⟩,
    root_isChannel, choiRank_square, choiRank_root, transferMap_square_eq_pow, ?_⟩
  intro hRank
  have hle := Channel.choiRank_le_of_hasKrausRankLE hRank
  rw [choiRank_root] at hle
  omega

end MPSTensor
