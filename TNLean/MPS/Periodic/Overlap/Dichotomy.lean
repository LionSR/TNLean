/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.Case3

/-!
# Periodic overlap dichotomy: main statement

This module contains the final Proposition 3.3 statement and its eventual
linear-independence corollary.

## Main declarations

* `periodicOverlapDichotomy`
* `periodicBasis_eventuallyLinearlyIndependent`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Proposition 3.3 and Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d : ℕ}

/-! ## Main dichotomy (Proposition 3.3) -/

/-- **Periodic overlap dichotomy** (Proposition 3.3 of arXiv:1708.00029).

For two periodic tensors `A` and `B` with periods `m_a` and `m_b` in
irreducible form II, either their overlap decays to zero, or `D_a = D_b` and
they are related by a gauge transformation up to a unit-modulus phase (which
forces m_a = m_b).

This is the core technical result of the paper: all subsequent theorems
(proportional FT, equal FT with Z-gauge, symmetry corollary) depend on it.

Source: arXiv:1708.00029, Proposition equal-or-orthogonal-generalized
(statement, lines 589--609; appendix proof, lines 903--1118). -/
theorem periodicOverlapDichotomy
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0)
      ∨ ∃ (hdim : D₁ = D₂),
          RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- APPENDIX CASE SPLIT (arXiv:1708.00029 lines 915--1117):
  --   * m_a ≠ m_b            → `periodicOverlap_tendsto_zero_of_ne_period`
  --   * m_a = m_b, D₁ ≠ D₂ → `periodicOverlap_tendsto_zero_of_ne_dim`
  --   * same period/dim, no sector match
  --                            → `periodicOverlap_tendsto_zero_of_no_sector_match`
  --   * same period/dim, a sector match
  --                            → `periodicOverlap_gaugeEquiv_of_sector_match`
  -- Each branch theorem is proved; the sector-match branch is proved modulo the
  -- two Case-3 leaves `sectorGaugePhaseEquiv_succ_of_cyclicTransport` and
  -- `repeatedBlocks_of_blockedSectorGaugePhase`.
  classical
  by_cases hm : m_a = m_b
  · subst hm
    haveI : NeZero m_a := ⟨hA.period_pos.ne'⟩
    by_cases hD : D₁ = D₂
    · subst hD
      obtain ⟨dimA, blocksA, hA_blocks_lc, hA_mpv, hA_cyclic, hNondegA⟩ :=
        exists_cyclic_sector_decomp_after_blocking_of_isPeriodic A hA
      obtain ⟨dimB, blocksB, hB_blocks_lc, hB_mpv, hB_cyclic, hNondegB⟩ :=
        exists_cyclic_sector_decomp_after_blocking_of_isPeriodic B hB
      by_cases hmatch : ∃ (u₀ v₀ : Fin m_a) (hdim : dimA u₀ = dimB v₀),
          GaugePhaseEquiv
            (cast (congr_arg (MPSTensor (blockPhysDim d m_a)) hdim) (blocksA u₀))
            (blocksB v₀)
      · refine Or.inr ⟨rfl, ?_⟩
        simpa using
          periodicOverlap_gaugeEquiv_of_sector_match A B hA hB blocksA blocksB
            hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic hNondegA hmatch
      · refine Or.inl ?_
        refine periodicOverlap_tendsto_zero_of_no_sector_match A B hA hB blocksA blocksB
          hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic hNondegA hNondegB ?_
        intro u v hdim _ hgpe
        exact hmatch ⟨u, v, hdim, hgpe⟩
    · exact Or.inl (periodicOverlap_tendsto_zero_of_ne_dim A B hA hB hD)
  · exact Or.inl (periodicOverlap_tendsto_zero_of_ne_period A B hA hB hm)

/-- **Eventual linear independence** (independence half of the consequence of
Proposition equal-or-orthogonal-generalized):
Given a family of periodic tensors `{A_j}` whose periods all divide a common
period `p`, there exists `N₀` such that for all `N ≥ N₀` that are multiples
of `p`, the vectors {|V_N(A_j)⟩} are linearly independent.

The common-period restriction ensures all `mpvState (A k) N` are nonzero
simultaneously (a zero vector would prevent `LinearIndependent` from holding).

**Scope restriction (independence only, no spanning):** the paper's consequence
(arXiv:1708.00029, lines 604--608) states *both* that the non-zero members of
{|V_N(A_j)⟩} are linearly independent *and* that they span |V_N(A)⟩ — the
spanning half is what "justifies the name basis of periodic vectors" (line 611).
Only the independence half is stated here. In addition the paper derives it from
Lem1t (the ε-almost-orthonormal ⇒ independent lemma, lines 511--519) applied to
the self-overlap limit and the cross-overlap decay; here the basis condition is
encoded directly as the pairwise non-repetition hypothesis `hNonrep`. The dropped
spanning clause and the Lem1t route are recorded in
docs/paper-gaps/1708_periodic_overlap_route_alignment.tex. -/
theorem periodicBasis_eventuallyLinearlyIndependent
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k))
    (p : ℕ) [NeZero p]
    (hDiv : ∀ k, period k ∣ p)
    (hNonrep : ∀ i j, i ≠ j →
      ∀ (hdim : dim i = dim j),
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (A i)) (A j)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ (fun k => mpvState (A k) (p * N)) := by
  -- PROOF STRUCTURE (Lem1t-style Gram argument, arXiv:1708.00029 lines 511--519,
  -- 604--608): for `N` a multiple of `p`, `periodicSelfOverlap_tendsto` gives
  -- ⟨V_N(A_k)|V_N(A_k)⟩ → m_k (the diagonal), and the off-diagonal entries
  -- ⟨V_N(A_i)|V_N(A_j)⟩ (i ≠ j) decay to 0 by the dichotomy
  -- `periodicOverlapDichotomy` together with the non-repetition hypothesis
  -- `hNonrep`. An almost-orthonormal Gram matrix is invertible (Lem1t), giving
  -- linear independence.
  -- The only sorry-backed input on this route is the off-diagonal decay for
  -- distinct cyclic sectors, `not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces`
  -- (SelfOverlap, the Lemma bdcf spectral non-repetition step, lines 404--423).
  sorry

end MPSTensor
