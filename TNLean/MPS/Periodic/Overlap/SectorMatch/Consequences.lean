/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SectorMatch.Contraction
import TNLean.MPS.Periodic.Overlap.SectorMatch.Propagation

/-!
# Consequences of periodic sector matching

This module assembles propagation and full-cycle contraction into the
sector-match branch of the periodic-overlap dichotomy.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module

namespace MPSTensor

variable {d D : ℕ}

/-- **Case 3: a matching sector implies gauge equivalence**. If two periodic tensors have
the same period and a compressed sector match exists, then they satisfy the repeated-block
relation: A^i = ξ Y B^i Y⁻¹ for a unit-modulus scalar ξ and an invertible gauge Y.

The hypotheses describe compressed sector decompositions: `blocksA`/`blocksB` are
the cyclic-sector tensors on corner bond spaces, tied back to the
original blocked tensors via `SameMPV₂` and to the cyclic orbit
structure via `IsCyclicSectorDecomp`. Global nondegeneracy
(`hNondegA : ∀ u, dimA u ≠ 0`) ensures every sector of `A` has
positive bond dimension, which is needed for normality of each sector
tensor. The `hSomeMatch` witness provides a single matching sector pair
`(u₀, v₀)` with compatible dimensions (the nondegeneracy of `dimA u₀`
follows from `hNondegA`), from which translation propagation extends the
match to all sectors.

The specified projectors and corner identifications realize the blocked sector
tensors as the corners \(C_u^\alpha = P_u (A^{[m]})^\alpha P_u\) and
\(D_v^\alpha = Q_v (B^{[m]})^\alpha Q_v\), matching the \(C_u\)-notation
used in Lemma bdcf before the Appendix A contraction step.

This is the repeated-block consequence of the sector-match case in
arXiv:1708.00029, Appendix A, lines 961--1117. -/
theorem periodicOverlap_gaugeEquiv_of_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    {PA PB : Fin m → MatrixAlg D}
    {φA : (k : Fin m) →
      Matrix (Fin (dimA k)) (Fin (dimA k)) ℂ ≃ₗ[ℂ] cornerSubmodule (PA k)}
    {φB : (k : Fin m) →
      Matrix (Fin (dimB k)) (Fin (dimB k)) ℂ ≃ₗ[ℂ] cornerSubmodule (PB k)}
    (hA_cyclic : IsCyclicSectorDecompWith A blocksA PA φA)
    (hB_cyclic : IsCyclicSectorDecompWith B blocksB PB φB)
    (hA_letter : ∀ k (i : Fin (blockPhysDim d m)),
      (φA k (blocksA k i)).1 = PA k * (blockTensor A m) i * PA k)
    (hB_letter : ∀ k (i : Fin (blockPhysDim d m)),
      (φB k (blocksB k i)).1 = PB k * (blockTensor B m) i * PB k)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hSomeMatch : ∃ (u₀ v₀ : Fin m) (hdim : dimA u₀ = dimB v₀),
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u₀))
        (blocksB v₀)) :
    RepeatedBlocks A B := by
  -- APPENDIX TWO-STAGE STRUCTURE (arXiv:1708.00029 lines 961--1117):
  --   1. `sectorMatch_propagation`: iterate the single match around the cycle
  --      (translation operator + thm:cf, lines 985--1008), reindexed to the
  --      offset form (u, u + q) with q = v₀ - u₀;
  --   2. `sectorBlocked_isNormal_of_isPeriodic` (PROVED): each sector is normal;
  --   3. `sectorTensor_proportional_of_blockedMatch`: contract the matched blocks
  --      to a global gauge with the κ/θ/φ phase assembly (lines 1023--1117).
  -- Stage 1 (`sectorGaugePhaseEquiv_succ_of_cyclicTransport`) is closed via the
  -- one-site rotation covariance of the cross sector overlap; stage 3 is the
  -- contraction `sectorTensor_proportional_of_blockedMatch`.
  classical
  obtain ⟨u₀, v₀, hdim₀, hMatch⟩ := hSomeMatch
  have hA_lc := hA.leftCanonical
  have hB_lc := hB.leftCanonical
  have hA_cyclic_exists : IsCyclicSectorDecomp A blocksA :=
    ⟨PA, φA, hA_cyclic⟩
  have hB_cyclic_exists : IsCyclicSectorDecomp B blocksB :=
    ⟨PB, φB, hB_cyclic⟩
  -- Stage 1: propagate the single match to every offset `l` around the cycle.
  have hprop := sectorMatch_propagation A B hA hB blocksA blocksB
    hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic_exists hB_cyclic_exists
    hdim₀ (hNondegA u₀) hMatch
  -- Stage 2: each sector of `A` is a normal tensor.
  have hNormal : ∀ u, IsNormal (blocksA u) := fun u =>
    sectorBlocked_isNormal_of_isPeriodic A hA blocksA hA_blocks_lc hA_mpv
      hA_cyclic_exists u (hNondegA u)
  -- Stage 3: contract the (reindexed) per-sector matches into a unitary global gauge.
  obtain ⟨ξ, Uglob, hξ, hUUstar, hUstarU, hconj⟩ :=
    sectorTensor_proportional_of_blockedMatch A B hA_lc hB_lc blocksA blocksB
      hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic hA_letter
      hB_letter (v₀ - u₀) (by
        -- Reindex `hprop` from `(u₀ + l, v₀ + l)` to
        -- `(u, u + (v₀ - u₀))` by taking `l = u - u₀`.
        intro u
        have key := hprop (u - u₀)
        have eA : u₀ + (u - u₀) = u := by abel
        have eB : v₀ + (u - u₀) = u + (v₀ - u₀) := by abel
        rw [eA, eB] at key
        exact key) hNondegA hNormal
  exact ⟨ξ, ⟨Uglob, Uglobᴴ, hUUstar, hUstarU⟩, hξ, hconj⟩

/-- When `D₁ ≠ D₂`, no `RepeatedBlocks` relation can hold (the types don't
match), so the overlap must decay. This covers the `D₁ ≠ D₂` subcase of
the main dichotomy regardless of period matching. -/
theorem periodicOverlap_tendsto_zero_of_ne_dim
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hdim : D₁ ≠ D₂) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) :=
  mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B
    hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical hdim


end MPSTensor
