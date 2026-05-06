/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.Case2

/-!
# Periodic overlap dichotomy: Case 3

This module contains the equal-period, sector-match case of Appendix A of
arXiv:1708.00029: a matching pair of sectors propagates around the cycle and
forces repeated blocks.

## Main declarations

* `sectorMatch_propagation`
* `sectorTensor_proportional_of_blockedMatch`
* `periodicOverlap_gaugeEquiv_of_sector_match`
* `periodicOverlap_tendsto_zero_of_ne_dim`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 3: Same period, sector match → gauge-equivalent (Appendix A, main case) -/

/-- Nonzero sector dimensions propagate one step around a cyclic sector decomposition.

This part uses only the currently exposed cyclic-sector interface: if `dim u ≠ 0` then the
projection `P u` is nonzero by the `N = 0` trace identity. If `P (u + 1)` were zero,
the cyclic relation `E†(P (u + 1)) = P u` would force `P u = 0`, contradiction. -/
private lemma sectorDim_ne_zero_succ_of_cyclicSectorDecomp
    [NeZero D] (A : MPSTensor d D)
    {m : ℕ} [NeZero m]
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    {u : Fin m} (hNondeg : dim u ≠ 0) :
    dim (u + 1) ≠ 0 := by
  classical
  obtain ⟨P, _φ, hPproj, _hPsum, hShift, _hComm, hTrace, _hIntertwine, _hMul, _hStar⟩ :=
    hCyclic
  intro hzero
  have htrace_succ :
      Matrix.trace (P (u + 1)) = 0 := by
    have h0 := hTrace (u + 1) 0 Fin.elim0
    simp only [mpv, coeff, List.ofFn_zero, evalWord_nil, Matrix.mul_one] at h0
    rw [← h0, Matrix.trace_one, Fintype.card_fin, hzero, Nat.cast_zero]
  have hPsucc_zero : P (u + 1) = 0 :=
    (isOrthogonalProjection_posSemidef (hPproj (u + 1))).trace_eq_zero_iff.mp htrace_succ
  have hPu_zero : P u = 0 := by
    rw [← hShift u, hPsucc_zero, map_zero]
  have htrace_u : Matrix.trace (P u) = 0 := by
    rw [hPu_zero, Matrix.trace_zero]
  have hdim_zero : dim u = 0 := by
    have h0 := hTrace u 0 Fin.elim0
    simp only [mpv, coeff, List.ofFn_zero, evalWord_nil, Matrix.mul_one] at h0
    have hcast : (dim u : ℂ) = 0 := by
      have htrace_one_zero :
          Matrix.trace (1 : Matrix (Fin (dim u)) (Fin (dim u)) ℂ) = 0 := by
        exact h0.trans htrace_u
      simpa [Matrix.trace_one, Fintype.card_fin] using htrace_one_zero
    exact Nat.cast_eq_zero.mp hcast
  exact hNondeg hdim_zero

/-- Missing cyclic gauge-transport statement.

This is the precise interface still needed for Equation A.8 of arXiv:1708.00029. From the
current `IsCyclicSectorDecomp` data one knows the projection shift
`E†(P (k+1)) = P k` and the blocked trace realization of each compressed sector.
To prove this statement, the cyclic-sector construction must additionally expose
one-site corner transition tensors, for example the compressions of
`P k * A i * P (k+1)` and `Q l * B i * Q (l+1)`, together with an identification
of their `m`-fold cyclic products with the supplied `blocksA k` and `blocksB l`.
Then a gauge-phase equivalence at `(u, v)` transports along those one-site
transition tensors to a gauge-phase equivalence at `(u + 1, v + 1)`. -/
private lemma sectorGaugePhaseEquiv_succ_of_cyclicTransport
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
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
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    {u : Fin m} {v : Fin m}
    (hdim : dimA u = dimB v)
    (hNondeg : dimA u ≠ 0)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg
        (MPSTensor (blockPhysDim d m)) hdim)
        (blocksA u))
      (blocksB v)) :
    ∃ (hdim' : dimA (u + 1) = dimB (v + 1)),
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim')
          (blocksA (u + 1)))
        (blocksB (v + 1)) := by
  -- Missing step: one-site cyclic transition tensors and their identification
  -- with the compressed blocked sector tensors produced by
  -- `exists_compressedTensor_of_supported_projection`.
  sorry

/-- Missing one-step cyclic transport statement for sector matches.

This is the formal one-step version of Equation A.8 in arXiv:1708.00029. The cyclic
projection relation `E†(P (k+1)) = P k`, together with the compressed-sector
realization, should transport a gauge-phase equivalence between sector pair
`(u, v)` to one between `(u + 1, v + 1)`. The conclusion also propagates
nondegeneracy so the step can be iterated around the cycle. -/
private lemma sectorMatch_succ_of_cyclicSectorDecomp
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
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
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    {u : Fin m} {v : Fin m}
    (hdim : dimA u = dimB v)
    (hNondeg : dimA u ≠ 0)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg
        (MPSTensor (blockPhysDim d m)) hdim)
        (blocksA u))
      (blocksB v)) :
    ∃ (hdim' : dimA (u + 1) = dimB (v + 1)),
      dimA (u + 1) ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim')
          (blocksA (u + 1)))
        (blocksB (v + 1)) := by
  obtain ⟨hdim', hMatch'⟩ :=
    sectorGaugePhaseEquiv_succ_of_cyclicTransport A B hA_lc hB_lc
      blocksA blocksB hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv
      hA_cyclic hB_cyclic hdim hNondeg hMatch
  exact ⟨hdim',
    sectorDim_ne_zero_succ_of_cyclicSectorDecomp A blocksA hA_cyclic hNondeg,
    hMatch'⟩

/-- Transport a sector `GaugePhaseEquiv` across equalities of both sector indices. -/
private lemma gaugePhaseEquiv_cast_indices {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    {i₁ i₂ : Fin gA} {j₁ j₂ : Fin gB}
    (hi : i₁ = i₂) (hj : j₁ = j₂)
    (hdim : dimA i₁ = dimB j₁)
    (hg : GaugePhaseEquiv
      (cast (congr_arg (MPSTensor d) hdim) (A i₁)) (B j₁)) :
    GaugePhaseEquiv
      (cast (congr_arg (MPSTensor d) (show dimA i₂ = dimB j₂ from hi ▸ hj ▸ hdim))
        (A i₂)) (B j₂) := by
  subst hi
  subst hj
  exact hg

/-- **Translation propagation** (Equation A.8 / blockedABprop of arXiv:1708.00029):
Given one matching compressed sector pair at `(u₀, v₀)`, applying the
translation operator `T^l` for `l = 1, …, m-1` yields matching for all
sector pairs `(u₀ + l, v₀ + l)`. Each offset `l` gets its own gauge
(the paper's Equation blockedABprop produces a different unitary at each
sector, not a single transported gauge).

The `hA_cyclic`/`hB_cyclic` hypotheses (see `IsCyclicSectorDecomp`)
tie the `Fin m` block indexing to the cyclic orbit structure of the
transfer map, which is essential: without them, `SameMPV₂` alone is
permutation-invariant over blocks and would not justify the shifted
conclusion `(u₀ + l, v₀ + l)`.

The nondegeneracy hypothesis `dimA u₀ ≠ 0` ensures the initial match
is substantive: for `MPSTensor _ 0`, `GaugePhaseEquiv` holds vacuously
and propagation would produce only vacuous matches.

The left-canonical hypotheses (`hA_lc`, `hB_lc`) ensure the propagated
phases are unit-modulus: the transfer operator preserves the
trace-preserving condition, so the scaling factor remains on the unit
circle at each step. -/
lemma sectorMatch_propagation
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
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
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    {u₀ : Fin m} {v₀ : Fin m}
    (hdim₀ : dimA u₀ = dimB v₀)
    (hNondeg : dimA u₀ ≠ 0)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg
        (MPSTensor (blockPhysDim d m)) hdim₀)
        (blocksA u₀))
      (blocksB v₀)) :
    ∀ l : Fin m,
      ∃ (hdim : dimA (u₀ + l) = dimB (v₀ + l)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA (u₀ + l)))
          (blocksB (v₀ + l)) := by
  -- PROOF STRUCTURE: see lemma
  -- `sectorMatch_succ_of_cyclicSectorDecomp` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`.
  sorry

/-- Missing full-cycle contraction step for periodic-overlap Case 3.

At this point the sector transport has already been abstracted into
`hBlockMatch`, so the remaining gap is no longer the Equation A.8 staircase
identification.  What is still needed from Eqs. A.14-A.18 of
arXiv:1708.00029 is the contraction argument around the whole cycle:
for each sector `u`, normality gives a repetition length after which
`blocksA u` is injective, and one should use a right inverse from
`decompositionMap` to contract the repeated blocked products and recover
per-site proportionality with a single telescoped phase.

The current chain library provides `decompositionMap` /
`exists_rightInverse` in `MPS/Chain/OneSidedInverse.lean` and the two-site
proportionality theorem `tensor_proportional` in
`MPS/Chain/TensorEquality.lean`, but it does not yet provide the `m`-factor
cyclic contraction theorem needed to pass from `hBlockMatch` to a global
`RepeatedBlocks` witness. -/
private lemma repeatedBlocks_of_blockedSectorGaugePhase
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
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
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (q : Fin m)
    (hBlockMatch : ∀ u : Fin m,
      ∃ (hdim : dimA u = dimB (u + q)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA u))
          (blocksB (u + q)))
    (hNondeg : ∀ u, dimA u ≠ 0)
    (hNormal : ∀ u, IsNormal (blocksA u)) :
    RepeatedBlocks A B := by
  -- Missing ingredient: a reusable `m`-factor cyclic contraction theorem,
  -- built from `decompositionMap`, that upgrades the per-sector blocked
  -- gauge data in `hBlockMatch` to one global phase and one global gauge.
  -- The current library only provides the two-site theorem
  -- `tensor_proportional`, so the full-cycle step from Eqs. A.14-A.18 of
  -- arXiv:1708.00029 still has to be formalized separately.
  sorry

/-- **Per-site proportionality** (Equation A.14 of arXiv:1708.00029):
After injectivity contraction, the sector-restricted tensors satisfy
`A_u^i = κ_v · e^{iη/m} · B_v^i` with `∏ κ_v = 1` and `|κ_v| = 1`.

The offset `q` accounts for the cyclic shift between sector labelings of
`A` and `B`: propagation from a match at `(u₀, v₀)` yields pairs
`(u, u + q)` where `q = v₀ - u₀`.

The `hBlockMatch` hypothesis says that for every sector `u`, the
compressed blocks `blocksA u` and `blocksB (u + q)` are gauge-phase
equivalent (after dimension cast). The injectivity contraction argument
shows these per-sector gauges combine into a single global gauge for
`RepeatedBlocks`.

The nondegeneracy hypothesis `hNondeg` ensures every sector has
positive bond dimension. Without this, zero-dimensional sectors
satisfy `IsNormal`, `GaugePhaseEquiv`, and `hBlockMatch` vacuously,
which would make the conclusion `RepeatedBlocks A B` too strong.

The left-canonical hypotheses (`hA_lc`, `hB_lc`) are essential: they
force the gauge-proportionality phases to have unit modulus, which is
required by `RepeatedBlocks`. -/
lemma sectorTensor_proportional_of_blockedMatch
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
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
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (q : Fin m)
    (hBlockMatch : ∀ u : Fin m,
      ∃ (hdim : dimA u = dimB (u + q)),
        GaugePhaseEquiv
          (cast (congr_arg
            (MPSTensor (blockPhysDim d m)) hdim)
            (blocksA u))
          (blocksB (u + q)))
    (hNondeg : ∀ u, dimA u ≠ 0)
    (hNormal : ∀ u, IsNormal (blocksA u)) :
    RepeatedBlocks A B := by
  exact repeatedBlocks_of_blockedSectorGaugePhase
    A B hA_lc hB_lc blocksA blocksB hA_blocks_lc hB_blocks_lc
    hA_mpv hB_mpv hA_cyclic hB_cyclic q hBlockMatch hNondeg hNormal

/-- **Case 3: a matching sector implies gauge equivalence**. If two periodic tensors have
the same period and a compressed sector match exists, then they are related by a gauge
transformation with a unit-modulus phase: `A^i = e^{iξ} U B^i U†`.

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

This is Equation (A.17)–(A.18) of arXiv:1708.00029. -/
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
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hSomeMatch : ∃ (u₀ v₀ : Fin m) (hdim : dimA u₀ = dimB v₀),
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u₀))
        (blocksB v₀)) :
    RepeatedBlocks A B := by
  -- PROOF STRUCTURE: see lemmas `sectorMatch_propagation`,
  -- `sectorBlocked_isNormal_of_isPeriodic`, and
  -- `sectorTensor_proportional_of_blockedMatch` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`,
  -- `compressedTensor_adjointTransferMap_cornerBridge`, and
  -- `repeatedBlocks_of_blockedSectorGaugePhase`.
  sorry

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
