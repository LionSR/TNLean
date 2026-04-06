/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.MPS.Core.Blocking
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.CanonicalForm.Assembly
import TNLean.Spectral.SpectralGapNT

import TNLean.Algebra.GramMatrixLI
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Periodic overlap dichotomy (Proposition 3.3, arXiv:1708.00029)

This file formalizes Proposition 3.3 of De las Cuevas–Cirac–Schuch–Perez-Garcia
(arXiv:1708.00029) and its proof from Appendix A: the "equal-or-orthogonal"
dichotomy for periodic MPS tensors.

## Main results

### Self-overlap
* `periodicSelfOverlap_tendsto` — for a periodic tensor `A` with period `m`,
  `⟨V_{mk}(A)|V_{mk}(A)⟩ → m` as `k → ∞`.

### Cross-overlap dichotomy
* `periodicOverlap_tendsto_zero_of_ne_period` — (Case 1) different periods
  imply orthogonality.
* `periodicOverlap_tendsto_zero_of_no_sector_match` — (Case 2) same period,
  same bond dimension, but no sector match implies orthogonality.
* `periodicOverlap_tendsto_zero_of_ne_dim` — different bond dimensions
  imply orthogonality (cross-transfer spectral gap).
* `periodicOverlap_gaugeEquiv_of_sector_match` — (Case 3) same period with
  a sector match forces gauge-phase equivalence `A^i = e^{iξ} U B^i U†`.

### Combined dichotomy
* `periodicOverlapDichotomy` — the full Proposition 3.3 statement.

## Proof structure (Appendix A)

**Case 1** (different periods): Block by `lcm(m_a, m_b)`. The blocked sectors
are non-repeated normal tensors by Lemma 2.4. If any sector pair matched,
translation invariance would force two non-repeated sectors of `B` to generate
equal states — contradiction.

**Case 2** (same period, no match): Block by `m`. All cross-sector overlaps
decay by the normal-tensor overlap dichotomy. The finite sum decays.

**Case 3** (same period, sector match): The hard case. From one matching pair,
propagate by translation to all sectors, define sector-restricted tensors,
establish blocked proportionality, use injectivity contraction via the
decomposition map to extract per-site proportionality, absorb phases, and
assemble the global gauge unitary.

## Status

The main theorems in this file are currently stated with `sorry` proofs.
The same-period sector statements (Case 2 and Case 3 helpers) are formulated
using **compressed sector tensors** on corner bond spaces, matching the output
of `exists_cyclic_sector_decomp_after_blocking_of_isPeriodic` and the live
cyclic-sector API in `CanonicalForm/CyclicSectors.lean`.

This module therefore serves as a skeleton / proof sketch and should not yet be
relied on as a completed formalization of Proposition 3.3.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029, Proposition 3.3
  and Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The blocks form a **cyclic sector decomposition** of `blockTensor A m`, witnessed by
orthogonal projections `P` satisfying the cyclic commutation relation
`P k * (blockTensor A m) i = (blockTensor A m) i * P (k + 1)`. This ties
the `Fin m` indexing of the compressed blocks to the physical cyclic shift
structure of the transfer map's peripheral spectrum, and each block is
MPV-equivalent to the corresponding ambient sector tensor `P k · A^(m)`. -/
def IsCyclicSectorDecomp [NeZero D] [NeZero m] (A : MPSTensor d D)
    {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)) : Prop :=
  ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ),
    (∀ k, IsOrthogonalProjection (P k)) ∧
    (∑ k : Fin m, P k = 1) ∧
    (∀ k (i : Fin (blockPhysDim d m)),
      P k * (blockTensor A m) i = (blockTensor A m) i * P (k + 1)) ∧
    (∀ k, SameMPV₂ (leftSectorTensor (P k) (blockTensor A m)) (blocks k))

private theorem exists_cyclic_sector_decomp_after_blocking_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) ∧
      IsCyclicSectorDecomp A blocks := by
  obtain ⟨K, h_unitalK, hIrrK, ρ, hρ_pd, h_adjfix, rfl⟩ :=
    conjTranspose_kraus_setup A hP.leftCanonical hP.irreducible
  obtain ⟨ω, hωprim⟩ := hP.primitiveRoot
  have hM : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
    classical
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM
  letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  have hAdj :
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) =
        (transferMap (d := d) (D := D) A).adjoint := by
    simpa using transferMap_conjTranspose_eq_adjoint (d := d) (D := D) (A := A)
  have hperiph_roots :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        {μ : ℂ | μ ^ m = 1} := by
    ext μ
    constructor
    · intro hμ
      have hEigAdj :
          Module.End.HasEigenvalue ((transferMap (d := d) (D := D) A).adjoint) μ := by
        simpa [hAdj] using hμ.1
      have hEig :
          Module.End.HasEigenvalue (transferMap (d := d) (D := D) A) (star μ) :=
        (Module.End.hasEigenvalue_adjoint_iff
          (E := transferMap (d := d) (D := D) A) (μ := star μ)).2 <| by
            simpa [star_star] using hEigAdj
      have hNorm : ‖star μ‖ = 1 := by
        simpa [norm_star] using hμ.2
      have hStarMem :
          star μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) :=
        ⟨hEig, hNorm⟩
      have hpowStar : (star μ) ^ m = 1 := by
        simpa [hP.peripheral_eq] using hStarMem
      have hpow : μ ^ m = 1 := by
        have := congrArg star hpowStar
        simpa using this
      exact hpow
    · intro hμ
      have hpowStar : (star μ) ^ m = 1 := by
        have := congrArg star hμ
        simpa using this
      have hStarMem :
          star μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) := by
        simpa [hP.peripheral_eq] using hpowStar
      have hEigAdj :
          Module.End.HasEigenvalue ((transferMap (d := d) (D := D) A).adjoint) μ := by
          simpa [star_star] using
            (Module.End.hasEigenvalue_adjoint_iff
              (E := transferMap (d := d) (D := D) A) (μ := star μ)).1 hStarMem.1
      have hNorm : ‖μ‖ = 1 := by
        simpa [norm_star] using hStarMem.2
      exact ⟨by simpa [hAdj] using hEigAdj, hNorm⟩
  have hperiph_range :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) =
        Set.range (fun j : Fin m => ω ^ (j : ℕ)) := by
    ext μ
    constructor
    · intro hμ
      have hpow : μ ^ m = 1 := by
        simpa [hperiph_roots] using hμ
      obtain ⟨i, hi, hωi⟩ := hωprim.eq_pow_of_pow_eq_one hpow
      exact ⟨⟨i, hi⟩, by simpa using hωi⟩
    · rintro ⟨j, rfl⟩
      have hpow : (ω ^ (j : ℕ)) ^ m = 1 := by
        calc
          (ω ^ (j : ℕ)) ^ m = ω ^ ((j : ℕ) * m) := by rw [pow_mul]
          _ = ω ^ (m * (j : ℕ)) := by rw [Nat.mul_comm]
          _ = (ω ^ m) ^ (j : ℕ) := by rw [pow_mul]
          _ = 1 := by simp [hωprim.pow_eq_one]
      simpa [hperiph_roots] using hpow
  obtain ⟨dim, blocks, hLC, hMPV⟩ := exists_cyclic_sector_decomp_after_blocking
    A hP.leftCanonical hP.irreducible ρ hρ_pd h_adjfix hIrrK hωprim hperiph_range
  exact ⟨dim, blocks, hLC, hMPV, by
    -- The cyclic projections P are produced internally by the cyclic decomposition;
    -- extracting them requires threading them through the Assembly API.
    sorry⟩

/-! ## Self-overlap (first paragraph of Appendix A) -/

/-- Self-overlap of a periodic tensor: `⟨V_N(A)|V_N(A)⟩ = tr(E_A^N)`, and
since the peripheral eigenvalues are `m`-th roots of unity, each contributing 1
at multiples of `m`, the limit along `m·ℕ` equals `m`.

This is the first displayed equation of Appendix A. -/
theorem periodicSelfOverlap_tendsto
    [NeZero D] (A : MPSTensor d D) {m : ℕ}
    (hP : IsPeriodic m A) :
    Tendsto (fun k => mpvOverlap A A (m * k)) atTop (nhds (m : ℂ)) := by
  sorry

/-! ## Case 1: Different periods → orthogonal (Appendix A, first case) -/

/-- If two periodic tensors have different periods `m_a ≠ m_b`, their overlap
decays to zero. The argument blocks by `lcm(m_a, m_b)` and uses the
non-repetition of blocked sectors to derive a contradiction if any sector pair
matched.

This is the first substantial argument in Appendix A of arXiv:1708.00029. -/
theorem periodicOverlap_tendsto_zero_of_ne_period
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hne : m_a ≠ m_b) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  -- Step 1: For N not a multiple of both m_a and m_b, the overlap is zero.
  -- Step 2: For N = k * lcm(m_a, m_b), block by lcm(m_a, m_b).
  -- Step 3: By Lemma 2.4, blocked sectors are non-repeated normal tensors.
  -- Step 4: If any sector pair (P_u A^(p), Q_v B^(p)) matched via gauge,
  --   translation invariance would force Q_v B^(p) and Q_{v+1} B^(p) to
  --   generate equal states — contradicting non-repetition.
  -- Step 5: Since no sector pair matches, all cross-sector overlaps decay.
  sorry

/-! ## Case 2: Same period, no sector match → orthogonal (Appendix A, second case) -/

/-- Case-2 helper for the compressed blocked sector tensors.

The intended mathematical content is Lemma 2.4: after blocking by the period,
each cyclic sector is a normal tensor. The statement uses the compressed sector
tensor on the corner bond space, as produced by
`exists_cyclic_sector_decomp_after_blocking_of_isPeriodic`.

The nontriviality hypothesis `dim u ≠ 0` excludes the degenerate
zero-dimensional "missing sector" case. With the current definitions, an
`MPSTensor _ 0` may satisfy block-injectivity/normality vacuously, so this
assumption is used to focus on genuine nonempty sectors.

The `hBlocks_mpv` hypothesis ties the compressed block decomposition back to
the original blocked tensor, and `hCyclic` ensures the block indexing
follows the cyclic orbit structure of the transfer map's peripheral
spectrum (see `IsCyclicSectorDecomp`). -/
lemma sectorBlocked_isNormal_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (u : Fin m) (hNonzero : dim u ≠ 0) :
    IsNormal (blocks u) := by
  sorry

/-- Same-period / no-match statement using compressed sector tensors.

If two periodic tensors have the same period `m` but no compressed sector
pair matches (up to dimension cast and gauge-phase equivalence), their
overlap decays to zero.

The `hNoMatch` hypothesis quantifies over nondegenerate dimension
equalities: for each sector pair `(u, v)` with `dimA u ≠ 0` and any
proof that `dimA u = dimB v`, the compressed blocks are not gauge-phase
equivalent. The nondegeneracy guard `dimA u ≠ 0` is essential: when
`dimA u = 0`, `GaugePhaseEquiv` may hold vacuously for
`MPSTensor _ 0`, and without this guard `hNoMatch` would be
unsatisfiable whenever a zero-dimensional sector pair exists. With
this guard, `hNoMatch` is exactly the negation of `hSomeMatch` in
`periodicOverlap_gaugeEquiv_of_sector_match`, making the two
conditions complementary for the dichotomy proof.

This is the "first case" of the same-period argument in Appendix A:
block by `m`, decompose into normal sectors, and observe that all
cross-sector overlaps decay by the normal-tensor overlap dichotomy. -/
theorem periodicOverlap_tendsto_zero_of_no_sector_match
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
    (hNoMatch : ∀ u v (hdim : dimA u = dimB v),
      dimA u ≠ 0 →
      ¬ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v)) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  -- Block by m. Writing k for the block-count (so the chain length is m*k),
  --   ⟨V_{mk}(A)|V_{mk}(B)⟩ = ∑_{u,v} ⟨V_k(C_u)|V_k(C'_v)⟩
  -- Each sector pair has decaying overlap (since no match exists).
  -- A finite sum of sequences tending to 0 also tends to 0.
  -- The full sequence N ↦ mpvOverlap A B N tends to 0 by reparametrization.
  sorry

/-! ## Case 3: Same period, sector match → gauge-equivalent (Appendix A, main case) -/

/-- **Translation propagation** (Eq. A.8 / blockedABprop of arXiv:1708.00029):
Given one matching compressed sector pair at `(u₀, v₀)`, applying the
translation operator `T^l` for `l = 1, …, m-1` yields matching for all
sector pairs `(u₀ + l, v₀ + l)`. Each offset `l` gets its own gauge
(the paper's Eq. blockedABprop produces a different unitary at each
sector, not a single transported gauge).

The `hA_cyclic`/`hB_cyclic` hypotheses (see `IsCyclicSectorDecomp`)
tie the `Fin m` block indexing to the cyclic orbit structure of the
transfer map, which is essential: without them, `SameMPV₂` alone is
permutation-invariant over blocks and would not justify the shifted
conclusion `(u₀ + l, v₀ + l)`.

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
  sorry

/-- **Per-site proportionality** (Eq. A.14 of arXiv:1708.00029):
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
  -- Step 1: Each blocked sector product is normal, so after N₀
  --   repetitions it becomes injective.
  -- Step 2: The decomposition map Ω_u exists for each sector.
  -- Step 3: Concatenate and apply Ω inverses to extract:
  --   C_u ⊗ ... ⊗ C_{u+m-1} = e^{iη} C'_v ⊗ ... ⊗ C'_{v+m-1}
  -- Step 4: Extract per-site proportionality via injectivity
  -- Step 5: |κ_v| = 1 from left-canonical normalization
  -- Step 6: Telescope κ_v = e^{i(φ_v - φ_{v+1})} and assemble U
  sorry

/-- **Case 3 assembly**: If two periodic tensors have the same period and
a compressed sector match exists, then they are related by a gauge
transformation with a unit-modulus phase: `A^i = e^{iξ} U B^i U†`.

The hypotheses mirror the compressed corner API: `blocksA`/`blocksB` are
the cyclic-sector tensors on corner bond spaces, tied back to the
original blocked tensors via `SameMPV₂` and to the cyclic orbit
structure via `IsCyclicSectorDecomp`. The `hSomeMatch` witness
provides a single matching sector pair `(u₀, v₀)` with compatible
dimensions and nonzero bond dimension (`dimA u₀ ≠ 0`), which excludes
the degenerate case where a zero-dimensional `GaugePhaseEquiv` holds
vacuously.

This is Eq. (A.17)–(A.18) of arXiv:1708.00029. -/
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
    (hSomeMatch : ∃ (u₀ v₀ : Fin m) (hdim : dimA u₀ = dimB v₀),
      dimA u₀ ≠ 0 ∧ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u₀))
        (blocksB v₀)) :
    RepeatedBlocks A B := by
  -- Use translation propagation to get matching for all sectors,
  -- then apply per-site proportionality extraction.
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

/-! ## Main dichotomy (Proposition 3.3) -/

/-- **Periodic overlap dichotomy** (Proposition 3.3 of arXiv:1708.00029).

For two periodic tensors `A` and `B` with periods `m_a` and `m_b` in
irreducible form II, either their overlap decays to zero, or `D_a = D_b` and
they are related by a gauge transformation up to a unit-modulus phase (which
forces `m_a = m_b`).

This is the core technical result of the paper: all downstream theorems
(proportional FT, equal FT with Z-gauge, symmetry corollary) depend on it. -/
theorem periodicOverlapDichotomy
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0)
      ∨ ∃ (hdim : D₁ = D₂),
          RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- Case split on whether periods match.
  by_cases hm : m_a = m_b
  case neg =>
    -- Case 1: Different periods → orthogonal.
    exact Or.inl (periodicOverlap_tendsto_zero_of_ne_period A B hA hB hm)
  case pos =>
    subst hm
    -- Case split on whether bond dimensions match.
    by_cases hdim : D₁ = D₂
    case neg =>
      -- Different bond dimensions → orthogonal.
      exact Or.inl (periodicOverlap_tendsto_zero_of_ne_dim A B hA hB hdim)
    case pos =>
      subst hdim
      -- Same period, same bond dimension.
      -- Extract compressed cyclic-sector blocks from IsPeriodic
      -- (via exists_cyclic_sector_decomp_after_blocking_of_isPeriodic).
      -- Case split on whether any compressed sector pair matches:
      --   • No match → periodicOverlap_tendsto_zero_of_no_sector_match
      --   • Some match → sectorMatch_propagation (using hA.leftCanonical,
      --     hB.leftCanonical for unit-modulus phases), then
      --     sectorTensor_proportional_of_blockedMatch → RepeatedBlocks
      sorry

/-- **Eventual linear independence** (Corollary of Proposition 3.3):
Given a family of periodic tensors `{A_j}` whose periods all divide a common
period `p`, there exists `N₀` such that for all `N ≥ N₀` that are multiples
of `p`, the vectors `{|V_N(A_j)⟩}` are linearly independent.

The common-period restriction ensures all `mpvState (A k) N` are nonzero
simultaneously (a zero vector would prevent `LinearIndependent` from holding).

This is the "consequence" stated at the end of Proposition 3.3. -/
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
  classical
  let V : Type := lp (fun N : ℕ => MPVSpace d (p * N)) 2
  let v : Fin r → ℕ → V := fun k N => lp.single 2 N (mpvState (A k) (p * N))
  have hself_overlap : ∀ k,
      Tendsto (fun N => mpvOverlap (A k) (A k) (p * N)) atTop (nhds (period k : ℂ)) := by
    intro k
    rcases hDiv k with ⟨q, hq⟩
    have hq_pos : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hq0
      have : p = 0 := by simp [hq, hq0]
      exact NeZero.ne p this
    simpa [hq, Nat.mul_assoc] using
      (periodicSelfOverlap_tendsto (A := A k) (m := period k) (hP := hPer k)).comp
        (tendsto_id.nsmul_atTop hq_pos)
  have hcross_overlap : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (A i) (A j) (p * N)) atTop (nhds 0) := by
    intro i j hij
    have hbase : Tendsto (fun N => mpvOverlap (A i) (A j) N) atTop (nhds 0) := by
      rcases periodicOverlapDichotomy (A := A i) (B := A j) (hA := hPer i) (hB := hPer j) with
        hzero | hrep
      · exact hzero
      · rcases hrep with ⟨hdim, hrep⟩
        exact False.elim (hNonrep i j hij hdim hrep)
    simpa [nsmul_eq_mul] using
      hbase.comp (tendsto_id.nsmul_atTop (Nat.pos_of_ne_zero (NeZero.ne p)))
  have hInnerState : ∀ i j : Fin r,
      Tendsto (fun N => ⟪mpvState (A i) (p * N), mpvState (A j) (p * N)⟫_ℂ)
        atTop (nhds (if i = j then (period i : ℂ) else 0)) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [if_pos rfl, mpvInner, mpvOverlap_eq_star_mpvInner] using
        (hself_overlap i).star
    · simpa [if_neg hij, mpvInner, mpvOverlap_eq_star_mpvInner] using
        (hcross_overlap i j hij).star
  have hgram : ∀ i j : Fin r,
      Tendsto (fun N : ℕ => ⟪v i N, v j N⟫_ℂ) atTop
        (nhds (if i = j then (period i : ℂ) else 0)) := by
    intro i j
    refine (hInnerState i j).congr ?_
    intro N
    simp only [v]
    rw [lp.inner_single_left, lp.single_apply_self]
  have hLI_emb : ∀ᶠ N in atTop, LinearIndependent ℂ (fun k => v k N) := by
    refine eventually_linearIndependent_of_gram_tendsto_nondegenerate v
      (Matrix.diagonal fun k : Fin r => (period k : ℂ)) ?_ ?_
    · rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => by
        exact_mod_cast Nat.ne_of_gt (hPer k).period_pos
    · intro i j
      simpa [Matrix.diagonal_apply] using hgram i j
  have hLI : ∀ᶠ N in atTop, LinearIndependent ℂ (fun k => mpvState (A k) (p * N)) := by
    refine hLI_emb.mono ?_
    intro N hN
    let fN : MPVSpace d (p * N) →ₗ[ℂ] V :=
      lp.lsingle (𝕜 := ℂ) (E := fun M : ℕ => MPVSpace d (p * M)) 2 N
    have hN' :
        LinearIndependent ℂ (fun k : Fin r => fN (mpvState (A k) (p * N))) := by
      simpa [v, fN, lp.lsingle_apply] using hN
    exact LinearIndependent.of_comp fN hN'
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hLI
  exact ⟨N₀, hN₀⟩

end MPSTensor
