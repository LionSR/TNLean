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

The main theorems in this file are currently stated with `sorry` proofs, and
some of the same-period statements are intentionally **provisional**. The live
cyclic-sector API in `CanonicalForm/CyclicSectors.lean` and
`CanonicalForm/Assembly.lean` naturally produces **compressed sector tensors**
living on the corner bond spaces, whereas several statements below are still
phrased in terms of the ambient tensors `leftSectorTensor (P u) (blockTensor A m)`.
That ambient formulation is convenient for the paper sketch, but it is stronger
than the currently formalized infrastructure and is the main blocker for the
first unfinished proofs in Case 2.

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

private theorem exists_cyclic_sector_decomp_after_blocking_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k)),
      (∀ k, ∑ i : Fin (blockPhysDim d m), (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ (blockTensor A m) (toTensorFromBlocks (μ := fun _ => 1) blocks) := by
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
  exact exists_cyclic_sector_decomp_after_blocking
    A hP.leftCanonical hP.irreducible ρ hρ_pd h_adjfix hIrrK hωprim hperiph_range

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

/-- Provisional Case-2 helper for the blocked sector tensors.

The intended mathematical content is Lemma 2.4: after blocking by the period,
each cyclic sector is a normal tensor. In the current file this statement is
still phrased for the ambient tensor `leftSectorTensor (P u) (blockTensor A m)`.
However, the live API more naturally gives a **compressed** tensor on the corner
bond space via `exists_compressedTensor_of_supported_projection`, together with
primitivity / irreducibility data for the corner restriction of the blocked
transfer map. Future proof work should likely reformulate this lemma using that
compressed sector tensor rather than the ambient one.

The nontriviality hypothesis `P u ≠ 0` is required because the zero projector
would yield the zero tensor, which is not normal (it cannot be block-injective).

The completeness and orthogonality hypotheses ensure that `P` forms a genuine
cyclic-sector decomposition (resolution of the identity into pairwise orthogonal
idempotents), not merely any commuting idempotent family. Without these, the
statement would be too strong: e.g., `P u = 1` for all `u` satisfies idempotence
and commutation but does not yield a normal sector tensor in general. -/
lemma sectorBlocked_isNormal_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    (P : Fin m → MatrixAlg D)
    (hProj : ∀ u, P u * P u = P u)
    (hComplete : ∑ u, P u = 1)
    (hOrtho : ∀ u v, u ≠ v → P u * P v = 0)
    (hComm : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (u : Fin m) (hNonzero : P u ≠ 0) :
    IsNormal (leftSectorTensor (P u) (blockTensor A m)) := by
  sorry

/-- Provisional same-period / no-match statement.

If two periodic tensors have the same period `m` but no sector pair matches,
their overlap should decay to zero. As above, the current statement uses the
ambient sector tensors `leftSectorTensor (P u) (blockTensor A m)`. The live
cyclic-sector machinery instead produces compressed sector tensors, and the
eventual proof will likely be cleaner when stated for those compressed blocks.

The hypotheses require that `PA` and `QB` form genuine cyclic-sector
decompositions: completeness (they sum to 1), mutual orthogonality, and
commutation with the tensor (interleaving with cyclic shift). These ensure
the overlap decomposes as a sum over sector pairs.

This is the "first case" of the same-period argument in Appendix A:
block by `m`, decompose into normal sectors, and observe that all
cross-sector overlaps decay by the normal-tensor overlap dichotomy. -/
theorem periodicOverlap_tendsto_zero_of_no_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    (PA QB : Fin m → MatrixAlg D)
    (hPA_proj : ∀ u, PA u * PA u = PA u)
    (hQB_proj : ∀ v, QB v * QB v = QB v)
    (hPA_complete : ∑ u, PA u = 1)
    (hQB_complete : ∑ v, QB v = 1)
    (hPA_ortho : ∀ u v, u ≠ v → PA u * PA v = 0)
    (hQB_ortho : ∀ u v, u ≠ v → QB u * QB v = 0)
    (hPA_comm : ∀ u (i : Fin d), PA u * A i = A i * PA (u + 1))
    (hQB_comm : ∀ v (i : Fin d), QB v * B i = B i * QB (v + 1))
    (hNoMatch : ∀ u v,
      ¬ GaugePhaseEquiv
        (leftSectorTensor (PA u) (blockTensor A m))
        (leftSectorTensor (QB v) (blockTensor B m))) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  -- Block by m. The overlap decomposes as a sum over sectors:
  --   ⟨V_{Nm}(A)|V_{Nm}(B)⟩ = ∑_{u,v} ⟨V_N(P_u A^(m))|V_N(Q_v B^(m))⟩
  -- Each sector pair has decaying overlap (since no match exists).
  -- A finite sum of sequences tending to 0 also tends to 0.
  sorry

/-! ## Case 3: Same period, sector match → gauge-equivalent (Appendix A, main case) -/

/-- **Translation propagation** (Eq. A.8 / blockedABprop of arXiv:1708.00029):
Given one matching sector pair `P_ũ A^(m) ≈ e^{iλ} V Q_ṽ B^(m) V†`,
applying the translation operator `T^l` for `l = 1, …, m-1` yields
matching for all sector pairs `(u₀ + l, v₀ + l)`. Each offset `l` gets
its own gauge `U_{ṽ+l}` (the paper's Eq. blockedABprop produces a different
unitary at each sector, not a single transported gauge). The phase also
varies per `l`.

The completeness and orthogonality hypotheses ensure `PA`/`QB` form genuine
cyclic-sector decompositions (resolution of identity into pairwise orthogonal
idempotents). Without completeness, the overlap decomposition into sector
contributions is invalid (identity-resolution steps fail).

The left-canonical hypotheses (`hA_lc`, `hB_lc`) ensure the propagated phases
are unit-modulus: the transfer operator preserves the trace-preserving
condition, so the scaling factor remains on the unit circle at each step. -/
lemma sectorMatch_propagation
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    (PA QB : Fin m → MatrixAlg D)
    (hPA_proj : ∀ u, PA u * PA u = PA u)
    (hQB_proj : ∀ v, QB v * QB v = QB v)
    (hPA_complete : ∑ u, PA u = 1)
    (hQB_complete : ∑ v, QB v = 1)
    (hPA_ortho : ∀ u v, u ≠ v → PA u * PA v = 0)
    (hQB_ortho : ∀ u v, u ≠ v → QB u * QB v = 0)
    (hPA_comm : ∀ u (i : Fin d), PA u * A i = A i * PA (u + 1))
    (hQB_comm : ∀ v (i : Fin d), QB v * B i = B i * QB (v + 1))
    {u₀ : Fin m} {v₀ : Fin m}
    (hMatch : GaugePhaseEquiv
      (leftSectorTensor (PA u₀) (blockTensor A m))
      (leftSectorTensor (QB v₀) (blockTensor B m))) :
    ∀ l : Fin m, ∃ (phase : ℂ) (gauge : GL (Fin D) ℂ), ‖phase‖ = 1 ∧
      ∀ σ : Fin m → Fin d,
        PA (u₀ + l) * evalWord A (List.ofFn σ) =
          phase • ((gauge : Matrix (Fin D) (Fin D) ℂ) *
            (QB (v₀ + l) * evalWord B (List.ofFn σ)) *
            ((gauge⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  sorry

/-- **Per-site proportionality** (Eq. A.14 of arXiv:1708.00029):
After injectivity contraction, the sector-restricted tensors satisfy
`A_u^i = κ_v · e^{iη/m} · B_v^i` with `∏ κ_v = 1` and `|κ_v| = 1`.

The offset `q` accounts for the cyclic shift between sector labelings of `A`
and `B`: propagation from a match at `(u₀, v₀)` yields pairs `(u, u + q)`
where `q = v₀ - u₀`.

Each sector `u` has its own gauge `gauge u` (as produced by translation
propagation, which yields a different unitary at each sector offset). The
injectivity contraction argument then shows these per-sector gauges are
compatible and combine into a single global gauge for `RepeatedBlocks`.

The left-canonical hypotheses (`hA_lc`, `hB_lc`) are essential: they force
the gauge-proportionality phases to have unit modulus, which is required by
`RepeatedBlocks`. Without normalization, one can have `A 0 = 2 • B 0` with
phase 2, satisfying the block match but not `RepeatedBlocks`. -/
lemma sectorTensor_proportional_of_blockedMatch
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    (P Q : Fin m → MatrixAlg D)
    (hP_proj : ∀ u, P u * P u = P u)
    (hQ_proj : ∀ v, Q v * Q v = Q v)
    (hP_complete : ∑ u, P u = 1)
    (hQ_complete : ∑ v, Q v = 1)
    (hP_ortho : ∀ u v, u ≠ v → P u * P v = 0)
    (hQ_ortho : ∀ u v, u ≠ v → Q u * Q v = 0)
    (hP_comm : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (hQ_comm : ∀ v (i : Fin d), Q v * B i = B i * Q (v + 1))
    (q : Fin m)
    (hBlockMatch : ∀ u : Fin m, ∃ (phase : ℂ) (gauge : GL (Fin D) ℂ),
        ‖phase‖ = 1 ∧
        ∀ σ : Fin m → Fin d,
          P u * evalWord A (List.ofFn σ) =
            phase • ((gauge : Matrix (Fin D) (Fin D) ℂ) *
              (Q (u + q) * evalWord B (List.ofFn σ)) *
              ((gauge⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))
    (hNormal : ∀ u, IsNormal (leftSectorTensor (P u) (blockTensor A m))) :
    RepeatedBlocks A B := by
  -- Step 1: Each blocked sector product is normal, so after N₀ repetitions
  --   it becomes injective.
  -- Step 2: The decomposition map Ω_u exists for each sector.
  -- Step 3: Concatenate A_u F_{u+1} A_{u+1} F_{u+2} ... and apply Ω inverses
  --   to extract: A_u ⊗ ... ⊗ A_{u+m-1} = e^{iη} B_v ⊗ ... ⊗ B_{v+m-1}
  -- Step 4: Extract per-site proportionality A_u = κ_v · e^{iη/m} · B_v
  -- Step 5: |κ_v| = 1 from left-canonical normalization
  -- Step 6: Telescope κ_v = e^{i(φ_v - φ_{v+1})} and assemble U
  sorry

/-- **Case 3 assembly**: If two periodic tensors have the same period and
a sector match exists, then they are related by a gauge transformation
with a unit-modulus phase: `A^i = e^{iξ} U B^i U†`.

This is Eq. (A.17)–(A.18) of arXiv:1708.00029. -/
theorem periodicOverlap_gaugeEquiv_of_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    (PA QB : Fin m → MatrixAlg D)
    (hPA_proj : ∀ u, PA u * PA u = PA u)
    (hQB_proj : ∀ v, QB v * QB v = QB v)
    (hPA_complete : ∑ u, PA u = 1)
    (hQB_complete : ∑ v, QB v = 1)
    (hPA_ortho : ∀ u v, u ≠ v → PA u * PA v = 0)
    (hQB_ortho : ∀ u v, u ≠ v → QB u * QB v = 0)
    (hPA_comm : ∀ u (i : Fin d), PA u * A i = A i * PA (u + 1))
    (hQB_comm : ∀ v (i : Fin d), QB v * B i = B i * QB (v + 1))
    (hSomeMatch : ∃ u v,
      GaugePhaseEquiv
        (leftSectorTensor (PA u) (blockTensor A m))
        (leftSectorTensor (QB v) (blockTensor B m))) :
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
      -- Extract cyclic-sector projections PA, QB from IsPeriodic.
      -- Case split on whether any sector pair (P_u A^(m), Q_v B^(m)) matches:
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
