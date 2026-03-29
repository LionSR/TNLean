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
import TNLean.Spectral.SpectralGapNT

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
This module serves as a skeleton / proof sketch and should not yet be
relied on as a completed formalization of Proposition 3.3.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029, Proposition 3.3
  and Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

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

/-- Two-sided sector restriction is "normal" when the original blocked tensor has
the appropriate cyclic-sector structure. This packages the consequence of
Lemma 2.4: each `P_u A^(m)` is a normal tensor.

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

/-- If two periodic tensors have the same period `m` but no sector pair
`(P_u A^(m), Q_v B^(m))` is gauge-phase equivalent, then their overlap
decays to zero.

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

/-- **Translation propagation** (Eq. A.8 of arXiv:1708.00029):
Given one matching sector pair `P_ũ A^(m) ≈ e^{iλ} V Q_ṽ B^(m) V†`,
applying the translation operator `T^l` for `l = 1, …, m-1` yields
matching for all sector pairs `(u₀ + l, v₀ + l)` with the *same* gauge `V`
(transported by the transfer operator). The phase may vary per `l`. -/
lemma sectorMatch_propagation
    [NeZero D]
    (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (PA QB : Fin m → MatrixAlg D)
    (hPA_comm : ∀ u (i : Fin d), PA u * A i = A i * PA (u + 1))
    (hQB_comm : ∀ v (i : Fin d), QB v * B i = B i * QB (v + 1))
    {u₀ : Fin m} {v₀ : Fin m}
    (hMatch : GaugePhaseEquiv
      (leftSectorTensor (PA u₀) (blockTensor A m))
      (leftSectorTensor (QB v₀) (blockTensor B m))) :
    ∃ (gauge : GL (Fin D) ℂ),
      ∀ l : Fin m, ∃ (phase : ℂ), ‖phase‖ = 1 ∧
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
where `q = v₀ - u₀`. -/
lemma sectorTensor_proportional_of_blockedMatch
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (P Q : Fin m → MatrixAlg D)
    (hP_proj : ∀ u, P u * P u = P u)
    (hQ_proj : ∀ v, Q v * Q v = Q v)
    (hP_comm : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (hQ_comm : ∀ v (i : Fin d), Q v * B i = B i * Q (v + 1))
    (q : Fin m)
    (gauge : GL (Fin D) ℂ)
    (hBlockMatch : ∀ u : Fin m, ∃ (phase : ℂ),
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
      -- Need sector projections from the cyclic decomposition.
      -- Case split on whether any sector pair matches.
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
  -- Use the dichotomy: pairwise non-repeated ⟹ pairwise decaying overlap.
  -- Self-overlaps converge to periods (bounded away from 0).
  -- By the epsilon-linear-independence lemma (Lemma 3.4 / Lem1 in the paper),
  -- for N large enough the vectors are linearly independent.
  sorry

end MPSTensor
