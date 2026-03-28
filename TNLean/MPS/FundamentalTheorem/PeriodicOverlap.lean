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
  `lim_{N→∞} ⟨V_N(A)|V_N(A)⟩ = m` (along multiples of `m`).

### Cross-overlap dichotomy
* `periodicOverlap_tendsto_zero_of_ne_period` — (Case 1) different periods
  imply orthogonality.
* `periodicOverlap_tendsto_zero_of_no_sector_match` — (Case 2) same period
  but no sector match implies orthogonality.
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

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029, Proposition 3.3
  and Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Sector-restricted tensor (Eq. A.5–A.6) -/

/-- Two-sided sector restriction: `P_u * A^i * P_{u+1}`, where indices are
cyclic mod `m`. This is the tensor `A_u` from Eq. (A.5) of arXiv:1708.00029. -/
noncomputable def sectorRestrictedTensor
    {m : ℕ} [NeZero m] (P : Fin m → MatrixAlg D) (A : MPSTensor d D) (u : Fin m) :
    MPSTensor d D :=
  fun i => P u * A i * P (u + 1)

/-- Left multiplication by a sector projection recovers the sector-restricted tensor. -/
lemma sectorRestrictedTensor_eq_left_mul_right
    {m : ℕ} [NeZero m] (P : Fin m → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin m) (i : Fin d) :
    sectorRestrictedTensor P A u i = P u * A i * P (u + 1) :=
  rfl

/-! ## Self-overlap (first paragraph of Appendix A) -/

/-- Self-overlap of a periodic tensor: `⟨V_N(A)|V_N(A)⟩ = tr(E_A^N)`, and
since the peripheral eigenvalues are `m`-th roots of unity, each contributing 1
at multiples of `m`, the limit along `m·ℕ` equals `m`.

This is the first displayed equation of Appendix A. -/
theorem periodicSelfOverlap_tendsto
    [NeZero D] (A : MPSTensor d D) {m : ℕ}
    (hP : IsPeriodic m A) :
    ∀ᶠ k in atTop, mpvOverlap A A (m * k) = (m : ℂ) := by
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
Lemma 2.4: each `P_u A^(m)` is a normal tensor. -/
theorem sectorBlocked_isNormal_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    (P : Fin m → MatrixAlg D)
    (hProj : ∀ u, P u * P u = P u)
    (hComm : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (u : Fin m) :
    IsNormal (leftSectorTensor (P u) (blockTensor A m)) := by
  sorry

/-- If two periodic tensors have the same period `m` but no sector pair
`(P_u A^(m), Q_v B^(m))` is gauge-phase equivalent, then their overlap
decays to zero.

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
matching for all sector pairs `(u, u+q)` where `q = ṽ - ũ`. -/
theorem sectorMatch_propagation
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
    ∀ l : Fin m,
      ∃ (phase : ℂ) (gauge : MatrixAlg D),
        ∀ σ : Fin m → Fin d,
          PA (u₀ + l) * evalWord A (List.ofFn σ) =
            phase • (gauge * (QB (v₀ + l) * evalWord B (List.ofFn σ)) * gaugeᴴ) := by
  sorry

/-- **Per-site proportionality** (Eq. A.14 of arXiv:1708.00029):
After injectivity contraction, the sector-restricted tensors satisfy
`A_u^i = κ_v · e^{iη/m} · B_v^i` with `∏ κ_v = 1` and `|κ_v| = 1`. -/
theorem sectorTensor_proportional_of_blockedMatch
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (P Q : Fin m → MatrixAlg D)
    (hP_proj : ∀ u, P u * P u = P u)
    (hQ_proj : ∀ v, Q v * Q v = Q v)
    (hP_comm : ∀ u (i : Fin d), P u * A i = A i * P (u + 1))
    (hQ_comm : ∀ v (i : Fin d), Q v * B i = B i * Q (v + 1))
    (hBlockMatch : ∀ u : Fin m,
      ∃ (phase : ℂ) (gauge : MatrixAlg D),
        ∀ σ : Fin m → Fin d,
          P u * evalWord A (List.ofFn σ) =
            phase • (gauge * (Q u * evalWord B (List.ofFn σ)) * gaugeᴴ))
    (hNormal : ∀ u, IsNormal (leftSectorTensor (P u) (blockTensor A m))) :
    ∃ (ξ : ℂ) (U : Matrix (Fin D) (Fin D) ℂ),
      ‖ξ‖ = 1 ∧
      ∀ i : Fin d, A i = ξ • (U * B i * Uᴴ) := by
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
    -- Need sector projections from the cyclic decomposition.
    -- Case split on whether any sector pair matches.
    sorry

/-- **Eventual linear independence** (Corollary of Proposition 3.3):
Given a basis of periodic tensors `{A_j}`, there exists `N₀` such that
for all `N ≥ N₀`, the nonzero vectors `{|V_N(A_j)⟩}` are linearly
independent.

This is the "consequence" stated at the end of Proposition 3.3. -/
theorem periodicBasis_eventuallyLinearlyIndependent
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k))
    (hNonrep : ∀ i j, i ≠ j →
      ∀ (hdim : dim i = dim j),
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (A i)) (A j)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ (fun k => mpvState (A k) N) := by
  -- Use the dichotomy: pairwise non-repeated ⟹ pairwise decaying overlap.
  -- Self-overlaps converge to periods (bounded away from 0).
  -- By the epsilon-linear-independence lemma (Lemma 3.4 / Lem1 in the paper),
  -- for N large enough the vectors are linearly independent.
  sorry

end MPSTensor
