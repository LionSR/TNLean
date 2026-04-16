/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.MPS.Periodic.Overlap
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

open scoped Matrix BigOperators

/-!
# Periodic Fundamental Theorem of MPS (arXiv:1708.00029, §3)

This file formalizes the periodic fundamental theorem of arXiv:1708.00029 §3 and the
Z-gauge infrastructure used in its equal-case strengthening:

* **Theorem 3.4** (`fundamentalTheorem_periodic_proportional`): If two non-repeating
  block families satisfy the periodic overlap dichotomy, their bases of periodic tensors
  match up to a bijection with per-block `RepeatedBlocks` equivalence. (In the paper,
  proportional MPVs imply the dichotomy; here it is a direct hypothesis.)

* **Infrastructure for Theorem 3.8**: The equal-case strengthening produces per-block
  Z-gauge data (diagonal Z with Z^m = 1) from the Newton–Girard identity on sector weights.
  The Z-gauge construction helpers (`zgauge_construction`, `perBlock_zgauge_of_power_eq`)
  compose the infrastructure from PR #94 into ready-to-use form.

## Status of #81 (periodic overlap dichotomy)

Theorem 3.4 is stated in two forms:

* `fundamentalTheorem_periodic_proportional` takes a `PeriodicOverlapHypothesis` directly,
  leaving callers free to supply the dichotomy from any source.
* `fundamentalTheorem_periodic_proportional_of_isPeriodic` is an API variant that no
  longer takes `PeriodicOverlapHypothesis` as a parameter: the
  `hetRepeatedBlocks_of_nondecaying` field is filled inside
  `PeriodicOverlapHypothesis.ofIsPeriodic` via `periodicOverlapDichotomy` (PR #573,
  partially addressing #81). Callers only need to supply per-block `IsPeriodic` data
  plus the existence of non-decaying cross-family overlaps (`exists_nondecaying_A/B`),
  which encode the paper's proportional-MPV assumption.

  **Caveat**: `periodicOverlapDichotomy` is stated and callable, but its proof in
  `TNLean/MPS/Periodic/Overlap.lean` still depends on several
  admitted sub-lemmas (see that file's header: "should not yet be relied on as a
  completed formalization of Proposition 3.3"). Downstream results using the
  `_of_isPeriodic` variant therefore inherit those remaining proof obligations and
  should not be treated as unconditional.

The Z-gauge construction (Theorem 3.8 steps 5–7) is fully proved.

## Key references

* arXiv:1708.00029 (De las Cuevas–Schuch–Pérez-García–Cirac, 2017)
* `blocks_match_of_sameMPV₂_CFBNT` in `Full.lean` — structural template for Thm 3.4
* Z-gauge construction lemmas in `SectorDecomposition.lean` (PR #94)
-/

namespace MPSTensor

variable {d : ℕ}

/-! ## Heterogeneous RepeatedBlocks -/

/-- Heterogeneous version of `RepeatedBlocks`: allows blocks with different bond dimensions
by packing a dimension-equality witness. This avoids explicit `cast` manipulation in
theorems involving families of varying-dimension blocks (e.g., `IsIrreducibleForm`). -/
def HetRepeatedBlocks {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∃ (h : D₁ = D₂), RepeatedBlocks (cast (congr_arg (MPSTensor d) h) A) B

theorem HetRepeatedBlocks.dim_eq {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : HetRepeatedBlocks A B) : D₁ = D₂ :=
  h.1

theorem HetRepeatedBlocks.symm {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : HetRepeatedBlocks A B) : HetRepeatedBlocks B A := by
  obtain ⟨heq, hrep⟩ := h
  subst heq; exact ⟨rfl, hrep.symm⟩

theorem HetRepeatedBlocks.trans {D₁ D₂ D₃ : ℕ}
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} {C : MPSTensor d D₃}
    (h₁ : HetRepeatedBlocks A B) (h₂ : HetRepeatedBlocks B C) :
    HetRepeatedBlocks A C := by
  obtain ⟨heq₁, hrep₁⟩ := h₁
  obtain ⟨heq₂, hrep₂⟩ := h₂
  subst heq₁; subst heq₂
  exact ⟨rfl, hrep₁.trans hrep₂⟩

theorem HetRepeatedBlocks.of_repeatedBlocks {D : ℕ} {A B : MPSTensor d D}
    (h : RepeatedBlocks A B) : HetRepeatedBlocks A B :=
  ⟨rfl, h⟩

/-! ## Periodic block matching witness -/

/-- Witness for periodic block matching: equal block counts, a bijection, and per-block
heterogeneous `RepeatedBlocks` equivalence. This is the periodic analogue of
`BlockPermutationGaugeWitness`. -/
abbrev PeriodicBlockMatchingWitness
    {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k)) : Prop :=
  ∃ _h : rA = rB,
    ∃ perm : Fin rA ≃ Fin rB,
      ∀ j : Fin rA, HetRepeatedBlocks (A j) (B (perm j))

/-! ## Periodic overlap dichotomy hypothesis -/

/-- Hypothesis packaging the periodic overlap dichotomy (Proposition 3.3 of 1708.00029).

The `hetRepeatedBlocks_of_nondecaying` field can be filled via `periodicOverlapDichotomy`
(see `PeriodicOverlapHypothesis.ofIsPeriodic`), though that dichotomy's proof in
`PeriodicOverlap.lean` still relies on several admitted sub-lemmas. The fields capture
the essential results:
1. For each block in one family, a non-decaying overlap partner exists in the other.
2. Non-decaying overlap forces `HetRepeatedBlocks`.

Injectivity of the matching uses only `HetRepeatedBlocks.trans` and the non-repetition
hypothesis — no separate cross-overlap decay field is needed. -/
structure PeriodicOverlapHypothesis
    {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k)) where
  /-- For each A-block, ∃ B-block with non-decaying overlap. -/
  exists_nondecaying_A : ∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
    ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) Filter.atTop (nhds 0)
  /-- For each B-block, ∃ A-block with non-decaying overlap. -/
  exists_nondecaying_B : ∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
    ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) Filter.atTop (nhds 0)
  /-- Non-decaying cross-family overlap forces `HetRepeatedBlocks`. -/
  hetRepeatedBlocks_of_nondecaying : ∀ j k,
    ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) Filter.atTop (nhds 0) →
    HetRepeatedBlocks (A j) (B k)

/-- **Build `PeriodicOverlapHypothesis` from `IsPeriodic` data via the overlap dichotomy.**

Given block families with `IsPeriodic` data on each block, the
`hetRepeatedBlocks_of_nondecaying` field is filled by `periodicOverlapDichotomy`
(PR #573): for any pair `A j, B k`, the dichotomy returns either overlap decay
(contradicting non-decay) or `HetRepeatedBlocks (A j) (B k)`.

The `exists_nondecaying_A/B` fields remain as explicit hypotheses — they encode the
paper's content that proportional total MPVs force non-vanishing per-block overlaps.

**Remaining proof obligations.** `periodicOverlapDichotomy` is stated and callable, but
its proof in `TNLean/MPS/Periodic/Overlap.lean` transitively depends
on several admitted sub-lemmas (`periodicSelfOverlap_tendsto`,
`sectorBlocked_isNormal_of_isPeriodic`, `periodicOverlap_gaugeEquiv_of_sector_match`,
`periodicOverlap_tendsto_zero_of_no_sector_match`,
`exists_cyclic_sector_decomp_after_blocking`). The module header of `PeriodicOverlap.lean`
states that file "should not yet be relied on as a completed formalization of
Proposition 3.3". Downstream users of this constructor therefore inherit those
obligations and should not treat the resulting `PeriodicOverlapHypothesis` as
unconditionally proven. -/
def PeriodicOverlapHypothesis.ofIsPeriodic
    {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [hneA : ∀ j, NeZero (dimA j)] [hneB : ∀ k, NeZero (dimB k)]
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (periodA : Fin rA → ℕ) (periodB : Fin rB → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hExA : ∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N)
        Filter.atTop (nhds 0))
    (hExB : ∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N)
        Filter.atTop (nhds 0)) :
    PeriodicOverlapHypothesis A B where
  exists_nondecaying_A := hExA
  exists_nondecaying_B := hExB
  hetRepeatedBlocks_of_nondecaying := by
    intro j k hnd
    haveI : NeZero (dimA j) := hneA j
    haveI : NeZero (dimB k) := hneB k
    rcases periodicOverlapDichotomy (A j) (B k) (hPerA j) (hPerB k) with hdecay | hrep
    · exact absurd hdecay hnd
    · exact hrep

/-! ## Theorem 3.4 — Proportional case -/

section ProportionalCase

variable {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}

/-- **Theorem 3.4 (Proportional case, arXiv:1708.00029).**

If two non-repeating block families satisfy the periodic overlap dichotomy, then
their bases of periodic tensors match: equal block counts, a bijection, and per-block
`HetRepeatedBlocks` equivalence.

In the paper, proportional MPVs imply the overlap dichotomy; here the dichotomy is
taken as a direct hypothesis via `PeriodicOverlapHypothesis`.

The proof mirrors `blocks_match_of_sameMPV₂_CFBNT` in `Full.lean`:
1. Non-decaying overlap → `HetRepeatedBlocks` matching for each block.
2. Injectivity from `HetRepeatedBlocks.trans` + non-repetition.
3. Injective maps on finite types → equal cardinalities.
4. Bijection construction.

The `PeriodicOverlapHypothesis` parameter can be supplied via
`PeriodicOverlapHypothesis.ofIsPeriodic`, which uses `periodicOverlapDichotomy`
(PR #573, partially addressing #81) to fill the `hetRepeatedBlocks_of_nondecaying`
field; see `fundamentalTheorem_periodic_proportional_of_isPeriodic`. Note that
`periodicOverlapDichotomy`'s proof in `PeriodicOverlap.lean` still relies on several
admitted sub-lemmas, so callers going through that route inherit those obligations. -/
theorem fundamentalTheorem_periodic_proportional
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hNonRepA : ∀ j₁ j₂ : Fin rA, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (A j₁) (A j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin rB, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (B k₁) (B k₂))
    (hOverlap : PeriodicOverlapHypothesis A B) :
    PeriodicBlockMatchingWitness (d := d) A B := by
  classical
  -- Step 1: Matching function from A-blocks to B-blocks.
  let fA : Fin rA → Fin rB := fun j => (hOverlap.exists_nondecaying_A j).choose
  have hfA_nd : ∀ j,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j) (B (fA j)) N)
        Filter.atTop (nhds 0) :=
    fun j => (hOverlap.exists_nondecaying_A j).choose_spec
  -- Step 2: HetRepeatedBlocks from overlap dichotomy.
  have hfA_rep : ∀ j, HetRepeatedBlocks (A j) (B (fA j)) :=
    fun j => hOverlap.hetRepeatedBlocks_of_nondecaying j (fA j) (hfA_nd j)
  -- Step 3: fA is injective.
  -- If fA(j₁) = fA(j₂) with j₁ ≠ j₂, then A j₁ ~ B(fA j₁) and A j₂ ~ B(fA j₂) = B(fA j₁).
  -- By symmetry + transitivity: A j₁ ~ B(fA j₁) ~ A j₂, i.e., HetRepeatedBlocks (A j₁) (A j₂).
  -- This contradicts hNonRepA.
  have hfA_inj : Function.Injective fA := by
    intro j₁ j₂ hfj
    by_contra hne
    have h₁ := hfA_rep j₁         -- A j₁ ~ B(fA j₁)
    have h₂ := (hfA_rep j₂).symm  -- B(fA j₂) ~ A j₂
    have h₂' : HetRepeatedBlocks (B (fA j₁)) (A j₂) := hfj ▸ h₂
    exact hNonRepA j₁ j₂ hne (h₁.trans h₂')
  -- Step 4: Matching function from B-blocks to A-blocks, also injective.
  let gB : Fin rB → Fin rA := fun k => (hOverlap.exists_nondecaying_B k).choose
  have hgB_nd : ∀ k,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A (gB k)) (B k) N)
        Filter.atTop (nhds 0) :=
    fun k => (hOverlap.exists_nondecaying_B k).choose_spec
  have hgB_rep : ∀ k, HetRepeatedBlocks (A (gB k)) (B k) :=
    fun k => hOverlap.hetRepeatedBlocks_of_nondecaying (gB k) k (hgB_nd k)
  have hgB_inj : Function.Injective gB := by
    intro k₁ k₂ hgk
    by_contra hne
    have h₁ := (hgB_rep k₁).symm  -- B k₁ ~ A(gB k₁)
    have h₂ := hgB_rep k₂          -- A(gB k₂) ~ B k₂
    have h₂' : HetRepeatedBlocks (A (gB k₁)) (B k₂) := hgk ▸ h₂
    exact hNonRepB k₁ k₂ hne (h₁.trans h₂')
  -- Step 5: rA = rB from injective maps between finite types.
  have hrA_le_rB : Fintype.card (Fin rA) ≤ Fintype.card (Fin rB) :=
    Fintype.card_le_of_injective fA hfA_inj
  have hrB_le_rA : Fintype.card (Fin rB) ≤ Fintype.card (Fin rA) :=
    Fintype.card_le_of_injective gB hgB_inj
  simp only [Fintype.card_fin] at hrA_le_rB hrB_le_rA
  have hrAB : rA = rB := le_antisymm hrA_le_rB hrB_le_rA
  refine ⟨hrAB, ?_⟩
  subst hrAB
  -- fA is injective on Fin rA, hence bijective; build the permutation.
  have hfA_bij : Function.Bijective fA :=
    ⟨hfA_inj, Finite.injective_iff_surjective.mp hfA_inj⟩
  exact ⟨Equiv.ofBijective fA hfA_bij, fun j => by
    simpa only [Equiv.ofBijective_apply] using hfA_rep j⟩

/-- **Theorem 3.4 (Periodic FT, proportional case) from `IsPeriodic` data.**

API variant of `fundamentalTheorem_periodic_proportional` that no longer takes
`PeriodicOverlapHypothesis` as a parameter; instead, the dichotomy field is filled via
`periodicOverlapDichotomy` (PR #573). The caller only needs to supply `IsPeriodic` data
plus the existence of non-decaying cross-family overlaps (the content of proportional
MPVs).

This is the form intended by the paper: two families of periodic blocks whose cross
overlaps do not all vanish must match up to bijection and per-block `HetRepeatedBlocks`
equivalence.

**Remaining proof obligations.** `periodicOverlapDichotomy` is stated and callable, but
its proof in `TNLean/MPS/Periodic/Overlap.lean` still contains several
admitted sub-lemmas. Downstream users of this theorem inherit those obligations — this
variant is a convenience wrapper, not an unconditional strengthening. -/
theorem fundamentalTheorem_periodic_proportional_of_isPeriodic
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (periodA : Fin rA → ℕ) (periodB : Fin rB → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hNonRepA : ∀ j₁ j₂ : Fin rA, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (A j₁) (A j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin rB, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (B k₁) (B k₂))
    (hExA : ∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N)
        Filter.atTop (nhds 0))
    (hExB : ∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N)
        Filter.atTop (nhds 0)) :
    PeriodicBlockMatchingWitness (d := d) A B :=
  fundamentalTheorem_periodic_proportional A B hNonRepA hNonRepB
    (PeriodicOverlapHypothesis.ofIsPeriodic A B periodA periodB hPerA hPerB hExA hExB)

end ProportionalCase

/-! ## Z-gauge construction helpers (Theorem 3.8 steps 5–7) -/

section ZGaugeAssembly

/-- **Z-gauge diagonal from matched m-th powers (Theorem 3.8, step 7).**

If two weight families have equal `m`-th powers and the denominators are nonzero, the
Z-gauge diagonal `Z = diag(μ_i/ν_i)` satisfies `Z^m = 1` and `Z · diag(ν) = diag(μ)`.

Assembles `zGaugeDiagonal_pow_eq_one` and `zGaugeDiagonal_mul_diagonal`. -/
theorem zgauge_construction
    {n : Type*} [Fintype n] [DecidableEq n]
    (m : ℕ) (μ ν : n → ℂ)
    (hpow : ∀ i, μ i ^ m = ν i ^ m)
    (hν : ∀ i, ν i ≠ 0) :
    ∃ Z : Matrix n n ℂ,
      Z ^ m = 1 ∧
      Z * Matrix.diagonal ν = Matrix.diagonal μ :=
  ⟨zGaugeDiagonal μ ν,
   zGaugeDiagonal_pow_eq_one m μ ν hpow hν,
   zGaugeDiagonal_mul_diagonal μ ν hν⟩

/-- **Per-block Z-gauge (Theorem 3.8, step 7 instantiated for `Fin r`).**

Convenience wrapper: given matched sector weights indexed by `Fin r` whose `m`-th powers
agree and whose denominators are nonzero, produces the diagonal Z-gauge matrix. -/
theorem perBlock_zgauge_of_power_eq
    {r : ℕ} (m : ℕ) (μ ν : Fin r → ℂ)
    (hpow : ∀ i, μ i ^ m = ν i ^ m)
    (hν : ∀ i, ν i ≠ 0) :
    ∃ Z : Matrix (Fin r) (Fin r) ℂ,
      Z ^ m = 1 ∧
      Z * Matrix.diagonal ν = Matrix.diagonal μ :=
  zgauge_construction m μ ν hpow hν

/-- **Weight multiset recovery via Newton-Girard (Theorem 3.8, step 6).**

If two weight families have equal power sums for all positive exponents, they determine
the same multiset. Direct wrapper around `power_sum_eq_implies_multiset_eq`. -/
theorem weight_multisets_eq_of_power_sums_eq
    {r : ℕ} (μ ν : Fin r → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i : Fin r, μ i ^ k = ∑ i : Fin r, ν i ^ k) :
    Finset.univ.val.map μ = Finset.univ.val.map ν :=
  power_sum_eq_implies_multiset_eq r μ ν h

/-- **Full Z-gauge pipeline (Theorem 3.8, steps 5–7 composed).**

Given two sector weight families where:
1. The `m`-th powers agree pointwise,
2. The denominators are nonzero,
3. Power sums agree for all positive exponents,

produces: weight multiset equality, a diagonal Z with `Z^m = 1`, and `Z · diag(ν) = diag(μ)`.

In the full Theorem 3.8 proof, hypothesis (3) follows from BNT linear independence + equal
MPVs (via `power_sums_eq_of_eventually_eq`), and hypothesis (1) is the Newton-Girard
consequence of (3) restricted to multiples of `m`. -/
theorem equalCase_zgauge_pipeline
    {r : ℕ} (m : ℕ) (μ ν : Fin r → ℂ)
    (hν : ∀ i, ν i ≠ 0)
    (hPow : ∀ i, μ i ^ m = ν i ^ m)
    (hPS : ∀ k : ℕ, 0 < k → ∑ i : Fin r, μ i ^ k = ∑ i : Fin r, ν i ^ k) :
    ∃ Z : Matrix (Fin r) (Fin r) ℂ,
      Z ^ m = 1 ∧
      Z * Matrix.diagonal ν = Matrix.diagonal μ ∧
      Finset.univ.val.map μ = Finset.univ.val.map ν :=
  let ⟨Z, hZm, hZmul⟩ := zgauge_construction m μ ν hPow hν
  ⟨Z, hZm, hZmul, weight_multisets_eq_of_power_sums_eq μ ν hPS⟩

end ZGaugeAssembly

/-! ## Theorem 3.8 — Equal case assembly (arXiv:1708.00029)

The equal-case Fundamental Theorem of MPS in irreducible form composes:

1. **Theorem 3.4** (`fundamentalTheorem_periodic_proportional`): block matching.
2. **Z-gauge pipeline** (`equalCase_zgauge_pipeline`): Newton–Girard + Z-gauge diagonal.

**Conditional on #81**: The `PeriodicOverlapHypothesis` and per-block weight power
equality hypotheses will be discharged once the periodic overlap dichotomy (Proposition
3.3) and coefficient extraction infrastructure are formalized. The Z-gauge construction
itself is fully proved.
-/

section EqualCase

variable {D₁ D₂ : ℕ}

/-- **Theorem 3.8, Step 1: Block matching.**

If two tensors in irreducible form with non-repeating blocks satisfy the periodic overlap
dichotomy, their bases of periodic tensors match: equal block counts, a bijection, and
per-block `HetRepeatedBlocks` equivalence.

Convenience wrapper around `fundamentalTheorem_periodic_proportional` that extracts block
families from `IsIrreducibleForm`.

**Conditional on #81**: The `PeriodicOverlapHypothesis` parameter will be discharged once
the periodic overlap dichotomy (Proposition 3.3) is formalized. -/
theorem fundamentalTheorem_periodic_equalCase_matching
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsIrreducibleForm A) (hB : IsIrreducibleForm B)
    (hNonRepA : ∀ j₁ j₂ : Fin hA.r, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (hA.blocks j₁) (hA.blocks j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin hB.r, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (hB.blocks k₁) (hB.blocks k₂))
    (hOverlap : PeriodicOverlapHypothesis hA.blocks hB.blocks) :
    PeriodicBlockMatchingWitness (d := d) hA.blocks hB.blocks :=
  fundamentalTheorem_periodic_proportional hA.blocks hB.blocks
    hNonRepA hNonRepB hOverlap

/-- **Theorem 3.8: Periodic FT, equal case (arXiv:1708.00029).**

If two MPS tensors in irreducible form with non-repeating blocks satisfy the periodic
overlap dichotomy and per-block weight power equality, then:

1. **Block matching**: equal block counts, a bijection, and per-block `HetRepeatedBlocks`.
2. **Per-block Z-gauge**: for each matched pair with period `m_j`, there exists a diagonal
   `Z_j` with `Z_j^{m_j} = 1` and `Z_j * diag(μB_{perm j}) = diag(μA_j)`.
3. **Weight multiset equality**: `μA_j` and `μB_{perm j}` determine the same multiset.

This composes Theorem 3.4 with the Z-gauge pipeline from PR #94.

**Conditional on #81**: The `PeriodicOverlapHypothesis` and `hPowEq` hypotheses will be
discharged once the periodic overlap dichotomy and coefficient extraction infrastructure
are formalized. The Z-gauge construction itself (`equalCase_zgauge_pipeline`) is fully
proved. -/
theorem fundamentalTheorem_periodic_equalCase
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsIrreducibleForm A) (hB : IsIrreducibleForm B)
    (hNonRepA : ∀ j₁ j₂ : Fin hA.r, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (hA.blocks j₁) (hA.blocks j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin hB.r, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (hB.blocks k₁) (hB.blocks k₂))
    (hOverlap : PeriodicOverlapHypothesis hA.blocks hB.blocks)
    (hPowEq : ∀ (perm : Fin hA.r ≃ Fin hB.r),
      (∀ j, HetRepeatedBlocks (hA.blocks j) (hB.blocks (perm j))) →
      ∀ j N, 0 < N → (hA.μ j) ^ N = (hB.μ (perm j)) ^ N)
    (hμB_ne : ∀ k, hB.μ k ≠ 0) :
    -- Block matching:
    ∃ (_ : hA.r = hB.r) (perm : Fin hA.r ≃ Fin hB.r),
      -- Per-block HetRepeatedBlocks:
      (∀ j, HetRepeatedBlocks (hA.blocks j) (hB.blocks (perm j))) ∧
      -- Per-block Z-gauge + weight multiset equality:
      (∀ j, ∃ Z : Matrix (Fin 1) (Fin 1) ℂ,
        Z ^ (hA.period j) = 1 ∧
        Z * Matrix.diagonal (fun _ : Fin 1 => hB.μ (perm j)) =
          Matrix.diagonal (fun _ : Fin 1 => hA.μ j) ∧
        ({hA.μ j} : Multiset ℂ) = {hB.μ (perm j)}) := by
  -- Step 1: Block matching via Theorem 3.4.
  obtain ⟨hrAB, perm, hRep⟩ :=
    fundamentalTheorem_periodic_equalCase_matching A B hA hB hNonRepA hNonRepB hOverlap
  refine ⟨hrAB, perm, hRep, fun j => ?_⟩
  -- Step 2: Per-block weight power equality from hypothesis.
  have hPowEqJ : ∀ N : ℕ, 0 < N → (hA.μ j) ^ N = (hB.μ (perm j)) ^ N :=
    hPowEq perm hRep j
  -- Step 3: Z-gauge construction from matched weights.
  have hPow_period : (hA.μ j) ^ (hA.period j) = (hB.μ (perm j)) ^ (hA.period j) :=
    hPowEqJ (hA.period j) (hA.periodic j).period_pos
  obtain ⟨Z, hZpow, hZmul, hMultiset⟩ :=
    equalCase_zgauge_pipeline (hA.period j)
      (fun _ : Fin 1 => hA.μ j) (fun _ : Fin 1 => hB.μ (perm j))
      (fun _ => hμB_ne (perm j))
      (fun _ => hPow_period)
      (fun k hk => by simp only [Fin.sum_univ_one, hPowEqJ k hk])
  refine ⟨Z, hZpow, hZmul, ?_⟩
  -- Convert Finset.univ.val.map to multiset singleton equality.
  simp only [Finset.univ_unique] at hMultiset
  exact hMultiset

end EqualCase

end MPSTensor
