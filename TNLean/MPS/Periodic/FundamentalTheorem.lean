/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.FundamentalTheorem.Full
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Periodic.Overlap
import TNLean.MPS.Periodic.ZGauge
import TNLean.MPS.SharedInfra.Scaling

open scoped Matrix BigOperators

/-!
# Periodic Fundamental Theorem of MPS (arXiv:1708.00029, Section 3)

This file formalizes the periodic fundamental theorem of arXiv:1708.00029 Section 3 and the
Z-gauge theory used in its equal-case strengthening:

* **Theorem 3.4** (`fundamentalTheorem_periodic_proportional`): If two non-repeating
  block families satisfy the periodic overlap dichotomy, their bases of periodic tensors
  match up to a bijection with per-block `RepeatedBlocks` equivalence. (In the paper,
  proportional MPVs imply the dichotomy; here it is a direct hypothesis.)

* **Supporting lemmas for Theorem 3.8**: The equal-case strengthening produces per-block
  Z-gauge data (diagonal Z with Z^m = 1) from the Newton–Girard identity on sector weights.
  The Z-gauge construction theorems (`zgauge_construction`, `perBlock_zgauge_of_power_eq`)
  combine the results from PR #94.

## Status of #81 (periodic overlap dichotomy)

Theorem 3.4 is stated in two forms:

* `fundamentalTheorem_periodic_proportional` takes a `PeriodicOverlapHypothesis` directly,
  leaving callers free to supply the dichotomy from any source.
* `fundamentalTheorem_periodic_proportional_of_isPeriodic` is a variant that no
  longer takes `PeriodicOverlapHypothesis` as a parameter: the
  `hetRepeatedBlocks_of_nondecaying` field is filled inside
  `PeriodicOverlapHypothesis.ofIsPeriodic` via `periodicOverlapDichotomy` (PR #573,
  partially addressing #81). Callers only need to supply per-block `IsPeriodic` data
  plus the existence of non-decaying cross-family overlaps (`exists_nondecaying_A/B`),
  which encode the paper's proportional-MPV assumption.

  **Caveat**: `periodicOverlapDichotomy` is stated and callable, but its proof still
  depends on admitted lemmas in the split periodic-overlap modules:
  `TNLean.MPS.Periodic.Overlap.SelfOverlap`,
  `TNLean.MPS.Periodic.Overlap.Case2`,
  `TNLean.MPS.Periodic.Overlap.Case3`, and
  `TNLean.MPS.Periodic.Overlap.Dichotomy`. Subsequent results using the
  `_of_isPeriodic` variant therefore inherit those proof obligations and should
  not be treated as unconditional.

The Z-gauge construction (Theorem 3.8 steps 5–7) is fully proved.

## Key references

* arXiv:1708.00029 (De las Cuevas–Schuch–Pérez-García–Cirac, 2017)
* `blocks_match_of_sameMPV₂_CFBNT` in `Full.lean` — structural template for Theorem 3.4
* Z-gauge construction lemmas in `ZGauge.lean` (PR #94)
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

/-- Hypothesis giving the periodic overlap dichotomy (Proposition 3.3 of 1708.00029).

The `hetRepeatedBlocks_of_nondecaying` field can be filled via `periodicOverlapDichotomy`
(see `PeriodicOverlapHypothesis.ofIsPeriodic`), though that dichotomy still relies on
admitted sub-lemmas in the split `TNLean.MPS.Periodic.Overlap.*` modules. The fields
capture the essential results:
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
its proof transitively depends on admitted lemmas in the split overlap development:
`TNLean.MPS.Periodic.Overlap.SelfOverlap` for self-overlap and cyclic-sector setup,
`TNLean.MPS.Periodic.Overlap.Case2` for the no-sector-match decay route,
`TNLean.MPS.Periodic.Overlap.Case3` for the sector-match repeated-block route, and
`TNLean.MPS.Periodic.Overlap.Dichotomy` for the final dichotomy and eventual
linear-independence packaging. Subsequent users of this constructor therefore inherit
those obligations and
should not treat the resulting `PeriodicOverlapHypothesis` as unconditionally proven. -/
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

/-- **Peripheral proportional case from exact MPV equality.**

If two periodic tensors generate the same MPV family, then their bond dimensions
agree and they are repeated blocks after identifying those bond spaces. This is
the single-block uniqueness direction behind Theorem 3.4 once the
proportionality scalar has been absorbed into one side.

The proof combines `periodicOverlapDichotomy` with `periodicSelfOverlap_tendsto`:
the decay branch would force the self-overlap of `A` to tend to `0`, contradicting
its periodic self-overlap limit `m_a` along the subsequence `m_a * ℕ`.

As with `periodicOverlapDichotomy`, this theorem currently inherits the admitted
sub-lemmas in `Periodic/Overlap`. -/
theorem peripheralProportionalCase_periodicFT_of_sameMPV
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hSame : SameMPV₂ A B) :
    HetRepeatedBlocks A B := by
  rcases periodicOverlapDichotomy A B hA hB with hDecay | ⟨hdim, hRep⟩
  · have hSameOverlap : ∀ N : ℕ, mpvOverlap (d := d) A B N = mpvOverlap A A N := by
      intro N
      unfold mpvOverlap
      refine Finset.sum_congr rfl ?_
      intro σ _
      rw [hSame N σ]
    have hSelfZero : Filter.Tendsto (fun N => mpvOverlap A A N) Filter.atTop (nhds 0) :=
      Filter.Tendsto.congr' (Filter.Eventually.of_forall hSameOverlap) hDecay
    have hMulAtTop : Filter.Tendsto (fun k : ℕ => m_a * k) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro n
      exact Filter.eventually_atTop.2 ⟨n, fun k hk => by
        have hm_a : 1 ≤ m_a := Nat.succ_le_of_lt hA.period_pos
        exact le_trans hk <| by simpa using Nat.mul_le_mul_right k hm_a⟩
    have hSelfZeroMul :
        Filter.Tendsto (fun k : ℕ => mpvOverlap A A (m_a * k)) Filter.atTop (nhds 0) :=
      hSelfZero.comp hMulAtTop
    have hm_ne : (m_a : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hA.period_pos
    exact False.elim <| hm_ne <|
      tendsto_nhds_unique (periodicSelfOverlap_tendsto A hA) hSelfZeroMul
  · exact ⟨hdim, hRep⟩

/-- **Phase-rescaling reduction for the peripheral proportional case.**

This Prop isolates the remaining scalar-absorption step behind
`peripheralProportionalCase_periodicFT_of_sameMPV`: whenever a periodic tensor
has an MPV family proportional to that of another tensor, one can rescale the
periodic side by a unit-modulus phase so that the MPV families agree exactly. -/
def PeripheralProportionalCaseRootFromRescaling (d D₁ D₂ : ℕ) : Prop :=
  ∀ {A : MPSTensor d D₁} {B : MPSTensor d D₂} {m_a : ℕ},
    IsPeriodic m_a A →
    ProportionalMPV₂ A B →
      ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ SameMPV₂ (fun i => ξ • A i) B

/-- **Peripheral proportional case from phase rescaling.**

Assuming `PeripheralProportionalCaseRootFromRescaling`, the exact-equality theorem
`peripheralProportionalCase_periodicFT_of_sameMPV` upgrades proportional periodic
MPVs to `HetRepeatedBlocks`. Thus the remaining single-block proportional gap in
Theorem 3.4 is exactly the phase-rescaling step provided by that hypothesis. -/
theorem peripheralProportionalCase_periodicFT_of_rootFromRescaling
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (hRescale : PeripheralProportionalCaseRootFromRescaling d D₁ D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hProp : ProportionalMPV₂ A B) :
    HetRepeatedBlocks A B := by
  obtain ⟨ξ, hξ, hSame⟩ := hRescale hA hProp
  let A' : MPSTensor d D₁ := fun i => ξ • A i
  have hA' : IsPeriodic m_a A' := by
    simpa [A'] using isPeriodic_smul_of_norm_one (c := ξ) hξ A hA
  have hScale : HetRepeatedBlocks A A' := by
    have hRep : RepeatedBlocks A' A := by
      refine ⟨ξ, 1, hξ, ?_⟩
      intro i
      simp [A']
    exact (HetRepeatedBlocks.of_repeatedBlocks hRep).symm
  have hRepeated : HetRepeatedBlocks A' B :=
    peripheralProportionalCase_periodicFT_of_sameMPV A' B hA' hB hSame
  exact hScale.trans hRepeated

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

The single-block proportional-to-equal reduction is now split explicitly.
`PeripheralProportionalCaseRootFromRescaling` provides the missing phase-rescaling
step, and `peripheralProportionalCase_periodicFT_of_rootFromRescaling` shows that,
once this step is available, the exact-MPV theorem
`peripheralProportionalCase_periodicFT_of_sameMPV` yields the heterogeneous
repeated-block conclusion. Thus the remaining mathematical gap is the multi-block
existence step that turns proportionality of the assembled tensors into the
non-decaying cross-overlap hypotheses `exists_nondecaying_A/B`.

The `PeriodicOverlapHypothesis` parameter can be supplied via
`PeriodicOverlapHypothesis.ofIsPeriodic`, which uses `periodicOverlapDichotomy`
(PR #573, partially addressing #81) to fill the `hetRepeatedBlocks_of_nondecaying`
field; see `fundamentalTheorem_periodic_proportional_of_isPeriodic`. Note that
`periodicOverlapDichotomy` still relies on several admitted sub-lemmas in the split
`TNLean.MPS.Periodic.Overlap.*` modules, so callers going through that route inherit
those obligations. -/
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

variant of `fundamentalTheorem_periodic_proportional` that no longer takes
`PeriodicOverlapHypothesis` as a parameter; instead, the dichotomy field is filled via
`periodicOverlapDichotomy` (PR #573). The caller only needs to supply `IsPeriodic` data
plus the existence of non-decaying cross-family overlaps (the content of proportional
MPVs).

This is the form intended by the paper: two families of periodic blocks whose cross
overlaps do not all vanish must match up to bijection and per-block `HetRepeatedBlocks`
equivalence.

**Remaining proof obligations.** `periodicOverlapDichotomy` is stated and callable, but
its proof in `TNLean/MPS/Periodic/Overlap.lean` still contains several
admitted sub-lemmas. Subsequent users of this theorem inherit those obligations — this
variant is a convenience reformulation, not an unconditional strengthening. -/
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

private lemma tendsto_zero_subseq_of_decomp_cross
    {r : ℕ} {dim : Fin r → ℕ}
    {Dtot Db : ℕ}
    (A_total : MPSTensor d Dtot)
    (A : (j : Fin r) → MPSTensor d (dim j))
    (coeff : ℕ → Fin r → ℂ)
    (lim : Fin r → ℂ)
    {m : ℕ}
    (hdecomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin r, coeff N j * mpv (A j) σ)
    (hcoeff : ∀ j,
      Filter.Tendsto (fun n => coeff (m * n) j) Filter.atTop (nhds (lim j)))
    (B : MPSTensor d Db)
    (hcross : ∀ j,
      Filter.Tendsto (fun n => mpvOverlap (d := d) (A j) B (m * n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => mpvOverlap (d := d) A_total B (m * n))
      Filter.atTop (nhds 0) := by
  have hEq : ∀ n,
      mpvOverlap (d := d) A_total B (m * n) =
        ∑ j : Fin r, coeff (m * n) j * mpvOverlap (d := d) (A j) B (m * n) := by
    intro n
    simpa only using
      (mpvOverlap_eq_sum_of_decomp_left (A_total := A_total) (A := A)
        (c := coeff (m * n)) (hdecomp := hdecomp (m * n)) (B := B))
  have hTerm : ∀ j : Fin r,
      Filter.Tendsto (fun n =>
        coeff (m * n) j * mpvOverlap (d := d) (A j) B (m * n))
        Filter.atTop (nhds 0) := by
    intro j
    have := (hcoeff j).mul (hcross j)
    simpa only [mul_zero] using this
  have hSum : Filter.Tendsto (fun n => ∑ j : Fin r,
      coeff (m * n) j * mpvOverlap (d := d) (A j) B (m * n))
        Filter.atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finset_sum Finset.univ (fun j _ => hTerm j))
  simpa only [hEq] using hSum

private lemma tendsto_focus_subseq_of_decomp
    {r : ℕ} {dim : Fin r → ℕ}
    {Dtot : ℕ}
    (A_total : MPSTensor d Dtot)
    (A : (j : Fin r) → MPSTensor d (dim j))
    (coeff : ℕ → Fin r → ℂ)
    (lim : Fin r → ℂ)
    {m : ℕ} (j : Fin r)
    (hdecomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ i : Fin r, coeff N i * mpv (A i) σ)
    (hcoeff : ∀ i,
      Filter.Tendsto (fun n => coeff (m * n) i) Filter.atTop (nhds (lim i)))
    (hSelf : Filter.Tendsto (fun n => mpvOverlap (d := d) (A j) (A j) (m * n))
      Filter.atTop (nhds (m : ℂ)))
    (hOff : ∀ i : Fin r, i ≠ j →
      Filter.Tendsto (fun n => mpvOverlap (d := d) (A i) (A j) (m * n))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => mpvOverlap (d := d) A_total (A j) (m * n))
      Filter.atTop (nhds (lim j * (m : ℂ))) := by
  have hEq : ∀ n,
      mpvOverlap (d := d) A_total (A j) (m * n) =
        ∑ i : Fin r, coeff (m * n) i * mpvOverlap (d := d) (A i) (A j) (m * n) := by
    intro n
    simpa only using
      (mpvOverlap_eq_sum_of_decomp_left (A_total := A_total) (A := A)
        (c := coeff (m * n)) (hdecomp := hdecomp (m * n)) (B := A j))
  have hTerm : ∀ i : Fin r,
      Filter.Tendsto (fun n =>
        coeff (m * n) i * mpvOverlap (d := d) (A i) (A j) (m * n))
        Filter.atTop (nhds (if i = j then lim j * (m : ℂ) else 0)) := by
    intro i
    by_cases hij : i = j
    · cases hij
      have := (hcoeff j).mul hSelf
      simpa only [↓reduceIte] using this
    · have := (hcoeff i).mul (hOff i hij)
      simpa only [hij, ↓reduceIte, mul_zero] using this
  have hSum := tendsto_finset_sum Finset.univ (fun i _ => hTerm i)
  have hRhs : (∑ i : Fin r, if i = j then lim j * (m : ℂ) else 0) =
      lim j * (m : ℂ) := by
    simp
  simpa only [hEq, hRhs] using hSum

private theorem exists_nondecaying_overlap_ofProportionalDecomp_core
    {rX rY : ℕ}
    {dimX : Fin rX → ℕ} {dimY : Fin rY → ℕ}
    {Dzero Dfocus : ℕ}
    [∀ y, NeZero (dimY y)]
    (X : (x : Fin rX) → MPSTensor d (dimX x))
    (Y : (y : Fin rY) → MPSTensor d (dimY y))
    (periodY : Fin rY → ℕ)
    (hPerY : ∀ y, IsPeriodic (periodY y) (Y y))
    (hNonRepY : ∀ y₁ y₂ : Fin rY, y₁ ≠ y₂ →
      ¬ HetRepeatedBlocks (Y y₁) (Y y₂))
    (zero_total : MPSTensor d Dzero)
    (focus_total : MPSTensor d Dfocus)
    (xCoeff : ℕ → Fin rX → ℂ)
    (yCoeff : ℕ → Fin rY → ℂ)
    (xLim : Fin rX → ℂ)
    (yLim : Fin rY → ℂ)
    (hZero_decomp : ∀ N (σ : Fin N → Fin d),
      mpv zero_total σ = ∑ x : Fin rX, xCoeff N x * mpv (X x) σ)
    (hFocus_decomp : ∀ N (σ : Fin N → Fin d),
      mpv focus_total σ = ∑ y : Fin rY, yCoeff N y * mpv (Y y) σ)
    (hxCoeff : ∀ x, Filter.Tendsto (fun N => xCoeff N x) Filter.atTop
      (nhds (xLim x)))
    (hyCoeff : ∀ y, Filter.Tendsto (fun N => yCoeff N y) Filter.atTop
      (nhds (yLim y)))
    (hyLim_ne : ∀ y, yLim y ≠ 0)
    (hContradict : ∀ (y : Fin rY) {m : ℕ},
      0 < m →
      Filter.Tendsto (fun n : ℕ => m * n) Filter.atTop Filter.atTop →
      Filter.Tendsto (fun n => mpvOverlap (d := d) zero_total (Y y) (m * n))
        Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => mpvOverlap (d := d) focus_total (Y y) (m * n))
        Filter.atTop (nhds (yLim y * (m : ℂ))) →
      yLim y * (m : ℂ) ≠ 0 →
      False) :
    ∀ y : Fin rY, ∃ x : Fin rX,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (X x) (Y y) N)
        Filter.atTop (nhds 0) := by
  classical
  intro y
  by_contra hall
  push Not at hall
  let m := periodY y
  have hm_pos : 0 < m := (hPerY y).period_pos
  have hMulAtTop : Filter.Tendsto (fun n : ℕ => m * n) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop' hm_pos
  have hxCoeff_mul : ∀ x, Filter.Tendsto (fun n => xCoeff (m * n) x) Filter.atTop
      (nhds (xLim x)) := fun x => (hxCoeff x).comp hMulAtTop
  have hyCoeff_mul : ∀ y', Filter.Tendsto (fun n => yCoeff (m * n) y') Filter.atTop
      (nhds (yLim y')) := fun y' => (hyCoeff y').comp hMulAtTop
  have hall_mul : ∀ x,
      Filter.Tendsto (fun n => mpvOverlap (d := d) (X x) (Y y) (m * n))
        Filter.atTop (nhds 0) := fun x => (hall x).comp hMulAtTop
  have hZero0 : Filter.Tendsto (fun n => mpvOverlap (d := d) zero_total (Y y) (m * n))
      Filter.atTop (nhds 0) :=
    tendsto_zero_subseq_of_decomp_cross (A_total := zero_total) (A := X)
      (coeff := xCoeff) (lim := xLim) (m := m) hZero_decomp hxCoeff_mul (Y y) hall_mul
  have hSelf : Filter.Tendsto (fun n => mpvOverlap (d := d) (Y y) (Y y) (m * n))
      Filter.atTop (nhds (m : ℂ)) := by
    simpa [m] using periodicSelfOverlap_tendsto (A := Y y) (hP := hPerY y)
  have hOff : ∀ y' : Fin rY, y' ≠ y →
      Filter.Tendsto (fun n => mpvOverlap (d := d) (Y y') (Y y) (m * n))
        Filter.atTop (nhds 0) := by
    intro y' hy'
    rcases periodicOverlapDichotomy (Y y') (Y y) (hPerY y') (hPerY y) with hDecay | hRep
    · exact hDecay.comp hMulAtTop
    · exact False.elim (hNonRepY y' y hy' hRep)
  have hFocus_lim : Filter.Tendsto
      (fun n => mpvOverlap (d := d) focus_total (Y y) (m * n))
      Filter.atTop (nhds (yLim y * (m : ℂ))) :=
    tendsto_focus_subseq_of_decomp (A_total := focus_total) (A := Y)
      (coeff := yCoeff) (lim := yLim) (m := m) y hFocus_decomp hyCoeff_mul hSelf hOff
  have hm_ne : (m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm_pos
  have hFocus_ne : yLim y * (m : ℂ) ≠ 0 := by
    exact mul_ne_zero (hyLim_ne y) hm_ne
  exact hContradict y (m := m) hm_pos hMulAtTop hZero0 hFocus_lim hFocus_ne

private theorem exists_nondecaying_overlap_ofProportionalDecomp_right
    {DtotA DtotB : ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (periodB : Fin rB → ℕ)
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hNonRepB : ∀ k₁ k₂ : Fin rB, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (B k₁) (B k₂))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ)
    (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ)
    (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ)
    (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, aCoeff N j * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, bCoeff N k * mpv (B k) σ)
    (haCoeff : ∀ j, Filter.Tendsto (fun N => aCoeff N j) Filter.atTop
      (nhds (aLim j)))
    (hbCoeff : ∀ k, Filter.Tendsto (fun N => bCoeff N k) Filter.atTop
      (nhds (bLim k)))
    (_haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = c N * mpv B_total σ)
    (hc : Filter.Tendsto c Filter.atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∀ k : Fin rB, ∃ j : Fin rA,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N)
        Filter.atTop (nhds 0) := by
  refine
    exists_nondecaying_overlap_ofProportionalDecomp_core (X := A) (Y := B)
      (periodY := periodB) hPerB hNonRepB (zero_total := A_total)
      (focus_total := B_total) (xCoeff := aCoeff) (yCoeff := bCoeff)
      (xLim := aLim) (yLim := bLim) hA_decomp hB_decomp haCoeff hbCoeff hbLim_ne ?_
  intro k m _hm_pos hMulAtTop hA0 hB_overlap_lim hB_lim_ne
  have hc_mul : Filter.Tendsto (fun n => c (m * n)) Filter.atTop (nhds cLim) :=
    hc.comp hMulAtTop
  have hEqProp : ∀ n,
      mpvOverlap (d := d) A_total (B k) (m * n) =
        c (m * n) * mpvOverlap (d := d) B_total (B k) (m * n) := by
    intro n
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (A := A_total) (B := B_total)
      (c := c (m * n)) (h := hProp (m * n)) (C := B k)
  have hAB_overlap_lim : Filter.Tendsto (fun n => mpvOverlap (d := d) A_total (B k) (m * n))
      Filter.atTop (nhds (cLim * (bLim k * (m : ℂ)))) := by
    have := hc_mul.mul hB_overlap_lim
    refine this.congr ?_
    intro n
    simp [hEqProp n]
  have hAB_ne : cLim * (bLim k * (m : ℂ)) ≠ 0 :=
    mul_ne_zero hcLim_ne hB_lim_ne
  exact (hAB_overlap_lim.ne_nhds hAB_ne) hA0

private theorem exists_nondecaying_overlap_ofProportionalDecomp_left
    {DtotA DtotB : ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (periodA : Fin rA → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hNonRepA : ∀ j₁ j₂ : Fin rA, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (A j₁) (A j₂))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ)
    (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ)
    (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ)
    (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, aCoeff N j * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, bCoeff N k * mpv (B k) σ)
    (haCoeff : ∀ j, Filter.Tendsto (fun N => aCoeff N j) Filter.atTop
      (nhds (aLim j)))
    (hbCoeff : ∀ k, Filter.Tendsto (fun N => bCoeff N k) Filter.atTop
      (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (_hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = c N * mpv B_total σ)
    (hc : Filter.Tendsto c Filter.atTop (nhds cLim))
    (_hcLim_ne : cLim ≠ 0) :
    ∀ j : Fin rA, ∃ k : Fin rB,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N)
        Filter.atTop (nhds 0) := by
  classical
  have hSwapped : ∀ j : Fin rA, ∃ k : Fin rB,
      ¬ Filter.Tendsto (fun N => mpvOverlap (d := d) (B k) (A j) N)
        Filter.atTop (nhds 0) := by
    refine
      exists_nondecaying_overlap_ofProportionalDecomp_core (X := B) (Y := A)
        (periodY := periodA) hPerA hNonRepA (zero_total := B_total)
        (focus_total := A_total) (xCoeff := bCoeff) (yCoeff := aCoeff)
        (xLim := bLim) (yLim := aLim) hB_decomp hA_decomp hbCoeff haCoeff haLim_ne ?_
    intro j m _hm_pos hMulAtTop hB0 hA_overlap_lim hA_lim_ne
    have hc_mul : Filter.Tendsto (fun n => c (m * n)) Filter.atTop (nhds cLim) :=
      hc.comp hMulAtTop
    have hEqProp : ∀ n,
        mpvOverlap (d := d) A_total (A j) (m * n) =
          c (m * n) * mpvOverlap (d := d) B_total (A j) (m * n) := by
      intro n
      exact mpvOverlap_eq_mul_of_mpv_eq_mul (A := A_total) (B := B_total)
        (c := c (m * n)) (h := hProp (m * n)) (C := A j)
    have hA0 : Filter.Tendsto (fun n => mpvOverlap (d := d) A_total (A j) (m * n))
        Filter.atTop (nhds 0) := by
      have hmul :
          Filter.Tendsto
            (fun n => c (m * n) * mpvOverlap (d := d) B_total (A j) (m * n))
            Filter.atTop (nhds 0) := by
        simpa only [mul_zero] using hc_mul.mul hB0
      refine hmul.congr ?_
      intro n
      simp [hEqProp n]
    exact (hA_overlap_lim.ne_nhds hA_lim_ne) hA0
  intro j
  obtain ⟨k, hk⟩ := hSwapped j
  exact ⟨k, fun h => hk (tendsto_mpvOverlap_zero_swap (A := A j) (B := B k) h)⟩

/-- **Build `PeriodicOverlapHypothesis` from proportional split-data.**

This provides the missing multi-block step for the proportional periodic FT.
Given periodic block families together with explicit decompositions of two total
MPV families into those blocks, coefficient arrays converging to nonzero limits,
and proportionality of the total MPVs, the non-decaying cross-overlap witnesses
`exists_nondecaying_A/B` follow automatically. The dichotomy field is then filled
by `PeriodicOverlapHypothesis.ofIsPeriodic`.

The remaining paper-level input is therefore sharply isolated in the split-data
hypotheses `hA_decomp`, `hB_decomp`, `haCoeff`, `hbCoeff`, and `hProp`. -/
def PeriodicOverlapHypothesis.ofProportionalDecomp
    {DtotA DtotB : ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (periodA : Fin rA → ℕ)
    (periodB : Fin rB → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hNonRepA : ∀ j₁ j₂ : Fin rA, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (A j₁) (A j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin rB, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (B k₁) (B k₂))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ)
    (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ)
    (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ)
    (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, aCoeff N j * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, bCoeff N k * mpv (B k) σ)
    (haCoeff : ∀ j, Filter.Tendsto (fun N => aCoeff N j) Filter.atTop
      (nhds (aLim j)))
    (hbCoeff : ∀ k, Filter.Tendsto (fun N => bCoeff N k) Filter.atTop
      (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = c N * mpv B_total σ)
    (hc : Filter.Tendsto c Filter.atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    PeriodicOverlapHypothesis A B :=
  PeriodicOverlapHypothesis.ofIsPeriodic A B periodA periodB hPerA hPerB
    (exists_nondecaying_overlap_ofProportionalDecomp_left A B periodA hPerA hNonRepA
      A_total B_total aCoeff bCoeff aLim bLim c cLim hA_decomp hB_decomp haCoeff hbCoeff
      haLim_ne hbLim_ne hProp hc hcLim_ne)
    (exists_nondecaying_overlap_ofProportionalDecomp_right A B periodB hPerB hNonRepB
      A_total B_total aCoeff bCoeff aLim bLim c cLim hA_decomp hB_decomp haCoeff hbCoeff
      haLim_ne hbLim_ne hProp hc hcLim_ne)

/-- **Split-data proportional periodic FT (Theorem 3.4, multi-block step).**

This theorem converts proportional split-data for two periodic block families into the
`PeriodicOverlapHypothesis` needed by `fundamentalTheorem_periodic_proportional`.
It is the current culminating theorem for the multi-block proportional-case argument:
all overlap-dichotomy consequences are discharged internally, while the remaining
residual hypothesis is the explicit coefficient-convergence / proportionality data
for the assembled tensors.

As with `PeriodicOverlapHypothesis.ofIsPeriodic`, this theorem inherits the admitted
sub-lemmas behind `periodicOverlapDichotomy` and `periodicSelfOverlap_tendsto`. -/
theorem fundamentalTheorem_periodic_proportional_ofProportionalDecomp
    {DtotA DtotB : ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (periodA : Fin rA → ℕ)
    (periodB : Fin rB → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hNonRepA : ∀ j₁ j₂ : Fin rA, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (A j₁) (A j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin rB, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (B k₁) (B k₂))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ)
    (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ)
    (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ)
    (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, aCoeff N j * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, bCoeff N k * mpv (B k) σ)
    (haCoeff : ∀ j, Filter.Tendsto (fun N => aCoeff N j) Filter.atTop
      (nhds (aLim j)))
    (hbCoeff : ∀ k, Filter.Tendsto (fun N => bCoeff N k) Filter.atTop
      (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = c N * mpv B_total σ)
    (hc : Filter.Tendsto c Filter.atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    PeriodicBlockMatchingWitness (d := d) A B :=
  fundamentalTheorem_periodic_proportional A B hNonRepA hNonRepB
    (PeriodicOverlapHypothesis.ofProportionalDecomp A B periodA periodB hPerA hPerB
      hNonRepA hNonRepB A_total B_total aCoeff bCoeff aLim bLim c cLim hA_decomp
      hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne)

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

Convenience reformulation: given matched sector weights indexed by `Fin r` whose `m`-th powers
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
the same multiset. Direct reformulation of `power_sum_eq_implies_multiset_eq`. -/
theorem weight_multisets_eq_of_power_sums_eq
    {r : ℕ} (μ ν : Fin r → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i : Fin r, μ i ^ k = ∑ i : Fin r, ν i ^ k) :
    Finset.univ.val.map μ = Finset.univ.val.map ν :=
  power_sum_eq_implies_multiset_eq r μ ν h

/-- **Full Z-gauge construction (Theorem 3.8, steps 5–7 composed).**

Given two sector weight families where:
1. The `m`-th powers agree pointwise,
2. The denominators are nonzero,
3. Power sums agree for all positive exponents,

produces: weight multiset equality, a diagonal Z with `Z^m = 1`, and `Z · diag(ν) = diag(μ)`.

In the full Theorem 3.8 proof, hypothesis (3) follows from BNT linear independence + equal
MPVs (via `power_sums_eq_of_eventually_eq`), and hypothesis (1) is the Newton-Girard
consequence of (3) restricted to multiples of `m`. -/
theorem equalCase_zgauge_of_power_sums
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
2. **Z-gauge construction** (`equalCase_zgauge_of_power_sums`): Newton–Girard + Z-gauge diagonal.

**Conditional on #81**: The `PeriodicOverlapHypothesis` and per-block weight power
equality hypotheses will be discharged once the periodic overlap dichotomy (Proposition
3.3) and coefficient extraction theory are formalized. The Z-gauge construction
itself is fully proved.
-/

section EqualCase

variable {D₁ D₂ : ℕ}

/-- **Theorem 3.8, Step 1: Block matching.**

If two tensors in irreducible form with non-repeating blocks satisfy the periodic overlap
dichotomy, their bases of periodic tensors match: equal block counts, a bijection, and
per-block `HetRepeatedBlocks` equivalence.

Convenience reformulation of `fundamentalTheorem_periodic_proportional` that extracts block
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

This composes Theorem 3.4 with the Z-gauge construction from PR #94.

**Conditional on #81**: The `PeriodicOverlapHypothesis` and `hPowEq` hypotheses will be
discharged once the periodic overlap dichotomy and coefficient extraction theory
are formalized. The Z-gauge construction itself (`equalCase_zgauge_of_power_sums`) is fully
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
    equalCase_zgauge_of_power_sums (hA.period j)
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
