/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.FundamentalTheorem.Full
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

## Dependency on #81

Theorem 3.4 depends on the periodic overlap dichotomy (Proposition 3.3, issue #81). Since
#81 is not yet merged, the theorem is stated conditionally on `PeriodicOverlapHypothesis`.
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

/-! ## Periodic overlap dichotomy hypothesis (conditional on #81) -/

/-- Hypothesis packaging the periodic overlap dichotomy (Proposition 3.3 of 1708.00029).

This will be discharged once #81 is merged. The fields capture the essential results:
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

**Conditional on #81**: The `PeriodicOverlapHypothesis` parameter will be discharged once
the periodic overlap dichotomy (Proposition 3.3) is formalized. -/
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
    simpa [Equiv.ofBijective_apply] using hfA_rep j⟩

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
2. **MPV expansion** (`mpv_toTensorFromBlocks_eq_sum`): expands `SameMPV₂` into
   per-block coefficient identities.
3. **Linear independence** (`periodicBasis_eventuallyLinearlyIndependent`): extracts
   per-block coefficient equality from the expansion.
4. **Z-gauge pipeline** (`equalCase_zgauge_pipeline`): Newton–Girard + Z-gauge diagonal.

**Conditional on #81**: Steps 1 and 3 depend on the periodic overlap dichotomy via
`PeriodicOverlapHypothesis` and `periodicOverlapDichotomy` (both sorry'd in
`PeriodicOverlap.lean`).
-/

section EqualCase

variable {D₁ D₂ : ℕ}

/-- **Theorem 3.8, Step 1: Block matching from equal MPVs.**

If two tensors in irreducible form with non-repeating blocks generate equal MPV families,
their bases of periodic tensors match: equal block counts, a bijection, and per-block
`HetRepeatedBlocks` equivalence.

Applies Theorem 3.4 (`fundamentalTheorem_periodic_proportional`).

**Conditional on #81**: Uses `sorry` for `PeriodicOverlapHypothesis`. -/
theorem fundamentalTheorem_periodic_equalCase_matching
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsIrreducibleForm A) (hB : IsIrreducibleForm B)
    (hNonRepA : ∀ j₁ j₂ : Fin hA.r, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (hA.blocks j₁) (hA.blocks j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin hB.r, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (hB.blocks k₁) (hB.blocks k₂))
    (hSame : SameMPV₂ A B) :
    PeriodicBlockMatchingWitness (d := d) hA.blocks hB.blocks := by
  -- Derive SameMPV₂ at the block-assembly level.
  have _hAssembly : SameMPV₂
      (toTensorFromBlocks hA.μ hA.blocks)
      (toTensorFromBlocks hB.μ hB.blocks) := by
    intro N σ
    calc mpv (toTensorFromBlocks hA.μ hA.blocks) σ
        = mpv A σ := (hA.sameMPV N σ).symm
      _ = mpv B σ := hSame N σ
      _ = mpv (toTensorFromBlocks hB.μ hB.blocks) σ := hB.sameMPV N σ
  -- Obtain PeriodicOverlapHypothesis.
  -- TODO(#81): Replace sorry once the periodic overlap dichotomy is formalized.
  -- The proof derives the overlap hypothesis from _hAssembly + periodicity data
  -- (hA.periodic, hB.periodic) via Proposition 3.3 of arXiv:1708.00029.
  have hOverlap : PeriodicOverlapHypothesis hA.blocks hB.blocks := by
    sorry -- #81: periodic overlap dichotomy (Proposition 3.3)
  -- Apply Theorem 3.4.
  exact fundamentalTheorem_periodic_proportional hA.blocks hB.blocks
    hNonRepA hNonRepB hOverlap

/-- **Theorem 3.8, Step 2: Per-block weight power-sum equality.**

After block matching (Step 1), the equal-MPV condition combined with the block expansion
formula and eventual linear independence of block MPV states yields: for each matched
pair `(j, perm j)`, the weight power sums agree for all positive exponents.

**Proof sketch** (Thm 3.8, steps 2–5 of arXiv:1708.00029):
1. `SameMPV₂ A B` + `mpv_toTensorFromBlocks_eq_sum` gives
   `∑_j μA_j^N * mpv(blocksA j) = ∑_j μB_{perm j}^N * ξ_j^N * mpv(blocksA j)`.
2. `periodicBasis_eventuallyLinearlyIndependent` gives eventual linear independence.
3. Therefore `μA_j^N = μB_{perm j}^N * ξ_j^N` for all large `N`.
4. `power_sums_eq_of_eventually_eq` extrapolates to all positive `N`.

**Conditional on #81**: Uses `periodicBasis_eventuallyLinearlyIndependent` which
depends on `periodicOverlapDichotomy`. -/
theorem perBlock_weight_powerSum_eq_of_matching
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsIrreducibleForm A) (hB : IsIrreducibleForm B)
    (hSame : SameMPV₂ A B)
    (hrAB : hA.r = hB.r)
    (perm : Fin hA.r ≃ Fin hB.r)
    (hRep : ∀ j, HetRepeatedBlocks (hA.blocks j) (hB.blocks (perm j))) :
    ∀ j : Fin hA.r, ∀ N : ℕ, 0 < N →
      (hA.μ j) ^ N = (hB.μ (perm j)) ^ N := by
  -- TODO(#81): Derive from MPV expansion + linear independence + phase absorption.
  -- The proof uses:
  -- (a) mpv_toTensorFromBlocks_eq_sum to expand both sides,
  -- (b) HetRepeatedBlocks → mpv equality up to phase ξ_j,
  -- (c) periodicBasis_eventuallyLinearlyIndependent → per-block coefficient match,
  -- (d) power_sums_eq_of_eventually_eq → extrapolation to all N > 0.
  sorry -- #81 + coefficient extraction infrastructure

/-- **Theorem 3.8: Periodic FT, equal case (arXiv:1708.00029).**

If two MPS tensors in irreducible form with non-repeating blocks generate equal MPV
families, then:

1. **Block matching**: equal block counts, a bijection, and per-block `HetRepeatedBlocks`.
2. **Per-block Z-gauge**: for each matched pair with period `m_j`, there exists a diagonal
   `Z_j` with `Z_j^{m_j} = 1` and `Z_j * diag(μB_{perm j}) = diag(μA_j)`.
3. **Weight multiset equality**: `μA_j` and `μB_{perm j}` determine the same multiset.

This composes Theorem 3.4 with the Z-gauge pipeline from PR #94.

**Conditional on #81**: The block matching and weight extraction use `sorry` for the
periodic overlap dichotomy and linear independence arguments. The Z-gauge construction
itself (`equalCase_zgauge_pipeline`) is fully proved. -/
theorem fundamentalTheorem_periodic_equalCase
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsIrreducibleForm A) (hB : IsIrreducibleForm B)
    (hNonRepA : ∀ j₁ j₂ : Fin hA.r, j₁ ≠ j₂ →
      ¬ HetRepeatedBlocks (hA.blocks j₁) (hA.blocks j₂))
    (hNonRepB : ∀ k₁ k₂ : Fin hB.r, k₁ ≠ k₂ →
      ¬ HetRepeatedBlocks (hB.blocks k₁) (hB.blocks k₂))
    (hSame : SameMPV₂ A B)
    (_hμA_ne : ∀ j, hA.μ j ≠ 0)
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
  obtain ⟨_hrAB, perm, hRep⟩ :=
    fundamentalTheorem_periodic_equalCase_matching A B hA hB hNonRepA hNonRepB hSame
  refine ⟨_hrAB, perm, hRep, fun j => ?_⟩
  -- Step 2: Per-block weight power-sum equality (sorry, #81).
  have hPowEq : ∀ N : ℕ, 0 < N → (hA.μ j) ^ N = (hB.μ (perm j)) ^ N := by
    exact perBlock_weight_powerSum_eq_of_matching A B hA hB hSame _hrAB perm hRep j
  -- Step 3: Z-gauge construction from matched weights.
  -- For a single weight per block, the Z-gauge is the scalar ratio μA_j / μB_{perm j}.
  have hPow_period : (hA.μ j) ^ (hA.period j) = (hB.μ (perm j)) ^ (hA.period j) :=
    hPowEq (hA.period j) (hA.periodic j).period_pos
  obtain ⟨Z, hZpow, hZmul, hMultiset⟩ :=
    equalCase_zgauge_pipeline (hA.period j)
      (fun _ : Fin 1 => hA.μ j) (fun _ : Fin 1 => hB.μ (perm j))
      (fun _ => hμB_ne (perm j))
      (fun _ => hPow_period)
      (fun k hk => by simp [hPowEq k hk])
  refine ⟨Z, hZpow, hZmul, ?_⟩
  -- Convert Finset.univ.val.map to multiset singleton equality.
  simp only [Finset.univ_unique] at hMultiset
  exact hMultiset

end EqualCase

end MPSTensor
