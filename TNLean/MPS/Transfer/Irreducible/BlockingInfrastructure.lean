/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Physical.BlockingTransfer
import TNLean.MPS.Tensor.DirectSum.GaugeEquiv
import TNLean.MPS.Transfer.Irreducible.BlockingViaAdjoint
import TNLean.MPS.Tensor.Tactic

import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Blocking infrastructure: SameMPV₂ compatibility, primitivity under multiples, common period

This file contains the blocking infrastructure needed to go from per-block periodicity
removal to a common blocking period making all blocks primitive simultaneously.  Blocking
`p` sites is `Kraus.block A p`, the family indexed by the words `Fin p → α`; configurations
of blocks are configurations of sites through `Kraus.blockConfigEquiv`.

## Main results

### Part A: SameMPV₂ blocking
* `mpv_block_eq_mpv_blockConfig` — the matrix product vector of a blocked tensor is the
  matrix product vector of the original tensor on the flattened configuration.
* `sameMPV₂_block_of_sameMPV₂_toTensorFromBlocks` — Blocking distributes over
  `toTensorFromBlocks`: if `SameMPV₂ A (toTensorFromBlocks μ blocks)`, then
  `SameMPV₂ (block A p) (toTensorFromBlocks (μ^p) (block blocks p))`.
* `EventuallyNonzeroProportionalMPV₂.block` — Eventual nonzero proportionality
  is preserved by positive physical blocking.
* `reindexPhysical_blockConfigEquiv_block` — blocking `n` blocks of length `m` is blocking
  `n * m` sites.

### Part B: Primitivity under multiples
* `isPrimitive_transferMap_block_of_dvd` — transfer-map primitivity is monotone
  in the blocking period (for multiples).

### Part C: Common period via LCM
* `lcmPeriod`, `lcmPeriod_pos`, `dvd_lcmPeriod` — auxiliary LCM results on `Fin k → ℕ`
  families used throughout common-period blocking.
* `exists_common_blocking_all_primitive` — given a family of blocks each admitting some
  primitivity period, there exists a single common period.
* `exists_common_blocking_all_primitive_of_TP_irr` — convenience entry point from TP +
  irreducible hypotheses.

## References

* [arXiv:1606.00608, Appendix A — periodicity removal by blocking]
* [arXiv:2011.12127, Section IV — canonical form construction]
-/

open MPTensor

open scoped Matrix BigOperators

namespace MPSTensor

variable {α : Type*} [Fintype α]

/-!
## Part A: SameMPV₂ compatibility under blocking
-/

section SameMPV₂Blocking

variable {D : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- Evaluating the blocked tensor on a configuration of blocks agrees with evaluating
the original tensor on the flattened configuration. -/
theorem mpv_block_eq_mpv_blockConfig {D' : ℕ} (T : MPTensor α (Fin D')) (p : ℕ) {N : ℕ}
    (σ : Fin N → Fin p → α) :
    mpv (Kraus.block T p) σ = mpv T (Kraus.blockConfigEquiv α N p σ) := by
  simp only [mpv, coeff, Kraus.evalWord_block, Kraus.ofFn_blockConfigEquiv]

/-- Blocking distributes over `toTensorFromBlocks`: if
`SameMPV₂ A (toTensorFromBlocks μ blocks)`, then blocking by `p` on both sides gives
`SameMPV₂ (block A p) (toTensorFromBlocks (μ^p) (block blocks p))`, since
`V_N(A^{[p]}) = V_{Np}(A)` and `(μ^p)^N = μ^(Np)`. -/
theorem sameMPV₂_block_of_sameMPV₂_toTensorFromBlocks
    (A : MPTensor α (Fin D)) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
    (hSame : SameMPV₂ A (toTensorFromBlocks μ blocks)) (p : ℕ) :
    SameMPV₂ (Kraus.block A p)
      (toTensorFromBlocks (fun k => (μ k) ^ p) (fun k => Kraus.block (blocks k) p)) := by
  intro N σ
  rw [mpv_block_eq_mpv_blockConfig, hSame, mpv_toTensorFromBlocks_eq_sum,
    mpv_toTensorFromBlocks_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mpv_block_eq_mpv_blockConfig, ← pow_mul, Nat.mul_comm p N]

/-- Blocking the assembled weighted block tensor is MPV-equivalent to assembling the
blocked blocks with powered weights. -/
theorem sameMPV₂_block_toTensorFromBlocks (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k))) (p : ℕ) :
    SameMPV₂ (Kraus.block (toTensorFromBlocks (α := α) (μ := μ) blocks) p)
      (toTensorFromBlocks (fun k => (μ k) ^ p) (fun k => Kraus.block (blocks k) p)) :=
  sameMPV₂_block_of_sameMPV₂_toTensorFromBlocks _ μ blocks (fun _ _ => rfl) p

/-- Positive-length MPV equality is preserved by positive physical blocking. -/
theorem sameMPV₂Pos_block {D₁ D₂ : ℕ} (A : MPTensor α (Fin D₁)) (B : MPTensor α (Fin D₂))
    (hSame : SameMPV₂Pos A B) (p : ℕ) (hp : 0 < p) :
    SameMPV₂Pos (Kraus.block A p) (Kraus.block B p) := by
  intro N hN σ
  rw [mpv_block_eq_mpv_blockConfig, mpv_block_eq_mpv_blockConfig]
  exact hSame (N * p) (Nat.mul_pos hN hp) _

/-- Eventual nonzero MPV proportionality is preserved by positive physical blocking. -/
theorem _root_.MPTensor.EventuallyNonzeroProportionalMPV₂.block
    {D₁ D₂ : ℕ} {A : MPTensor α (Fin D₁)} {B : MPTensor α (Fin D₂)}
    (h : EventuallyNonzeroProportionalMPV₂ A B) (p : ℕ) (hp : 0 < p) :
    EventuallyNonzeroProportionalMPV₂ (Kraus.block A p) (Kraus.block B p) := by
  unfold EventuallyNonzeroProportionalMPV₂ at h ⊢
  rw [Filter.eventually_atTop] at h ⊢
  rcases h with ⟨N₀, hN₀⟩
  refine ⟨N₀, fun N hN => ?_⟩
  have hNle : N ≤ N * p := le_mul_of_one_le_right (Nat.zero_le N) hp
  rcases hN₀ (N * p) (hN.trans hNle) with ⟨c, hc, hEq⟩
  refine ⟨c, hc, fun σ => ?_⟩
  rw [mpv_block_eq_mpv_blockConfig, mpv_block_eq_mpv_blockConfig]
  exact hEq _

/-- Positive-length equality with a weighted nonzero-block tensor is preserved by
positive physical blocking, with each weight transported to the corresponding power. -/
theorem sameMPV₂Pos_block_toTensorFromBlocks
    (A : MPTensor α (Fin D)) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
    (hSame : SameMPV₂Pos A (toTensorFromBlocks (α := α) (μ := μ) blocks))
    (p : ℕ) (hp : 0 < p) :
    SameMPV₂Pos (Kraus.block A p)
      (toTensorFromBlocks (fun k => (μ k) ^ p) (fun k => Kraus.block (blocks k) p)) := by
  intro N hN σ
  exact (sameMPV₂Pos_block A _ hSame p hp N hN σ).trans
    (sameMPV₂_block_toTensorFromBlocks μ blocks p N σ)

/-- Positive-length equality of weighted nonzero-block tensors is preserved after
positive common blocking, with each weight transported to the corresponding power. -/
theorem sameMPV₂Pos_toTensorFromBlocks_blockPower
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (μA : Fin rA → ℂ) (blocksA : (k : Fin rA) → MPTensor α (Fin (dimA k)))
    (μB : Fin rB → ℂ) (blocksB : (k : Fin rB) → MPTensor α (Fin (dimB k)))
    (hSame : SameMPV₂Pos
      (toTensorFromBlocks (α := α) (μ := μA) blocksA)
      (toTensorFromBlocks (α := α) (μ := μB) blocksB))
    (p : ℕ) (hp : 0 < p) :
    SameMPV₂Pos
      (toTensorFromBlocks (fun k => (μA k) ^ p) (fun k => Kraus.block (blocksA k) p))
      (toTensorFromBlocks (fun k => (μB k) ^ p) (fun k => Kraus.block (blocksB k) p)) := by
  intro N hN σ
  exact ((sameMPV₂_block_toTensorFromBlocks μA blocksA p N σ).symm.trans
    (sameMPV₂Pos_block _ _ hSame p hp N hN σ)).trans
    (sameMPV₂_block_toTensorFromBlocks μB blocksB p N σ)

end SameMPV₂Blocking

/-! ## Weight transport under blocking -/

section WeightTransport

variable {r : ℕ}

omit [Fintype α] in
/-- Nonzero block weights remain nonzero after taking a blocking power. -/
theorem blockWeights_ne_zero
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) (p : ℕ) :
    ∀ k, (μ k) ^ p ≠ 0 := by
  intro k
  exact pow_ne_zero p (hμ k)

end WeightTransport

/-! ## Iterated blocking -/

section IteratedBlocking

omit [Fintype α] in
/-- Blocking `n` blocks of length `m` is blocking `n * m` sites, after reading a
configuration of `n` blocks as a configuration of `n * m` sites. -/
theorem reindexPhysical_blockConfigEquiv_block {D : ℕ} (A : MPTensor α (Fin D)) (m n : ℕ) :
    Kraus.reindexPhysical (Kraus.blockConfigEquiv α n m) (Kraus.block A (n * m)) =
      Kraus.block (Kraus.block A m) n := by
  funext σ
  simp only [Kraus.reindexPhysical, Kraus.block_apply, Kraus.evalWord_block,
    Kraus.ofFn_blockConfigEquiv]

end IteratedBlocking

/-!
## Part B: Primitivity under multiples

If the transfer map of `block A p` is primitive and `p ∣ q`, then the
transfer map of `block A q` is also primitive, by `isPrimitive_pow_of_isPrimitive`:
if `periph(E) = {1}` then `periph(E^m) = {1}`.
-/

section PrimitivityMultiples

variable {D : ℕ}

/-- Transfer-map primitivity is monotone in the blocking period (for multiples).

If `block A p` has a primitive transfer map and `p ∣ q` with `q > 0`, then
`block A q` also has a primitive transfer map. The proof uses `Kraus.transferMap_block`
to convert between blocking levels. -/
theorem isPrimitive_transferMap_block_of_dvd
    [NeZero D]
    (A : MPTensor α (Fin D)) (p q : ℕ) (hpq : p ∣ q) (hq : 0 < q)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (Kraus.block A p))) :
    _root_.IsPrimitive (Kraus.transferMap (Kraus.block A q)) := by
  obtain ⟨m, rfl⟩ := hpq
  -- p > 0 since p * m > 0
  have hp : 0 < p := by
    by_contra h; push Not at h; interval_cases p; simp at hq
  -- m > 0 since p * m > 0 and p > 0
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  -- Rewrite transfer maps as iterates of the original transfer map.
  rw [Kraus.transferMap_block]    -- goal: IsPrimitive ((Kraus.transferMap A) ^ (p * m))
  rw [pow_mul]                          -- goal: IsPrimitive (((Kraus.transferMap A) ^ p) ^ m)
  -- goal: IsPrimitive ((Kraus.transferMap (block A p)) ^ m)
  rw [← Kraus.transferMap_block]
  exact isPrimitive_pow_of_isPrimitive _ m hm hPrim

end PrimitivityMultiples

/-!
## Part C: Common blocking period via LCM

Given a finite family of blocks, each admitting some blocking period that
makes its transfer map primitive, there exists a single common period
making all of them primitive simultaneously. The period is the LCM of
the individual periods.
-/

section CommonPeriod

/-- LCM of a finite family of periods indexed by `Fin k`. -/
noncomputable def lcmPeriod {k : ℕ} (periods : Fin k → ℕ) : ℕ :=
  Finset.univ.lcm periods

/-- The LCM of a positive family of periods is positive. -/
theorem lcmPeriod_pos {k : ℕ} {periods : Fin k → ℕ} (h : ∀ i, 0 < periods i) :
    0 < lcmPeriod periods := by
  refine Nat.pos_of_ne_zero ?_
  refine Finset.lcm_ne_zero_iff.2 ?_
  intro i _
  exact Nat.ne_of_gt (h i)

/-- Each member of the family divides the LCM of the family. -/
theorem dvd_lcmPeriod {k : ℕ} (periods : Fin k → ℕ) (i : Fin k) :
    periods i ∣ lcmPeriod periods :=
  Finset.dvd_lcm (Finset.mem_univ i)

/-- There exists a common blocking period making all block transfer maps primitive.

Given a family of blocks indexed by `Fin r`, where each block `k` has some period `p_k`
making `Kraus.transferMap (block (blocks k) p_k)` primitive, the LCM of all `p_k`
serves as a universal period. -/
theorem exists_common_blocking_all_primitive
    {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
    (hDim : ∀ k, 0 < dim k)
    (hPer : ∀ k, ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (Kraus.transferMap (Kraus.block (blocks k) p))) :
    ∃ p, 0 < p ∧ ∀ k,
      _root_.IsPrimitive
        (Kraus.transferMap (Kraus.block (blocks k) p)) := by
  classical
  -- Choose a period for each block.
  let pk : Fin r → ℕ := fun k => (hPer k).choose
  have pk_pos : ∀ k, 0 < pk k := fun k => (hPer k).choose_spec.1
  have pk_prim : ∀ k, _root_.IsPrimitive
      (Kraus.transferMap (Kraus.block (blocks k) (pk k))) :=
    fun k => (hPer k).choose_spec.2
  -- Take the LCM of all periods.
  let P := lcmPeriod pk
  have hP_pos : 0 < P := lcmPeriod_pos pk_pos
  refine ⟨P, hP_pos, fun k => ?_⟩
  have hk_dvd : pk k ∣ P := dvd_lcmPeriod pk k
  have : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
  exact isPrimitive_transferMap_block_of_dvd (blocks k) (pk k) P hk_dvd hP_pos (pk_prim k)

/-- Common blocking from TP + irreducible hypotheses (the standard reduction entry point).

This combines `exists_block_isPrimitive_of_TP_of_isIrreducibleFamily` (per-block
periodicity removal) with `exists_common_blocking_all_primitive` (LCM common period). -/
theorem exists_common_blocking_all_primitive_of_TP_irr
    {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k)))
    (hTP : ∀ k, ∑ i : α, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, Kraus.IsIrreducibleFamily (blocks k))
    (hDim : ∀ k, 0 < dim k) :
    ∃ p, 0 < p ∧ ∀ k,
      _root_.IsPrimitive
        (Kraus.transferMap (Kraus.block (blocks k) p)) := by
  have hPer : ∀ k, ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (Kraus.transferMap (Kraus.block (blocks k) p)) := by
    intro k
    have : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
    exact exists_block_isPrimitive_of_TP_of_isIrreducibleFamily
      (blocks k) (hTP k) (hIrr k) (hDim k)
  exact exists_common_blocking_all_primitive blocks hDim hPer

end CommonPeriod

end MPSTensor
