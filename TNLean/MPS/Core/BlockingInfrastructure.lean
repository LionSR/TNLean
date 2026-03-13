/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint

import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Blocking infrastructure: SameMPV₂ compatibility, primitivity under multiples, common period

This file contains the **Tier 3** blocking infrastructure needed to go from
per-block periodicity removal to a common blocking period making all blocks
primitive simultaneously.

## Main results

### Part A: SameMPV₂ blocking
* `sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks` — Blocking distributes over
  `toTensorFromBlocks`: if `SameMPV₂ A (toTensorFromBlocks μ blocks)`, then
  `SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ^p) (blockTensor blocks p))`.

### Part B: Primitivity under multiples
* `isPrimitive_pow_of_isPrimitive` — primitive channels remain primitive under positive powers.
* `isPrimitive_transferMap_blockTensor_of_dvd` — transfer-map primitivity is monotone
  in the blocking period (for multiples).

### Part C: Common period via LCM
* `exists_common_blocking_all_primitive` — given a family of blocks each admitting some
  primitivity period, there exists a single common period.
* `exists_common_blocking_all_primitive_of_TP_irr` — convenience entry point from TP +
  irreducible hypotheses.

## References

* [arXiv:1606.00608, Appendix A — periodicity removal by blocking]
* [arXiv:2011.12127, §IV — canonical form construction]
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-!
## Part A: SameMPV₂ compatibility under blocking

The key observation: `blockTensor T p` computes `mpv` via flattened words,
and the flattening depends only on the blocked configuration `σ` and the
period `p`, not on the tensor `T`. This lets us "push blocking through"
`toTensorFromBlocks`.
-/

section SameMPV₂Blocking

variable {D : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- Blocking distributes over `toTensorFromBlocks`: if
`SameMPV₂ A (toTensorFromBlocks μ blocks)`, then blocking by `p` on both sides gives
`SameMPV₂ (blockTensor A p) (toTensorFromBlocks (μ^p) (blockTensor blocks p))`.

The mathematical content is: `V_N(blockTensor A p) = V_{Np}(A)` after identifying
physical indices, and the block-diagonal expansion of `toTensorFromBlocks` respects
this identification with exponents scaling from `N * p` to `N` by `(μ^p)^N = μ^(Np)`. -/
theorem sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks
    (A : MPSTensor d D)
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ A (toTensorFromBlocks μ blocks))
    (p : ℕ) :
    SameMPV₂
      (blockTensor (d := d) (D := D) A p)
      (toTensorFromBlocks (d := blockPhysDim d p)
        (fun k => (μ k) ^ p) (fun k => blockTensor (d := d) (D := dim k) (blocks k) p)) := by
  intro N σ
  classical
  -- Build the flattened configuration σflat : Fin (N * p) → Fin d.
  -- This depends only on σ and p, not on any particular tensor.
  set flat : List (Fin d) := flattenBlockedWord d p (List.ofFn σ) with flat_def
  have hlen : flat.length = N * p := by
    simpa [flat_def] using (length_flattenBlockedWord (d := d) (L := p) (List.ofFn σ))
  set σflat : Fin (N * p) → Fin d :=
    fun i => flat.get (Fin.cast hlen.symm i) with σflat_def
  have hofFn : List.ofFn σflat = flat := by
    rw [σflat_def]
    conv_rhs => rw [← List.ofFn_get flat]
    have hcongr :=
      (List.ofFn_congr (m := N * p) (n := flat.length) hlen.symm
        (fun i : Fin (N * p) => flat.get (Fin.cast hlen.symm i)))
    simpa [Function.comp, Fin.cast_cast] using hcongr
  -- Key: for ANY tensor T with physical dimension d, mpv (blockTensor T p) σ = mpv T σflat.
  -- This is because the flattening σ ↦ σflat is independent of the tensor.
  have hblock (D' : ℕ) (T : MPSTensor d D') :
      mpv (blockTensor (d := d) (D := D') T p) σ = mpv T σflat := by
    simp [mpv, coeff, hofFn, flat_def, evalWord_blockTensor]
  calc
    mpv (blockTensor (d := d) (D := D) A p) σ
        = mpv A σflat := hblock D A
    _ = mpv (toTensorFromBlocks μ blocks) σflat := hSame (N * p) σflat
    _ = ∑ k : Fin r, (μ k) ^ (N * p) • mpv (blocks k) σflat := by
          exact mpv_toTensorFromBlocks_eq_sum μ blocks σflat
    _ = ∑ k : Fin r,
          ((μ k) ^ p) ^ N • mpv (blockTensor (d := d) (D := dim k) (blocks k) p) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hpow : (μ k) ^ (N * p) = ((μ k) ^ p) ^ N := by
            rw [Nat.mul_comm, pow_mul]
          rw [hpow, (hblock (dim k) (blocks k)).symm]
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (fun k => (μ k) ^ p) (fun k => blockTensor (d := d) (D := dim k) (blocks k) p)) σ := by
          exact (mpv_toTensorFromBlocks_eq_sum
            (fun k => (μ k) ^ p)
            (fun k => blockTensor (d := d) (D := dim k) (blocks k) p) σ).symm

end SameMPV₂Blocking

/-!
## Part B: Primitivity under multiples

If the transfer map of `blockTensor A p` is primitive and `p ∣ q`, then the
transfer map of `blockTensor A q` is also primitive.

The mathematical content: peripheral eigenvalues of `E^m` are `{μ^m | μ ∈ periph(E)}`,
so if `periph(E) = {1}` then `periph(E^m) = {1}`.
-/

section PrimitivityMultiples

variable {D : ℕ}

/-- Primitive channels remain primitive under positive powers.

If `peripheralEigenvalues E = {1}` and `m > 0`, then `peripheralEigenvalues (E^m) = {1}`.
This follows because the only peripheral eigenvalue `1` satisfies `1^m = 1`, and
spectral mapping ensures no new peripheral eigenvalues arise. -/
theorem isPrimitive_pow_of_isPrimitive
    [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (m : ℕ) (hm : 0 < m)
    (hPrim : _root_.IsPrimitive E) :
    _root_.IsPrimitive (E ^ m) := by
  -- Extract a nonzero fixed point from IsPrimitive.
  -- IsPrimitive says peripheralEigenvalues E = {1}, so 1 is an eigenvalue.
  have h1_mem : (1 : ℂ) ∈ peripheralEigenvalues E := by
    rw [hPrim]; exact rfl
  obtain ⟨ρ, hρ_ev⟩ := h1_mem.1.exists_hasEigenvector
  have hρ_ne : ρ ≠ 0 := (Module.End.hasEigenvector_iff.mp hρ_ev).2
  have hρ_fix : E ρ = ρ := by
    have := Module.End.mem_eigenspace_iff.mp (Module.End.hasEigenvector_iff.mp hρ_ev).1
    simpa using this
  -- All peripheral eigenvalues of E are 1, so μ^m = 1 for any peripheral eigenvalue μ.
  have hper : ∀ μ : ℂ, μ ∈ peripheralEigenvalues E → μ ^ m = 1 := by
    intro μ hμ
    have hμ1 : μ = 1 := by rw [hPrim] at hμ; exact hμ
    simp [hμ1]
  -- Apply the existing periodicity removal theorem.
  exact peripheralEigenvalues_pow_eq_singleton E hm hper ρ hρ_fix hρ_ne

/-- Transfer-map primitivity is monotone in the blocking period (for multiples).

If `blockTensor A p` has a primitive transfer map and `p ∣ q` with `q > 0`, then
`blockTensor A q` also has a primitive transfer map. The proof uses `transferMap_blockTensor`
to convert between blocking levels. -/
theorem isPrimitive_transferMap_blockTensor_of_dvd
    [NeZero D]
    (A : MPSTensor d D) (p q : ℕ) (hpq : p ∣ q) (hq : 0 < q)
    (hPrim : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := D) (blockTensor (d := d) (D := D) A p))) :
    _root_.IsPrimitive
      (transferMap (d := blockPhysDim d q) (D := D) (blockTensor (d := d) (D := D) A q)) := by
  obtain ⟨m, rfl⟩ := hpq
  -- p > 0 since p * m > 0
  have hp : 0 < p := by
    by_contra h; push_neg at h; interval_cases p; simp at hq
  -- m > 0 since p * m > 0 and p > 0
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  -- Rewrite transfer maps as iterates of the original transfer map.
  rw [transferMap_blockTensor]          -- goal: IsPrimitive ((transferMap A) ^ (p * m))
  rw [pow_mul]                          -- goal: IsPrimitive (((transferMap A) ^ p) ^ m)
  rw [← transferMap_blockTensor]        -- goal: IsPrimitive ((transferMap (blockTensor A p)) ^ m)
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

/-- There exists a common blocking period making all block transfer maps primitive.

Given a family of blocks indexed by `Fin r`, where each block `k` has some period `p_k`
making `transferMap (blockTensor (blocks k) p_k)` primitive, the LCM of all `p_k`
serves as a universal period. -/
theorem exists_common_blocking_all_primitive
    {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hDim : ∀ k, 0 < dim k)
    (hPer : ∀ k, ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p))) :
    ∃ p, 0 < p ∧ ∀ k,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p)) := by
  classical
  -- Choose a period for each block.
  let pk : Fin r → ℕ := fun k => (hPer k).choose
  have pk_pos : ∀ k, 0 < pk k := fun k => (hPer k).choose_spec.1
  have pk_prim : ∀ k, _root_.IsPrimitive
      (transferMap (d := blockPhysDim d (pk k)) (D := dim k)
        (blockTensor (d := d) (D := dim k) (blocks k) (pk k))) :=
    fun k => (hPer k).choose_spec.2
  -- Take the LCM of all periods.
  let P := Finset.univ.lcm pk
  have hP_pos : 0 < P := by
    have hne : Finset.univ.lcm pk ≠ 0 := by
      refine Finset.lcm_ne_zero_iff.2 ?_
      intro k _; exact Nat.ne_of_gt (pk_pos k)
    exact Nat.pos_of_ne_zero hne
  refine ⟨P, hP_pos, fun k => ?_⟩
  have hk_dvd : pk k ∣ P := Finset.dvd_lcm (Finset.mem_univ k)
  haveI : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
  exact isPrimitive_transferMap_blockTensor_of_dvd (blocks k) (pk k) P hk_dvd hP_pos (pk_prim k)

/-- Common blocking from TP + irreducible hypotheses (the standard pipeline entry point).

This combines `exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor` (per-block
periodicity removal) with `exists_common_blocking_all_primitive` (LCM common period). -/
theorem exists_common_blocking_all_primitive_of_TP_irr
    {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hDim : ∀ k, 0 < dim k) :
    ∃ p, 0 < p ∧ ∀ k,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p)) := by
  have hPer : ∀ k, ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim k)
          (blockTensor (d := d) (D := dim k) (blocks k) p)) := by
    intro k
    haveI : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
    exact exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor
      (blocks k) (hTP k) (hIrr k) (hDim k)
  exact exists_common_blocking_all_primitive blocks hDim hPer

end CommonPeriod

end MPSTensor
