/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.CumulativeSpan
import TNLean.Wielandt.PrimitivePaper
import TNLean.Wielandt.Lemma2b
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Invertible-element word span growth

This file establishes key structural properties of word spans when some
Kraus operator `A i₀` is invertible, toward **case (2)** of the Quantum
Wielandt inequality (arXiv:0909.5347, Theorem 1; Wolf §6.9).

## What is proved (sorry-free)

### Dimension monotonicity
* `wordSpan_finrank_le`: `dim(S_n) ≤ D²`.
* `mulLeft_image_wordSpan_le_succ`: `A i₀ · S_n ⊆ S_{n+1}`.
* `wordSpan_finrank_mono_of_isUnit`: `dim(S_{n+1}) ≥ dim(S_n)` when `A i₀`
  is invertible.

### Permanence of fullness
* `wordSpan_eq_top_of_ge_of_isUnit`: if `S_N = ⊤` and `A i₀` is invertible,
  then `S_m = ⊤` for all `m ≥ N`.

### Left-multiplication decomposition
* `wordSpan_succ_eq_mul_left`: `S_{n+1} = span{A_i} · S_n`.

## What is NOT yet proved

The **sharp bound** `i(A) ≤ D² − krausRank(A) + 1` for the invertible case
requires strict growth of `dim(S_n)` at each step where `dim < D²`. This
is the remaining formal gap for the invertible-case bound.

## References

* [SPGWC09] Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Theorem 1
* [Wolf12] Wolf, *Quantum Channels & Operations*, Theorem 6.9
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## Basic dimension bound for wordSpan -/

/-- The dimension of `S_n(A) = wordSpan A n` is bounded by `D²`. -/
theorem wordSpan_finrank_le (A : MPSTensor d D) (n : ℕ) :
    Module.finrank ℂ (wordSpan A n) ≤ D ^ 2 := by
  calc Module.finrank ℂ (wordSpan A n)
      ≤ Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) :=
        Submodule.finrank_le _
    _ = Fintype.card (Fin D) * Fintype.card (Fin D) *
        Module.finrank ℂ ℂ := Module.finrank_matrix ℂ ℂ _ _
    _ = D * D * 1 := by simp [Fintype.card_fin, Module.finrank_self]
    _ = D ^ 2 := by ring

/-! ## Left multiplication maps S_n into S_{n+1} -/

/-- Left multiplication by `A i₀` maps `S_n` into `S_{n+1}`. -/
theorem mulLeft_image_wordSpan_le_succ (A : MPSTensor d D)
    (i₀ : Fin d) (n : ℕ) :
    Submodule.map (LinearMap.mulLeft ℂ (A i₀)) (wordSpan A n) ≤
      wordSpan A (n + 1) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro M ⟨σ, rfl⟩
  change (LinearMap.mulLeft ℂ (A i₀)) (evalWord A (List.ofFn σ)) ∈
    wordSpan A (n + 1)
  simp only [LinearMap.mulLeft_apply]
  change evalWord A (i₀ :: List.ofFn σ) ∈ wordSpan A (n + 1)
  apply Submodule.subset_span
  exact ⟨Fin.cons i₀ σ, by simp [List.ofFn_succ]⟩

/-- Left multiplication by `A i₀ ^ k` maps `S_n` into `S_{n+k}`. -/
theorem mulLeft_pow_image_wordSpan_le (A : MPSTensor d D)
    (i₀ : Fin d) (n k : ℕ) :
    Submodule.map (LinearMap.mulLeft ℂ (A i₀ ^ k)) (wordSpan A n) ≤
      wordSpan A (n + k) := by
  induction k with
  | zero => simp [Submodule.map_id]
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 from by omega]
    calc Submodule.map (LinearMap.mulLeft ℂ (A i₀ ^ (k + 1))) (wordSpan A n)
        = Submodule.map (LinearMap.mulLeft ℂ (A i₀))
            (Submodule.map (LinearMap.mulLeft ℂ (A i₀ ^ k)) (wordSpan A n)) := by
          rw [← Submodule.map_comp]; congr 1; ext x
          simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
            pow_succ', ← Matrix.mul_assoc]
      _ ≤ Submodule.map (LinearMap.mulLeft ℂ (A i₀)) (wordSpan A (n + k)) :=
          Submodule.map_mono ih
      _ ≤ wordSpan A ((n + k) + 1) :=
          mulLeft_image_wordSpan_le_succ A i₀ (n + k)

/-! ## S_{n+1} = span{A_i} * S_n -/

/-- `S_{n+1} = span{A_i} · S_n` (left-multiplication decomposition). -/
theorem wordSpan_succ_eq_mul_left (A : MPSTensor d D) (n : ℕ) :
    wordSpan A (n + 1) =
      (Submodule.span ℂ (Set.range A)) * wordSpan A n := by
  apply le_antisymm
  · exact wordSpan_succ_le_mul A n
  · -- span{A_i} ≤ wordSpan A 1
    have hS1 : Submodule.span ℂ (Set.range A) ≤ wordSpan A 1 := by
      apply Submodule.span_le.mpr
      rintro M ⟨j, rfl⟩
      apply Submodule.subset_span
      refine ⟨fun _ => j, ?_⟩
      simp only [List.ofFn, Fin.foldr_succ, Fin.foldr_zero]
      simp [evalWord]
    calc (Submodule.span ℂ (Set.range A)) * wordSpan A n
        ≤ wordSpan A 1 * wordSpan A n :=
          mul_le_mul' hS1 (le_refl _)
      _ ≤ wordSpan A (1 + n) := wordSpan_mul_le A 1 n
      _ = wordSpan A (n + 1) := by congr 1; omega

/-! ## Monotonicity of wordSpan dimension under invertibility -/

/-- When `A i₀` is invertible, `dim(S_{n+1}) ≥ dim(S_n)`.

Left-multiplication by an invertible matrix is injective; its image in
`S_{n+1}` has the same dimension as `S_n`. -/
theorem wordSpan_finrank_mono_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) (n : ℕ) :
    Module.finrank ℂ (wordSpan A n) ≤
    Module.finrank ℂ (wordSpan A (n + 1)) := by
  have hle := mulLeft_image_wordSpan_le_succ A i₀ n
  have hinj : Function.Injective (LinearMap.mulLeft ℂ (A i₀)) := by
    intro x y hxy; simp only [LinearMap.mulLeft_apply] at hxy
    exact hU.mul_right_injective hxy
  -- finrank(map) ≤ finrank(source) by Submodule.finrank_map_le
  -- finrank(source) ≤ finrank(map) by injectivity
  -- Combined with finrank(map) ≤ finrank(S_{n+1}) by inclusion
  have hle_image : Module.finrank ℂ
      (Submodule.map (LinearMap.mulLeft ℂ (A i₀)) (wordSpan A n)) ≤
      Module.finrank ℂ (wordSpan A (n + 1)) :=
    Submodule.finrank_mono hle
  -- finrank(S_n) ≤ finrank(image) by injection + rank-nullity
  -- For injective f: finrank(map f p) = finrank(p)
  -- We use: finrank(image) ≤ finrank(source) from Submodule.finrank_map_le
  -- and finrank(source) ≤ finrank(image) from the fact that f restricts to
  -- an injective linear map from source to image (rank ≥ by injection)
  -- Simplest: just use Submodule.equivMapOfInjective to get a LinearEquiv
  have heq : Module.finrank ℂ (wordSpan A n) =
      Module.finrank ℂ
        (Submodule.map (LinearMap.mulLeft ℂ (A i₀)) (wordSpan A n)) := by
    let e := Submodule.equivMapOfInjective
      (LinearMap.mulLeft ℂ (A i₀)) hinj (wordSpan A n)
    -- e : wordSpan A n ≃ₛₗ[RingHom.id ℂ] map ... wordSpan
    -- Since σ = id, this is a linear equiv
    exact LinearEquiv.finrank_eq e
  linarith

/-- General monotonicity: `dim(S_m) ≤ dim(S_n)` for `m ≤ n` when `A i₀`
is invertible. -/
theorem wordSpan_finrank_mono_of_isUnit' (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) {m n : ℕ} (h : m ≤ n) :
    Module.finrank ℂ (wordSpan A m) ≤
    Module.finrank ℂ (wordSpan A n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp
  | succ k ih =>
    calc Module.finrank ℂ (wordSpan A m)
        ≤ Module.finrank ℂ (wordSpan A (m + k)) := ih (by omega)
      _ ≤ Module.finrank ℂ (wordSpan A (m + (k + 1))) := by
          rw [show m + (k + 1) = (m + k) + 1 from by omega]
          exact wordSpan_finrank_mono_of_isUnit A i₀ hU (m + k)

/-! ## Permanence of fullness -/

/-- **Permanence**: if `S_N = ⊤` and `A i₀` is invertible, then `S_m = ⊤`
for all `m ≥ N`.

Proof: `A i₀ ^ (m - N)` is invertible, so its left-multiplication maps
`S_N = M_D(ℂ)` surjectively into `S_m`, giving `S_m = ⊤`. -/
theorem wordSpan_eq_top_of_ge_of_isUnit (A : MPSTensor d D)
    (i₀ : Fin d) (hU : IsUnit (A i₀)) {N : ℕ}
    (hN : wordSpan A N = ⊤) {m : ℕ} (hm : N ≤ m) :
    wordSpan A m = ⊤ := by
  rw [eq_top_iff]
  have hPow : IsUnit (A i₀ ^ (m - N)) := hU.pow (m - N)
  -- mulLeft(A i₀ ^ (m - N)) is surjective since the matrix is invertible
  have hSurj : Function.Surjective (LinearMap.mulLeft ℂ (A i₀ ^ (m - N))) := by
    intro y
    obtain ⟨u, hu⟩ := hPow
    refine ⟨(↑u⁻¹ : Matrix (Fin D) (Fin D) ℂ) * y, ?_⟩
    simp only [LinearMap.mulLeft_apply, ← Matrix.mul_assoc]
    rw [← hu, show (u : Matrix (Fin D) (Fin D) ℂ) * ↑u⁻¹ = 1 from
      Units.mul_inv u]
    simp
  calc ⊤ = Submodule.map (LinearMap.mulLeft ℂ (A i₀ ^ (m - N))) ⊤ := by
          rw [Submodule.map_top]
          exact (LinearMap.range_eq_top.mpr hSurj).symm
    _ = Submodule.map (LinearMap.mulLeft ℂ (A i₀ ^ (m - N)))
          (wordSpan A N) := by rw [hN]
    _ ≤ wordSpan A (N + (m - N)) :=
          mulLeft_pow_image_wordSpan_le A i₀ N (m - N)
    _ = wordSpan A m := by congr 1; omega

end MPSTensor
