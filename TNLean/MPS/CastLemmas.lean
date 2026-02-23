/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPVOverlap

/-!
# Cast lemmas for MPSTensor dimension changes

When two bond dimensions `D₁` and `D₂` are propositionally equal (`h : D₁ = D₂`),
the cast `cast (congr_arg (MPSTensor d) h) A` preserves all relevant MPS quantities:
matrix product vectors, overlaps, injectivity, the DS gauge condition, and
gauge-phase equivalence.

These lemmas were previously duplicated as private helpers in
`BNTPermutationSimple`, `BNTPermutationThm44`, and `BNTConstruction`.
-/

open scoped BigOperators Matrix

namespace MPSTensor

/-! ## Pointwise cast lemmas -/

/-- Casting the bond dimension of an MPS tensor preserves matrix product vectors. -/
lemma mpv_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂) (A : MPSTensor d D₁) :
    ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (cast (congr_arg (MPSTensor d) h) A) σ = mpv A σ := by
  subst h; simp

/-- Casting the bond dimension of the left tensor preserves the MPV overlap. -/
lemma mpvOverlap_cast_dim_left {d D₁ D₂ D₃ : ℕ} (h : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₃) :
    ∀ N, mpvOverlap (d := d) (cast (congr_arg (MPSTensor d) h) A) B N =
      mpvOverlap (d := d) A B N := by
  subst h; simp

/-- Casting the bond dimension preserves injectivity. -/
lemma isInjective_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂) (A : MPSTensor d D₁) :
    IsInjective (cast (congr_arg (MPSTensor d) h) A) ↔ IsInjective A := by
  subst h; simp

/-- Casting the bond dimension preserves the DS gauge condition `∑ Aᵢᴴ * Aᵢ = 1`. -/
lemma dsGauge_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂) (A : MPSTensor d D₁) :
    (∑ i : Fin d, (cast (congr_arg (MPSTensor d) h) A i)ᴴ *
      (cast (congr_arg (MPSTensor d) h) A i)) = 1 ↔
    (∑ i : Fin d, (A i)ᴴ * (A i)) = 1 := by
  subst h; simp

/-- Shift the tensor index in a gauge-phase equivalence along an index equality. -/
lemma gaugePhaseEquiv_cast_idx {d g : ℕ} {dim₁ dim₂ : Fin g → ℕ}
    (T₁ : (j : Fin g) → MPSTensor d (dim₁ j))
    (T₂ : (j : Fin g) → MPSTensor d (dim₂ j))
    {i₁ i₂ : Fin g} (hi : i₁ = i₂) {j : Fin g}
    (hdim : dim₁ i₁ = dim₂ j)
    (hg : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) (T₁ i₁)) (T₂ j)) :
    GaugePhaseEquiv (cast (congr_arg (MPSTensor d) (show dim₁ i₂ = dim₂ j from hi ▸ hdim))
      (T₁ i₂)) (T₂ j) := by
  subst hi; exact hg

/-- Shift the tensor index on the left family in a gauge-phase equivalence along an index equality.

This is a version of `gaugePhaseEquiv_cast_idx` that allows different index types for the two
families. -/
lemma gaugePhaseEquiv_cast_idx_left {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    {i₁ i₂ : Fin gA} (hi : i₁ = i₂) {k : Fin gB}
    (hdim : dimA i₁ = dimB k)
    (hg : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hdim) (A i₁)) (B k)) :
    GaugePhaseEquiv (cast (congr_arg (MPSTensor d) (show dimA i₂ = dimB k from hi ▸ hdim))
      (A i₂)) (B k) := by
  subst hi; exact hg

end MPSTensor
