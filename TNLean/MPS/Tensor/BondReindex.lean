/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Matrix.MatrixReindex
import TNLean.MPS.Tensor.Defs
import QICLean.Channel.Irreducible.InvariantProjection
import TNLean.MPS.Tensor.Overlap

/-!
# Bond-dimension reindexing of matrix product tensors

This file provides the canonical transport of a matrix product tensor along an
equality of bond dimensions.  The transport is expressed as an equivalence and
implemented by reindexing both matrix coordinates along the induced equivalence
of finite bond-index types.

The accompanying lemmas identify this transport with the former raw type
cast, describe its values at physical and bond coordinates, and record the
transport of word evaluation together with the invariance of matrix product
vectors, `SameMPV₂`, and `GaugePhaseEquiv`.

## Cast lemmas for MPSTensor dimension changes

When two bond dimensions `D₁` and `D₂` are propositionally equal (`h : D₁ = D₂`),
the cast `cast (congr_arg (MPSTensor d) h) A` preserves all relevant MPS quantities:
matrix product vectors, overlaps, injectivity, irreducibility, the left-canonical /
trace-preserving condition `∑ Aᵢ† Aᵢ = I`, and gauge-phase equivalence.

These lemmas were previously duplicated as private auxiliary results in
`BNT/PermutationRigidityPrimitive`, `BNT/Construction`, and
`CanonicalForm/Reduction`.
-/

section

namespace MPSTensor

variable {d D D₁ D₂ D₃ : ℕ}

/-- Reindex the bond coordinates of a matrix product tensor along an equality
of bond dimensions. -/
def reindex (h : D₁ = D₂) : MPSTensor d D₁ ≃ MPSTensor d D₂ :=
  Equiv.piCongrRight fun _ : Fin d => Matrix.reindex (finCongr h) (finCongr h)

/-- The bond reindexing along reflexivity is the identity on tensors. -/
@[simp] theorem reindex_rfl (A : MPSTensor d D) :
    reindex (rfl : D = D) A = A := by
  ext i j k
  rfl

/-- The former type-cast transport agrees with bond-coordinate reindexing. -/
@[simp] theorem cast_eq_reindex (h : D₁ = D₂) (A : MPSTensor d D₁) :
    cast (congrArg (MPSTensor d) h) A = reindex h A := by
  subst h
  simp

/-- Reindexing a tensor at one physical index reindexes both matrix
coordinates. -/
theorem reindex_apply (h : D₁ = D₂) (A : MPSTensor d D₁) (i : Fin d) :
    reindex h A i =
      Matrix.reindex (finCongr h) (finCongr h) (A i) := by
  rfl

/-- At one physical index, bond reindexing agrees with dependent transport of
the corresponding matrix value. -/
theorem reindex_apply_eq_cast (h : D₁ = D₂) (A : MPSTensor d D₁) (i : Fin d) :
    reindex h A i =
      cast (congrArg (fun n => Matrix (Fin n) (Fin n) ℂ) h) (A i) := by
  subst h
  rfl

/-- Reindexing at physical and bond coordinates evaluates the original tensor
at the inversely reindexed bond coordinates. -/
@[simp] theorem reindex_apply_apply (h : D₁ = D₂) (A : MPSTensor d D₁)
    (i : Fin d) (j k : Fin D₂) :
    reindex h A i j k = A i (finCongr h.symm j) (finCongr h.symm k) := by
  rfl

/-- Word evaluation commutes with bond-dimension reindexing. -/
theorem reindex_evalWord (h : D₁ = D₂) (A : MPSTensor d D₁)
    (w : List (Fin d)) :
    Kraus.evalWord (reindex h A) w =
      Matrix.reindex (finCongr h) (finCongr h) (Kraus.evalWord A w) := by
  subst h
  simp

/-- Bond-dimension reindexing does not change matrix product vector
coefficients. -/
theorem reindex_mpv (h : D₁ = D₂) (A : MPSTensor d D₁)
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (reindex h A) σ = mpv A σ := by
  unfold mpv coeff
  rw [reindex_evalWord, Matrix.trace_reindex]

/-- Bond-dimension reindexing preserves algebraic injectivity. -/
@[simp] theorem isInjective_reindex (h : D₁ = D₂) (A : MPSTensor d D₁) :
    Kraus.IsInjective (reindex h A) ↔ Kraus.IsInjective A := by
  subst h
  simp

/-- Reindexing the left tensor preserves equality of matrix product vector
families. -/
@[simp] theorem sameMPV₂_reindex_left (h : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₃) :
    SameMPV₂ (reindex h A) B ↔ SameMPV₂ A B := by
  constructor <;> intro hAB N σ <;> simpa only [reindex_mpv] using hAB N σ

/-- Reindexing the right tensor preserves equality of matrix product vector
families. -/
@[simp] theorem sameMPV₂_reindex_right (h : D₁ = D₂)
    (A : MPSTensor d D₃) (B : MPSTensor d D₁) :
    SameMPV₂ A (reindex h B) ↔ SameMPV₂ A B := by
  constructor <;> intro hAB N σ <;> simpa only [reindex_mpv] using hAB N σ

/-- Simultaneous bond-dimension reindexing preserves gauge-phase equivalence. -/
@[simp] theorem gaugePhaseEquiv_reindex (h : D₁ = D₂)
    (A B : MPSTensor d D₁) :
    GaugePhaseEquiv (reindex h A) (reindex h B) ↔ GaugePhaseEquiv A B := by
  subst h
  simp

end MPSTensor

end

section

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
    Kraus.IsInjective (cast (congr_arg (MPSTensor d) h) A) ↔ Kraus.IsInjective A := by
  subst h; simp

/-- Casting the bond dimension preserves fixed-length block injectivity. -/
lemma isNBlkInjective_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂)
    (A : MPSTensor d D₁) (N : ℕ) :
    Kraus.IsNBlkInjective (cast (congr_arg (MPSTensor d) h) A) N ↔
      Kraus.IsNBlkInjective A N := by
  subst h
  simp

/-- Casting the bond dimension preserves irreducibility. -/
lemma isIrreducibleTensor_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂) (A : MPSTensor d D₁) :
    Kraus.IsIrreducibleFamily (cast (congr_arg (MPSTensor d) h) A) ↔
      Kraus.IsIrreducibleFamily A := by
  subst h
  rfl

/-- Casting the bond dimension preserves the left-canonical (trace-preserving)
condition `∑ Aᵢᴴ * Aᵢ = 1`.  A dimension cast is a propositional equality
`h : D₁ = D₂`; this lemma confirms that the normalization identity transfers
through such a cast without change. -/
lemma leftCanonical_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂) (A : MPSTensor d D₁) :
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

end MPSTensor

end
