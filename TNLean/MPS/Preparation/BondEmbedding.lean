/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Analysis.MatrixSqrt

/-!
# Embedding virtual bonds in a common space

Coordinate isometries preserve density matrices, their traces, and their positive square
roots. The same embeddings act on the pairs used in matrix product state preparation.
These identities are shared by the direct-sum and varying-bond constructions.

## References

* arXiv:2307.01696, Supplemental Material, eqs. (S2) and (S7), and the paragraph
  "Inhomogeneous short-range correlated MPS".
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker

namespace MPSTensor

variable {D : ℕ}

/-! ### Coordinate embeddings -/

/-- The coordinate isometry `E : ℂ^{D'} → ℂ^D`, `|a⟩ ↦ |ι a⟩`. -/
def coordEmbedding {D' : ℕ} (ι : Fin D' → Fin D) : Matrix (Fin D) (Fin D') ℂ :=
  of fun x a => if x = ι a then 1 else 0

/-- `E_ιᴴ E_ι'` has the entry `1` where `ι a = ι' a'` and `0` elsewhere. -/
theorem conjTranspose_coordEmbedding_mul_apply {D' D'' : ℕ} (ι : Fin D' → Fin D)
    (ι' : Fin D'' → Fin D) (a : Fin D') (a' : Fin D'') :
    ((coordEmbedding ι)ᴴ * coordEmbedding ι') a a' = if ι a = ι' a' then 1 else 0 := by
  rw [mul_apply, Finset.sum_eq_single (ι a)]
  · by_cases h : ι a = ι' a' <;> simp [coordEmbedding, conjTranspose_apply, h]
  · intro x _ hx
    simp [coordEmbedding, conjTranspose_apply, hx]
  · simp

/-- An injective coordinate map gives an isometry, `E_ιᴴ E_ι = 1`. -/
theorem conjTranspose_coordEmbedding_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) : (coordEmbedding ι)ᴴ * coordEmbedding ι = 1 := by
  ext a a'
  rw [conjTranspose_coordEmbedding_mul_apply, one_apply]
  exact if_congr hι.eq_iff rfl rfl

/-- Coordinate maps with disjoint ranges give isometries with orthogonal ranges. -/
theorem conjTranspose_coordEmbedding_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') :
    (coordEmbedding ι)ᴴ * coordEmbedding ι' = 0 := by
  ext a a'
  rw [conjTranspose_coordEmbedding_mul_apply, Matrix.zero_apply, ite_eq_right (h a a')]

/-- `E_ιᴴ (E_ι' Y) = 0` for coordinate maps with disjoint ranges. -/
theorem conjTranspose_coordEmbedding_mul_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') {γ : Type*} (Y : Matrix (Fin D'') γ ℂ) :
    (coordEmbedding ι)ᴴ * (coordEmbedding ι' * Y) = 0 := by
  rw [← Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_eq_zero h, Matrix.zero_mul]

/-- `E_ιᴴ (E_ι Y) = Y` for an injective coordinate map. -/
theorem conjTranspose_coordEmbedding_mul_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) {γ : Type*} (Y : Matrix (Fin D') γ ℂ) :
    (coordEmbedding ι)ᴴ * (coordEmbedding ι * Y) = Y := by
  rw [← Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_self hι, Matrix.one_mul]

/-- The isometry `K = E_ι ⊗ E_ι` embedding the bond pairs `ℂ^{D'} ⊗ ℂ^{D'}` of a block into the
bond pairs of the direct sum; these index the columns of the physical matrix. -/
def pairEmbedding {D' : ℕ} (ι : Fin D' → Fin D) : Matrix (Fin D × Fin D) (Fin D' × Fin D') ℂ :=
  coordEmbedding ι ⊗ₖ coordEmbedding ι

theorem pairEmbedding_apply {D' : ℕ} (ι : Fin D' → Fin D) (p : Fin D × Fin D)
    (r : Fin D' × Fin D') : pairEmbedding ι p r = if p = (ι r.1, ι r.2) then 1 else 0 := by
  rcases p with ⟨x, y⟩
  rcases r with ⟨a, c⟩
  simp only [pairEmbedding, kroneckerMap_apply, coordEmbedding, of_apply, Prod.mk.injEq]
  by_cases h1 : x = ι a <;> by_cases h2 : y = ι c <;> simp [h1, h2]

theorem conjTranspose_pairEmbedding_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) : (pairEmbedding ι)ᴴ * pairEmbedding ι = 1 := by
  rw [pairEmbedding, conjTranspose_kronecker, ← mul_kronecker_mul,
    conjTranspose_coordEmbedding_mul_self hι, one_kronecker_one]

theorem conjTranspose_pairEmbedding_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') :
    (pairEmbedding ι)ᴴ * pairEmbedding ι' = 0 := by
  rw [pairEmbedding, pairEmbedding, conjTranspose_kronecker, ← mul_kronecker_mul,
    conjTranspose_coordEmbedding_mul_eq_zero h, zero_kronecker]

/-- A coordinate isometry has real entries: `E_ιᴴ = E_ιᵀ`. -/
theorem conjTranspose_coordEmbedding {D' : ℕ} (ι : Fin D' → Fin D) :
    (coordEmbedding ι)ᴴ = (coordEmbedding ι)ᵀ := by
  ext a x
  by_cases h : x = ι a <;> simp [coordEmbedding, conjTranspose_apply, h]

/-- `√(E σ Eᴴ) = E √σ Eᴴ` for a coordinate isometry `E`. -/
theorem cfc_sqrt_coordEmbedding_mul_mul {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) {σ : Matrix (Fin D') (Fin D') ℂ} (hσ : σ.PosSemidef) :
    CFC.sqrt (coordEmbedding ι * σ * (coordEmbedding ι)ᴴ) =
      coordEmbedding ι * CFC.sqrt σ * (coordEmbedding ι)ᴴ := by
  refine CFC.sqrt_unique ?_ ((Matrix.nonneg_iff_posSemidef.1
    (CFC.sqrt_nonneg σ)).mul_mul_conjTranspose_same _).nonneg
  calc coordEmbedding ι * CFC.sqrt σ * (coordEmbedding ι)ᴴ *
        (coordEmbedding ι * CFC.sqrt σ * (coordEmbedding ι)ᴴ)
      = coordEmbedding ι * (CFC.sqrt σ * ((coordEmbedding ι)ᴴ * coordEmbedding ι) *
          CFC.sqrt σ) * (coordEmbedding ι)ᴴ := by simp only [Matrix.mul_assoc]
    _ = coordEmbedding ι * σ * (coordEmbedding ι)ᴴ := by
        rw [conjTranspose_coordEmbedding_mul_self hι, Matrix.mul_one,
          CFC.sqrt_mul_sqrt_self σ hσ.nonneg]

/-- The fixed point `σ' = E_ι σ E_ιᴴ` of a block, placed in the full bond space along `ι`. -/
noncomputable def embeddedBlockState {D' : ℕ} (ι : Fin D' → Fin D)
    (σ : Matrix (Fin D') (Fin D') ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  coordEmbedding ι * σ * (coordEmbedding ι)ᴴ

/-- `Tr(E σ Eᴴ) = Tr σ` for a coordinate isometry `E`. -/
theorem trace_embeddedBlockState {D' : ℕ} {ι : Fin D' → Fin D} (hι : Function.Injective ι)
    (σ : Matrix (Fin D') (Fin D') ℂ) : (embeddedBlockState ι σ).trace = σ.trace := by
  rw [embeddedBlockState, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    conjTranspose_coordEmbedding_mul_self hι, Matrix.one_mul]

/-- The entries of `E_ι X E_ιᴴ`. -/
theorem coordEmbedding_mul_mul_conjTranspose_apply {D' : ℕ} (ι : Fin D' → Fin D)
    (X : Matrix (Fin D') (Fin D') ℂ) (x y : Fin D) :
    (coordEmbedding ι * X * (coordEmbedding ι)ᴴ) x y =
      ∑ a, ∑ c, if x = ι a ∧ y = ι c then X a c else 0 := by
  simp only [mul_apply, coordEmbedding, conjTranspose_apply, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  by_cases h1 : x = ι a <;> by_cases h2 : y = ι c <;> simp [h1, h2]

/-- `(E_ι X E_ιᴴ)_{ι a, ι c} = X_{a c}` for an injective `ι`. -/
theorem coordEmbedding_mul_mul_conjTranspose_apply_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) (X : Matrix (Fin D') (Fin D') ℂ) (a c : Fin D') :
    (coordEmbedding ι * X * (coordEmbedding ι)ᴴ) (ι a) (ι c) = X a c := by
  rw [coordEmbedding_mul_mul_conjTranspose_apply, Finset.sum_eq_single a, Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    exact ite_eq_right_iff.2 fun h => absurd (hι h.2).symm hc'
  · simp
  · intro a' _ ha'
    exact Finset.sum_eq_zero fun c' _ => ite_eq_right_iff.2 fun h => absurd (hι h.1).symm ha'
  · simp

/-- `E_ι X E_ιᴴ` vanishes off the range of `ι`. -/
theorem coordEmbedding_mul_mul_conjTranspose_apply_eq_zero {D' : ℕ} (ι : Fin D' → Fin D)
    (X : Matrix (Fin D') (Fin D') ℂ) {x y : Fin D} (h : x ∉ Set.range ι ∨ y ∉ Set.range ι) :
    (coordEmbedding ι * X * (coordEmbedding ι)ᴴ) x y = 0 := by
  rw [coordEmbedding_mul_mul_conjTranspose_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ite_eq_right_iff.2 ?_
  rintro ⟨rfl, rfl⟩
  rcases h with h | h
  · exact absurd ⟨a, rfl⟩ h
  · exact absurd ⟨c, rfl⟩ h

end MPSTensor
