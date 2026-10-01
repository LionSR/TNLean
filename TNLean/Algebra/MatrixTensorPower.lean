/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Set
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Tensor powers of rectangular matrices

The `M`-fold tensor power `W^{⊗M}` of a rectangular complex matrix `W : Matrix ι κ ℂ`, as a
matrix indexed by configurations `Fin M → ι` and `Fin M → κ`. For square families the
finite Kronecker product `Matrix.finKronecker` covers the same construction; this file
allows different row and column index types, as needed for the isometry
`W : |j⟩ ↦ |ω_j⟩` of arXiv:2307.01696, the paragraph after eq. (19).

## Main declarations

* `Matrix.tensorPower` — the matrix `W^{⊗M}` with entries `∏ₖ W (p k) (s k)`.
* `Matrix.tensorPower_mul` — the tensor power is multiplicative.
* `Matrix.IsIsometry.tensorPower` — the tensor power of an isometry is an isometry.
* `Matrix.tensorPower_one`, `Matrix.tensorPower_zero` — tensor powers of `1` and `0`.
* `Matrix.conjTranspose_tensorPower` — `(W^{⊗M})ᴴ = (Wᴴ)^{⊗M}`.
* `Matrix.sum_star_tensorPower_mulVec_mul`, `Matrix.sum_norm_sq_tensorPower_mulVec_le` —
  inner products and norms after a tensor power of a partial isometry.
-/

open scoped BigOperators Matrix ComplexOrder

namespace Matrix

/-- The `M`-fold tensor power `W^{⊗M}` of a matrix `W`, as a matrix indexed by
configurations of `M` sites: its entry at `(p, s)` is `∏ₖ W (p k) (s k)`
(arXiv:2307.01696, the map `W^{⊗M}` in the paragraph after eq. (19)). -/
def tensorPower {ι κ : Type*} (M : ℕ) (W : Matrix ι κ ℂ) : Matrix (Fin M → ι) (Fin M → κ) ℂ :=
  Matrix.of fun p s => ∏ k, W (p k) (s k)

/-- The tensor power of a product is the product of the tensor powers:
`X^{⊗M} Y^{⊗M} = (X Y)^{⊗M}`. -/
theorem tensorPower_mul {ι₁ ι₂ ι₃ : Type*} [Fintype ι₂] (M : ℕ) (X : Matrix ι₁ ι₂ ℂ)
    (Y : Matrix ι₂ ι₃ ℂ) :
    tensorPower M X * tensorPower M Y = tensorPower M (X * Y) := by
  ext s t
  simp only [mul_apply, tensorPower, of_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun τ _ => (Finset.prod_mul_distrib).symm

/-- The tensor power of an isometry is an isometry, so `W^{⊗M}` in arXiv:2307.01696,
the paragraph after eq. (19), is an isometry from `(ℂ^b)^{⊗M}` to the bonds. -/
theorem IsIsometry.tensorPower {ι κ : Type*} [Fintype ι] [DecidableEq κ] (M : ℕ)
    {W : Matrix ι κ ℂ} (hW : W.IsIsometry) : (Matrix.tensorPower M W).IsIsometry := by
  ext s t
  have hWe : ∀ a c, ∑ i, star (W i a) * W i c = if a = c then 1 else 0 := fun a c => by
    have := congrFun (congrFun hW a) c
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.tensorPower, Matrix.of_apply,
    star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k i => star (W i (s k)) * W i (t k))]
  simp_rw [hWe, Matrix.one_apply]
  by_cases h : s = t
  · subst h; simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    rw [ite_eq_right_iff.2 fun h' => absurd h' h]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right_iff.2 fun h' => absurd h' hk)

/-- The tensor power of the identity is the identity. -/
theorem tensorPower_one {κ : Type*} [DecidableEq κ] (M : ℕ) :
    tensorPower M (1 : Matrix κ κ ℂ) = 1 := by
  ext s t
  simp only [tensorPower, of_apply, one_apply]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  exact if_congr funext_iff.symm rfl rfl

/-- The tensor power of the zero matrix on `M ≥ 1` sites is zero. -/
theorem tensorPower_zero {ι κ : Type*} {M : ℕ} (hM : M ≠ 0) :
    tensorPower M (0 : Matrix ι κ ℂ) = 0 := by
  ext s t
  simp only [tensorPower, of_apply, zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hM⟩) rfl

/-! ### Partial isometries on many sites -/

/-- The conjugate transpose of a tensor power is the tensor power of the conjugate transpose:
`(W^{⊗M})ᴴ = (Wᴴ)^{⊗M}`. -/
theorem conjTranspose_tensorPower {ι κ : Type*} (M : ℕ) (W : Matrix ι κ ℂ) :
    (tensorPower M W)ᴴ = tensorPower M Wᴴ := by
  ext s t
  simp [tensorPower, conjTranspose_apply, star_prod]

/-- `⟨W^{⊗M} ψ, W'^{⊗M} φ⟩ = ⟨ψ, (Wᴴ W')^{⊗M} φ⟩`. -/
theorem sum_star_tensorPower_mulVec_mul {n κ κ' : Type*} [Fintype n] [Fintype κ] [Fintype κ']
    (W : Matrix n κ ℂ) (W' : Matrix n κ' ℂ) {M : ℕ} (ψ : (Fin M → κ) → ℂ)
    (φ : (Fin M → κ') → ℂ) :
    ∑ s, star ((tensorPower M W *ᵥ ψ) s) * (tensorPower M W' *ᵥ φ) s =
      ∑ τ, star (ψ τ) * (tensorPower M (Wᴴ * W') *ᵥ φ) τ := by
  change star (tensorPower M W *ᵥ ψ) ⬝ᵥ (tensorPower M W' *ᵥ φ) =
    star ψ ⬝ᵥ (tensorPower M (Wᴴ * W') *ᵥ φ)
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_tensorPower,
    tensorPower_mul]

/-- **Partial isometries do not increase norms.** If `Wᴴ W` is a projector, then
`‖W^{⊗M} ψ‖ ≤ ‖ψ‖`. For the partial isometry `V` of the polar decomposition, `Vᴴ V = Π` is the
projector onto the range of `P` (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors"). -/
theorem sum_norm_sq_tensorPower_mulVec_le {n κ : Type*} [Fintype n] [Fintype κ]
    {W : Matrix n κ ℂ} (hidem : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W) {M : ℕ}
    (ψ : (Fin M → κ) → ℂ) :
    ∑ s, ‖(tensorPower M W *ᵥ ψ) s‖ ^ 2 ≤ ∑ τ, ‖ψ τ‖ ^ 2 := by
  classical
  set Pr := tensorPower M (Wᴴ * W)
  have hH : Prᴴ = Pr := by
    rw [conjTranspose_tensorPower, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hI : Pr * Pr = Pr := by rw [tensorPower_mul, hidem]
  have hpsd : (1 - Pr).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - Pr)
    have e : (1 - Pr)ᴴ * (1 - Pr) = 1 - Pr := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hI]
      abel
    rwa [e] at h
  have hnn := hpsd.dotProduct_mulVec_nonneg ψ
  have h1 : ((∑ s, ‖(tensorPower M W *ᵥ ψ) s‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, star ((tensorPower M W *ᵥ ψ) s) * (tensorPower M W *ᵥ ψ) s := by
    push_cast
    exact Finset.sum_congr rfl fun x _ => by rw [Complex.star_def, Complex.conj_mul']
  have h2 : ((∑ τ, ‖ψ τ‖ ^ 2 : ℝ) : ℂ) = ∑ τ, star (ψ τ) * ψ τ := by
    push_cast
    exact Finset.sum_congr rfl fun x _ => by rw [Complex.star_def, Complex.conj_mul']
  rw [sum_star_tensorPower_mulVec_mul] at h1
  have key : ((∑ τ, ‖ψ τ‖ ^ 2 - ∑ s, ‖(tensorPower M W *ᵥ ψ) s‖ ^ 2 : ℝ) : ℂ) =
      star ψ ⬝ᵥ ((1 - Pr) *ᵥ ψ) := by
    rw [Complex.ofReal_sub, h1, h2, sub_mulVec, one_mulVec, dotProduct_sub]
    rfl
  rw [← key] at hnn
  have := Complex.zero_le_real.1 hnn
  linarith

end Matrix
