/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Auxiliary matrix lemmas

General-purpose matrix lemmas that are not specific to any chapter's theory.
Extracted from various files for reusability.

## Main results

- `Matrix.sum_mul_mul`: pull fixed left/right factors through a finite sum
- `Matrix.finrank_matrix_fin_eq_sq`: square `Fin D` matrices have dimension `D ^ 2`
- `Matrix.dim_le_of_mulVec_injective`: injective mulVec implies dimension bound
- `Matrix.PosSemidef.mulVec_eq_zero_left/right`: kernel containment for PSD matrix sums
- `Matrix.sum_single_diag_const`: diagonal matrix units with a common entry sum to `c • 1`
- `Matrix.each_zero_of_sum_conjTranspose_mul_self_zero`: a vanishing sum `∑ i, Rᵢᴴ * Rᵢ`
  forces each `Rᵢ = 0`
- `Matrix.IsHermitian.mul_posDef_mul_self_ne_zero`: `P * ρ * P ≠ 0` for nonzero Hermitian `P`
  and positive-definite `ρ`
- `Matrix.trace_eq_of_charpoly_eq`: equal characteristic polynomials imply equal traces
-/

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

/-- The complex vector-space dimension of `D × D` matrices is `D ^ 2`. -/
theorem finrank_matrix_fin_eq_sq (D : ℕ) :
    Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) = D ^ 2 := by
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
  ring

/-- The top submodule of `D × D` matrices has dimension `D ^ 2`. -/
theorem finrank_top_matrix_fin_eq_sq (D : ℕ) :
    Module.finrank ℂ (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) = D ^ 2 := by
  simpa using finrank_matrix_fin_eq_sq D

/-- Pull fixed left and right matrix factors through a finite sum indexed by `Fin d`. -/
theorem sum_mul_mul {α : Type*} [NonUnitalNonAssocSemiring α]
    {d l m n r : ℕ} (L : Matrix (Fin l) (Fin m) α)
    (M : Fin d → Matrix (Fin m) (Fin n) α) (R : Matrix (Fin n) (Fin r) α) :
    ∑ i : Fin d, L * M i * R = L * (∑ i : Fin d, M i) * R := by
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum]

/-- If multiplication by a rectangular matrix has trivial kernel, then the source dimension is at
most the target dimension. -/
theorem dim_le_of_mulVec_injective {D₁ D₂ : ℕ} [NeZero D₂]
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (h_inj : ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0) :
    D₂ ≤ D₁ := by
  let f : (Fin D₂ → ℂ) →ₗ[ℂ] (Fin D₁ → ℂ) := Matrix.toLin' X
  have hf_inj : Function.Injective f := by
    intro u v huv
    have h_sub : f (u - v) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp <| h_inj _ h_sub
  have hfinrank : Module.finrank ℂ (Fin D₂ → ℂ) ≤ Module.finrank ℂ (Fin D₁ → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hf_inj
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hfinrank

end Matrix

/-! ## Kernel intersection for PSD matrices -/

section KernelPSD

open Matrix

variable {D : ℕ}

namespace Matrix.PosSemidef

/-- For PSD matrices `A` and `B`, `ker(A + B) ⊆ ker(A)`.
Proof: `v†(A+B)v = v†Av + v†Bv = 0` with both nonneg implies `v†Av = 0`. -/
theorem mulVec_eq_zero_left
    {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : Fin D → ℂ) (hv : (A + B) *ᵥ v = 0) :
    A *ᵥ v = 0 := by
  have hqf : star v ⬝ᵥ ((A + B) *ᵥ v) = 0 := by rw [hv]; simp
  rw [add_mulVec, dotProduct_add] at hqf
  have h1_re := hA.re_dotProduct_nonneg v
  have h2_re := hB.re_dotProduct_nonneg v
  have h3_re : (star v ⬝ᵥ (A *ᵥ v)).re + (star v ⬝ᵥ (B *ᵥ v)).re = 0 := by
    have := congr_arg Complex.re hqf; simpa using this
  change 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re at h1_re
  change 0 ≤ (star v ⬝ᵥ (B *ᵥ v)).re at h2_re
  have hre : (star v ⬝ᵥ (A *ᵥ v)).re = 0 := by linarith
  exact (hA.dotProduct_mulVec_zero_iff v).mp
    (Complex.ext hre (hA.isHermitian.im_star_dotProduct_mulVec_self v))

/-- For PSD matrices `A` and `B`, `ker(A + B) ⊆ ker(B)`. -/
theorem mulVec_eq_zero_right
    {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : Fin D → ℂ) (hv : (A + B) *ᵥ v = 0) :
    B *ᵥ v = 0 := by
  exact mulVec_eq_zero_left hB hA v (by simpa [add_comm] using hv)

end Matrix.PosSemidef

end KernelPSD

/-! ## Sums of conjugated squares and matrix units -/

section ConjSquares

namespace Matrix

/-- The sum of diagonal matrix units with a common scalar entry is that scalar times the
identity: `∑ i, single i i c = c • 1`. -/
theorem sum_single_diag_const {D : ℕ} (c : ℂ) :
    ∑ i : Fin D, Matrix.single i i c = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  rw [Matrix.sum_single_eq_diagonal, Matrix.smul_one_eq_diagonal]

/-- If a finite sum `∑ i, Rᵢᴴ * Rᵢ` of conjugated squares vanishes, then each summand
matrix `Rᵢ` vanishes. -/
theorem each_zero_of_sum_conjTranspose_mul_self_zero
    {ι n : Type*} [Fintype ι] [Fintype n]
    (R : ι → Matrix n n ℂ)
    (h : ∑ i : ι, (R i)ᴴ * R i = 0) :
    ∀ i : ι, R i = 0 := by
  intro i
  have h_psd_i := Matrix.posSemidef_conjTranspose_mul_self (R i)
  have h_each_nonneg : ∀ j : ι, 0 ≤ ((R j)ᴴ * R j).trace.re :=
    fun j => (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self (R j)).trace_nonneg).1
  have h_tr_sum_re : (∑ j : ι, ((R j)ᴴ * R j).trace.re) = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, h]
    simp
  have h_tr_re : ((R i)ᴴ * R i).trace.re = 0 :=
    le_antisymm
      (by
        linarith [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_each_nonneg j)
            |>.mp h_tr_sum_re i (Finset.mem_univ i)])
      (h_each_nonneg i)
  have h_tr_zero : ((R i)ᴴ * R i).trace = 0 :=
    Complex.ext h_tr_re (Complex.le_def.mp h_psd_i.trace_nonneg).2.symm
  exact Matrix.conjTranspose_mul_self_eq_zero.mp (h_psd_i.trace_eq_zero_iff.mp h_tr_zero)

/-- For a nonzero Hermitian `P` and a positive-definite `ρ`, the two-sided compression
`P * ρ * P` is nonzero. Idempotence of `P` is not needed. -/
theorem IsHermitian.mul_posDef_mul_self_ne_zero {D : ℕ}
    {P ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP_herm : P.IsHermitian) (hP_ne : P ≠ 0) (hρ_pd : ρ.PosDef) :
    P * ρ * P ≠ 0 := by
  intro h0
  apply hP_ne
  have hPv_zero : ∀ v : Fin D → ℂ, P *ᵥ v = 0 := by
    intro v
    by_contra hne
    set w := P *ᵥ v
    have hρ_pos : (0 : ℂ) < star w ⬝ᵥ (ρ.mulVec w) :=
      hρ_pd.dotProduct_mulVec_pos hne
    have h_zero : star v ⬝ᵥ ((P * ρ * P) *ᵥ v) = 0 := by
      rw [h0]
      simp [zero_mulVec, dotProduct_zero]
    have h_expand : (P * ρ * P) *ᵥ v = P *ᵥ (ρ *ᵥ w) := by
      change (P * ρ * P) *ᵥ v = P *ᵥ (ρ *ᵥ (P *ᵥ v))
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [h_expand] at h_zero
    rw [Matrix.dotProduct_mulVec] at h_zero
    have h_key : Matrix.vecMul (star v) P = star w := by
      apply star_injective
      rw [star_star]
      have := star_vecMul P (star v)
      rw [star_star, hP_herm.eq] at this
      exact this
    rw [h_key] at h_zero
    linarith
  ext i j
  have h := congr_fun (hPv_zero (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_boole, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  simpa using h

end Matrix

end ConjSquares

/-! ## Characteristic polynomial lemmas -/

section CharpolyAux

namespace Matrix

/-- If two square matrices over `ℂ` have the same characteristic polynomial, they have the same
trace. This follows from the fact that the trace is the negation of the next-to-leading coefficient
of the characteristic polynomial. -/
theorem trace_eq_of_charpoly_eq
    {D : ℕ} [NeZero D]
    (T U : Matrix (Fin D) (Fin D) ℂ)
    (h : T.charpoly = U.charpoly) :
    Matrix.trace T = Matrix.trace U := by
  have : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (NeZero.pos D)
  have hT := Matrix.trace_eq_neg_charpoly_coeff T
  have hU := Matrix.trace_eq_neg_charpoly_coeff U
  rw [hT, hU, h]

end Matrix

end CharpolyAux
