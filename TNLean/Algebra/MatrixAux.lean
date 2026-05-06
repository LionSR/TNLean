/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
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
- `Matrix.trace_eq_of_charpoly_eq`: equal characteristic polynomials imply equal traces
-/

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

/-- The complex vector-space dimension of `D × D` matrices is `D ^ 2`. -/
theorem finrank_matrix_fin_eq_sq (D : ℕ) :
    Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) = D ^ 2 := by
  calc
    Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ)
        = Fintype.card (Fin D) * Fintype.card (Fin D) * Module.finrank ℂ ℂ :=
            Module.finrank_matrix ℂ ℂ _ _
    _ = D * D * 1 := by
          simp only [Fintype.card_fin, Module.finrank_self, mul_one]
    _ = D ^ 2 := by ring

/-- The top submodule of `D × D` matrices has dimension `D ^ 2`. -/
theorem finrank_top_matrix_fin_eq_sq (D : ℕ) :
    Module.finrank ℂ (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) = D ^ 2 := by
  simpa using finrank_matrix_fin_eq_sq D

/-- Pull fixed left and right matrix factors through a finite sum indexed by `Fin d`. -/
theorem sum_mul_mul {α : Type*} [NonUnitalNonAssocSemiring α]
    {d l m n r : ℕ} (L : Matrix (Fin l) (Fin m) α)
    (M : Fin d → Matrix (Fin m) (Fin n) α) (R : Matrix (Fin n) (Fin r) α) :
    ∑ i : Fin d, L * M i * R = L * (∑ i : Fin d, M i) * R := by
  calc
    ∑ i : Fin d, L * M i * R = (∑ i : Fin d, L * M i) * R := by
      simpa [Matrix.mul_assoc] using
        (Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
          (f := fun i : Fin d => L * M i) (M := R)).symm
    _ = (L * ∑ i : Fin d, M i) * R := by
      exact congrArg (fun T => T * R) <|
        (Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
          (f := fun i : Fin d => M i) (M := L)).symm

/-- If multiplication by a rectangular matrix has trivial kernel, then the source dimension is at
most the target dimension. -/
theorem dim_le_of_mulVec_injective {D₁ D₂ : ℕ} [NeZero D₂]
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (h_inj : ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0) :
    D₂ ≤ D₁ := by
  let f : (Fin D₂ → ℂ) →ₗ[ℂ] (Fin D₁ → ℂ) := Matrix.toLin' X
  have hf_inj : Function.Injective f := by
    intro u v huv
    have h_sub : f (u - v) = 0 := by
      simpa using congrArg (fun w => w - f v) huv
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
