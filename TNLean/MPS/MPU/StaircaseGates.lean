/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.MPU.StandardForm

/-!
# Staircase gates and the first network identity

The gates are the literal crossed contractions in arXiv:2502.20257,
`eq:wLR` (lines 811–869). Rows are the upper legs, columns the lower legs,
in spatial left-to-right order. Thus $w_L:d\times\ell\to\ell\times d$
and $w_R:r\times d\to d\times r$. Red horizontal legs are virtual indices.

The first diagram in the proof of `cor:mpu` (lines 918–974) follows from
the two source factorizations alone. Cancelling its bottom middle gate
requires only $uu^\dagger=I$, already part of the source theorem's unitary
claim. This file does not establish the second network or scalar normalization.
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

/-- Place a two-leg gate on the middle legs of a four-leg space. The explicit
reshuffle sends `((a,b),(c,e))` to `((a,(b,c)),e)` before applying
$(I\otimes M)\otimes I$. This is the leg convention in arXiv:2502.20257,
the first diagram in the proof of `cor:mpu`, lines 918–974. -/
def staircaseMiddle {A B C B' C' E : Type*} [DecidableEq A] [DecidableEq E]
    (M : Matrix (B × C) (B' × C') ℂ) :
    Matrix ((A × B) × (C × E)) ((A × B') × (C' × E)) ℂ :=
  (((1 : Matrix A A ℂ) ⊗ₖ M) ⊗ₖ (1 : Matrix E E ℂ)).submatrix
    (fun x ↦ ((x.1.1, (x.1.2, x.2.1)), x.2.2))
    (fun x ↦ ((x.1.1, (x.1.2, x.2.1)), x.2.2))

/-- Composition of middle layers preserves the explicit reshuffle used in
arXiv:2502.20257, proof of `cor:mpu`, lines 968–974. -/
theorem staircaseMiddle_mul {A B C B' C' B'' C'' E : Type*}
    [Fintype A] [Fintype B'] [Fintype C'] [Fintype E]
    [DecidableEq A] [DecidableEq E]
    (M : Matrix (B × C) (B' × C') ℂ)
    (N : Matrix (B' × C') (B'' × C'') ℂ) :
    staircaseMiddle (A := A) (E := E) M * staircaseMiddle N =
      staircaseMiddle (M * N) := by
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  simp [staircaseMiddle, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul,
    Finset.sum_ite_irrel]

/-- The middle identity layer is the four-leg identity, in the reshuffle of
arXiv:2502.20257, proof of `cor:mpu`, lines 968–974. -/
theorem staircaseMiddle_one {A B C E : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] :
    staircaseMiddle (A := A) (E := E) (1 : Matrix (B × C) (B × C) ℂ) = 1 := by
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  simp [staircaseMiddle, Matrix.one_apply, Prod.mk.injEq]
  aesop

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- $w_L=Y_2\mathbin{-}X_2$, with rows $(\ell,i)$ and columns $(j,\ell')$.
Source: arXiv:2502.20257, `eq:wLR`, lines 811–869. -/
def sourceWL {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin ℓ[U] × Fin d) (Fin d × Fin ℓ[U]) ℂ :=
  fun (l, i) (j, l') ↦ ∑ β, S.Y₂ l (j, β) * S.X₂ (β, i) l'

/-- $w_R=X_1\mathbin{-}Y_1$, with rows $(i,r)$ and columns $(r',j)$.
Source: arXiv:2502.20257, `eq:wLR`, lines 811–869. -/
def sourceWR {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin d × Fin r[U]) (Fin r[U] × Fin d) ℂ :=
  fun (i, r) (r', j) ↦ ∑ β, S.X₁ (i, β) r' * S.Y₁ r (β, j)

/-- The first graphical equality before cancelling the bottom middle $u$.
No simplicity, normalization or unitarity hypothesis is needed: replace
both middle two-site contractions by the same product of tensor letters.
Source: arXiv:2502.20257, proof of `cor:mpu`, lines 918–968. -/
theorem sourceWL_kronecker_sourceWR_mul_middle_sourceU
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    (sourceWL U S ⊗ₖ sourceWR U S) * staircaseMiddle (sourceU U S) =
      staircaseMiddle (sourceV U S) * (sourceU U S ⊗ₖ sourceU U S) := by
  classical
  ext ⟨⟨l, i₂⟩, i₃, r⟩ ⟨⟨j₁, j₂⟩, j₃, j₄⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, staircaseMiddle,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  trans ∑ γ : Fin D, ∑ α : Fin D,
    S.Y₂ l (j₁, α) * (U i₂ j₂ * U i₃ j₃) α γ * S.Y₁ r (γ, j₄)
  · simp only [sourceWL, sourceWR, Finset.sum_mul, Finset.mul_sum]
    rw [Fintype.sum_last_two_first_four]
    refine Finset.sum_congr₂ fun γ _ α _ ↦ ?_
    rw [mul_apply_eq_sum_X₂_mul_sourceU_mul_X₁ U S]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr₂ fun l' _ r' _ ↦ by ring
  · symm
    simp only [sourceU_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Fintype.sum_last_two_first_four]
    refine Finset.sum_congr₂ fun γ _ α _ ↦ ?_
    rw [mul_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂ U S]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr₂ fun r' _ l' _ ↦ by ring

/-- The displayed first staircase network identity
$w_L\otimes w_R=(I\otimes v\otimes I)(u\otimes u)(I\otimes u^\dagger\otimes I)$,
with every middle-layer reshuffle explicit. The sole extra premise is
$uu^\dagger=I$, the coisometry half of the unitarity of $u$ supplied by
arXiv:2502.20257, Theorem `thm:mpu`. It is not a premise about either staircase
gate, nor an assumed network equality. In particular, this theorem does not
assert that arbitrary source factors give a unitary $u$.

Source: arXiv:2502.20257, proof of `cor:mpu`, lines 918–974. -/
theorem sourceWL_kronecker_sourceWR_eq
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hu : (sourceU U S).IsCoisometry) :
    sourceWL U S ⊗ₖ sourceWR U S =
      staircaseMiddle (sourceV U S) * (sourceU U S ⊗ₖ sourceU U S) *
        staircaseMiddle ((sourceU U S)ᴴ) := by
  calc
    _ = ((sourceWL U S ⊗ₖ sourceWR U S) * staircaseMiddle (sourceU U S)) *
        staircaseMiddle ((sourceU U S)ᴴ) := by
      rw [Matrix.mul_assoc, staircaseMiddle_mul, hu, staircaseMiddle_one,
        Matrix.mul_one]
    _ = _ := by rw [sourceWL_kronecker_sourceWR_mul_middle_sourceU U S]

end SourceFactors
end MPOTensor
