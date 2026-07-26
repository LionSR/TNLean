/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionFourfold

/-!
# Pentagon coherence for complete zipper fusion data

The five elementary printed $F$-moves identify the two paths between the fully left- and
fully right-associated fourfold fusion trees.  Cancelling the common right-associated
synthesis map proves equality of the forward composites.  The inverse edges then give the
literal upper/lower index placement of the pentagon printed in arXiv:1511.08090.
The multiplicities are those of `CompleteZipperFusionFamily`, not the positive-diagonal
weighted coordinates of `BNTFusionIsometryFamily`.

**Local fix (equation `pentagoneq`):** The source prints the entries in equation
`pentagoneq` with the opposite upper/lower placement from equation `Fmove`.  The forward edges
follow `Fmove`, with right-tree rows and left-tree columns.  The literal index placement in
`pentagoneq` therefore belongs to the inverse edges.  This correction is documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

## References

* arXiv:1511.08090, `AnyonsPEPS.tex`, equations `Fmove` and `pentagoneq`, lines 248--299.
* arXiv:1606.00608, Theorem 4.14 and the discussion at lines 995--999.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

/-! ### Regroupings for the five printed `F`-moves -/

private def leftPathFirstSourceEquiv (a b c d e : Λ) :
    Fus.FourfoldLeftAssocMultiplicity a b c d e ≃
      (g : Λ) × (Fus.LeftTripleMultiplicity a b c g ×
        Fin (Fus.fusionMultiplicity g d e)) where
  toFun
    | ⟨f, g, mu, nu, rho⟩ => ⟨g, ⟨⟨f, mu, nu⟩, rho⟩⟩
  invFun
    | ⟨g, ⟨⟨f, mu, nu⟩, rho⟩⟩ => ⟨f, g, mu, nu, rho⟩
  left_inv := by rintro ⟨f, g, mu, nu, rho⟩; rfl
  right_inv := by rintro ⟨g, ⟨⟨f, mu, nu⟩, rho⟩⟩; rfl

private def leftPathFirstTargetEquiv (a b c d e : Λ) :
    Fus.FourfoldLeftInnerMultiplicity a b c d e ≃
      (g : Λ) × (Fus.RightTripleMultiplicity a b c g ×
        Fin (Fus.fusionMultiplicity g d e)) where
  toFun
    | ⟨h, g, sigma, lambda, rho⟩ => ⟨g, ⟨⟨h, sigma, lambda⟩, rho⟩⟩
  invFun
    | ⟨g, ⟨⟨h, sigma, lambda⟩, rho⟩⟩ => ⟨h, g, sigma, lambda, rho⟩
  left_inv := by rintro ⟨h, g, sigma, lambda, rho⟩; rfl
  right_inv := by rintro ⟨g, ⟨⟨h, sigma, lambda⟩, rho⟩⟩; rfl

private def leftPathSecondSourceEquiv (a b c d e : Λ) :
    Fus.FourfoldLeftInnerMultiplicity a b c d e ≃
      (h : Λ) × (Fin (Fus.fusionMultiplicity b c h) ×
        Fus.LeftTripleMultiplicity a h d e) where
  toFun
    | ⟨h, g, sigma, lambda, rho⟩ => ⟨h, ⟨sigma, ⟨g, lambda, rho⟩⟩⟩
  invFun
    | ⟨h, ⟨sigma, ⟨g, lambda, rho⟩⟩⟩ => ⟨h, g, sigma, lambda, rho⟩
  left_inv := by rintro ⟨h, g, sigma, lambda, rho⟩; rfl
  right_inv := by rintro ⟨h, ⟨sigma, ⟨g, lambda, rho⟩⟩⟩; rfl

private def leftPathSecondTargetEquiv (a b c d e : Λ) :
    Fus.FourfoldMiddleMultiplicity a b c d e ≃
      (h : Λ) × (Fin (Fus.fusionMultiplicity b c h) ×
        Fus.RightTripleMultiplicity a h d e) where
  toFun
    | ⟨h, i, sigma, omega, kappa⟩ => ⟨h, ⟨sigma, ⟨i, omega, kappa⟩⟩⟩
  invFun
    | ⟨h, ⟨sigma, ⟨i, omega, kappa⟩⟩⟩ => ⟨h, i, sigma, omega, kappa⟩
  left_inv := by rintro ⟨h, i, sigma, omega, kappa⟩; rfl
  right_inv := by rintro ⟨h, ⟨sigma, ⟨i, omega, kappa⟩⟩⟩; rfl

private def leftPathThirdSourceEquiv (a b c d e : Λ) :
    Fus.FourfoldMiddleMultiplicity a b c d e ≃
      (i : Λ) × (Fus.LeftTripleMultiplicity b c d i ×
        Fin (Fus.fusionMultiplicity a i e)) where
  toFun
    | ⟨h, i, sigma, omega, kappa⟩ => ⟨i, ⟨⟨h, sigma, omega⟩, kappa⟩⟩
  invFun
    | ⟨i, ⟨⟨h, sigma, omega⟩, kappa⟩⟩ => ⟨h, i, sigma, omega, kappa⟩
  left_inv := by rintro ⟨h, i, sigma, omega, kappa⟩; rfl
  right_inv := by rintro ⟨i, ⟨⟨h, sigma, omega⟩, kappa⟩⟩; rfl

private def leftPathThirdTargetEquiv (a b c d e : Λ) :
    Fus.FourfoldRightAssocMultiplicity a b c d e ≃
      (i : Λ) × (Fus.RightTripleMultiplicity b c d i ×
        Fin (Fus.fusionMultiplicity a i e)) where
  toFun
    | ⟨j, i, gamma, delta, kappa⟩ => ⟨i, ⟨⟨j, gamma, delta⟩, kappa⟩⟩
  invFun
    | ⟨i, ⟨⟨j, gamma, delta⟩, kappa⟩⟩ => ⟨j, i, gamma, delta, kappa⟩
  left_inv := by rintro ⟨j, i, gamma, delta, kappa⟩; rfl
  right_inv := by rintro ⟨i, ⟨⟨j, gamma, delta⟩, kappa⟩⟩; rfl

private def rightPathFirstSourceEquiv (a b c d e : Λ) :
    Fus.FourfoldLeftAssocMultiplicity a b c d e ≃
      (f : Λ) × (Fin (Fus.fusionMultiplicity a b f) ×
        Fus.LeftTripleMultiplicity f c d e) where
  toFun
    | ⟨f, g, mu, nu, rho⟩ => ⟨f, ⟨mu, ⟨g, nu, rho⟩⟩⟩
  invFun
    | ⟨f, ⟨mu, ⟨g, nu, rho⟩⟩⟩ => ⟨f, g, mu, nu, rho⟩
  left_inv := by rintro ⟨f, g, mu, nu, rho⟩; rfl
  right_inv := by rintro ⟨f, ⟨mu, ⟨g, nu, rho⟩⟩⟩; rfl

private def rightPathFirstTargetEquiv (a b c d e : Λ) :
    Fus.FourfoldPairMultiplicity a b c d e ≃
      (f : Λ) × (Fin (Fus.fusionMultiplicity a b f) ×
        Fus.RightTripleMultiplicity f c d e) where
  toFun
    | ⟨f, j, mu, gamma, tau⟩ => ⟨f, ⟨mu, ⟨j, gamma, tau⟩⟩⟩
  invFun
    | ⟨f, ⟨mu, ⟨j, gamma, tau⟩⟩⟩ => ⟨f, j, mu, gamma, tau⟩
  left_inv := by rintro ⟨f, j, mu, gamma, tau⟩; rfl
  right_inv := by rintro ⟨f, ⟨mu, ⟨j, gamma, tau⟩⟩⟩; rfl

private def rightPathSecondSourceEquiv (a b c d e : Λ) :
    Fus.FourfoldPairMultiplicity a b c d e ≃
      (j : Λ) × (Fus.LeftTripleMultiplicity a b j e ×
        Fin (Fus.fusionMultiplicity c d j)) where
  toFun
    | ⟨f, j, mu, gamma, tau⟩ => ⟨j, ⟨⟨f, mu, tau⟩, gamma⟩⟩
  invFun
    | ⟨j, ⟨⟨f, mu, tau⟩, gamma⟩⟩ => ⟨f, j, mu, gamma, tau⟩
  left_inv := by rintro ⟨f, j, mu, gamma, tau⟩; rfl
  right_inv := by rintro ⟨j, ⟨⟨f, mu, tau⟩, gamma⟩⟩; rfl

private def rightPathSecondTargetEquiv (a b c d e : Λ) :
    Fus.FourfoldRightAssocMultiplicity a b c d e ≃
      (j : Λ) × (Fus.RightTripleMultiplicity a b j e ×
        Fin (Fus.fusionMultiplicity c d j)) where
  toFun
    | ⟨j, i, gamma, delta, kappa⟩ => ⟨j, ⟨⟨i, delta, kappa⟩, gamma⟩⟩
  invFun
    | ⟨j, ⟨⟨i, delta, kappa⟩, gamma⟩⟩ => ⟨j, i, gamma, delta, kappa⟩
  left_inv := by rintro ⟨j, i, gamma, delta, kappa⟩; rfl
  right_inv := by rintro ⟨j, ⟨⟨i, delta, kappa⟩, gamma⟩⟩; rfl

/-! ### The five lifted printed `F`-matrices -/

/-- The `F^{abc}_g` edge from `(((a b) c) d) -> e` to `((a (b c)) d) -> e`.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, and the first factor of
equation `pentagoneq`, lines 280--281. -/
noncomputable def leftAssocToLeftInnerPrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldLeftInnerMultiplicity a b c d e)
      (Fus.FourfoldLeftAssocMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun g => Fus.printedFMatrix a b c g ⊗ₖ
    (1 : Matrix (Fin (Fus.fusionMultiplicity g d e))
      (Fin (Fus.fusionMultiplicity g d e)) ℂ)).submatrix
        (Fus.leftPathFirstTargetEquiv a b c d e)
        (Fus.leftPathFirstSourceEquiv a b c d e)

/-- The `F^{ahd}_e` edge from `((a (b c)) d) -> e` to `a ((b c) d) -> e`.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, and the second factor of
equation `pentagoneq`, lines 280--281. -/
noncomputable def leftInnerToMiddlePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldMiddleMultiplicity a b c d e)
      (Fus.FourfoldLeftInnerMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun h =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity b c h))
      (Fin (Fus.fusionMultiplicity b c h)) ℂ) ⊗ₖ Fus.printedFMatrix a h d e).submatrix
        (Fus.leftPathSecondTargetEquiv a b c d e)
        (Fus.leftPathSecondSourceEquiv a b c d e)

/-- The `F^{bcd}_i` edge from `a ((b c) d) -> e` to `a (b (c d)) -> e`.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, and the third factor of
equation `pentagoneq`, lines 280--281. -/
noncomputable def middleToRightAssocPrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e)
      (Fus.FourfoldMiddleMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun i => Fus.printedFMatrix b c d i ⊗ₖ
    (1 : Matrix (Fin (Fus.fusionMultiplicity a i e))
      (Fin (Fus.fusionMultiplicity a i e)) ℂ)).submatrix
        (Fus.leftPathThirdTargetEquiv a b c d e)
        (Fus.leftPathThirdSourceEquiv a b c d e)

/-- The `F^{fcd}_e` edge from `(((a b) c) d) -> e` to `(a b) (c d) -> e`.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, and the first factor on the
right-hand side of equation `pentagoneq`, lines 282--283. -/
noncomputable def leftAssocToPairPrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldPairMultiplicity a b c d e)
      (Fus.FourfoldLeftAssocMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun f =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity a b f))
      (Fin (Fus.fusionMultiplicity a b f)) ℂ) ⊗ₖ Fus.printedFMatrix f c d e).submatrix
        (Fus.rightPathFirstTargetEquiv a b c d e)
        (Fus.rightPathFirstSourceEquiv a b c d e)

/-- The `F^{abj}_e` edge from `(a b) (c d) -> e` to `a (b (c d)) -> e`.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, and the second factor on the
right-hand side of equation `pentagoneq`, lines 282--283. -/
noncomputable def pairToRightAssocPrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e)
      (Fus.FourfoldPairMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun j => Fus.printedFMatrix a b j e ⊗ₖ
    (1 : Matrix (Fin (Fus.fusionMultiplicity c d j))
      (Fin (Fus.fusionMultiplicity c d j)) ℂ)).submatrix
        (Fus.rightPathSecondTargetEquiv a b c d e)
        (Fus.rightPathSecondSourceEquiv a b c d e)

/-! ### The five lifted inverse-orientation `F`-matrices -/

/-- The inverse-orientation `F^{abc}_g` edge from the left-inner tree to
the left-associated tree.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
noncomputable def leftInnerToLeftAssocInversePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldLeftAssocMultiplicity a b c d e)
      (Fus.FourfoldLeftInnerMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun g => Fus.inversePrintedFMatrix a b c g ⊗ₖ
    (1 : Matrix (Fin (Fus.fusionMultiplicity g d e))
      (Fin (Fus.fusionMultiplicity g d e)) ℂ)).submatrix
        (Fus.leftPathFirstSourceEquiv a b c d e)
        (Fus.leftPathFirstTargetEquiv a b c d e)

/-- The inverse-orientation `F^{ahd}_e` edge from the middle tree to the
left-inner tree.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
noncomputable def middleToLeftInnerInversePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldLeftInnerMultiplicity a b c d e)
      (Fus.FourfoldMiddleMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun h =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity b c h))
      (Fin (Fus.fusionMultiplicity b c h)) ℂ) ⊗ₖ
        Fus.inversePrintedFMatrix a h d e).submatrix
          (Fus.leftPathSecondSourceEquiv a b c d e)
          (Fus.leftPathSecondTargetEquiv a b c d e)

/-- The inverse-orientation `F^{bcd}_i` edge from the right-associated tree
to the middle tree.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
noncomputable def rightAssocToMiddleInversePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldMiddleMultiplicity a b c d e)
      (Fus.FourfoldRightAssocMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun i => Fus.inversePrintedFMatrix b c d i ⊗ₖ
    (1 : Matrix (Fin (Fus.fusionMultiplicity a i e))
      (Fin (Fus.fusionMultiplicity a i e)) ℂ)).submatrix
        (Fus.leftPathThirdSourceEquiv a b c d e)
        (Fus.leftPathThirdTargetEquiv a b c d e)

/-- The inverse-orientation `F^{fcd}_e` edge from the pair tree to the
left-associated tree.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
noncomputable def pairToLeftAssocInversePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldLeftAssocMultiplicity a b c d e)
      (Fus.FourfoldPairMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun f =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity a b f))
      (Fin (Fus.fusionMultiplicity a b f)) ℂ) ⊗ₖ
        Fus.inversePrintedFMatrix f c d e).submatrix
          (Fus.rightPathFirstSourceEquiv a b c d e)
          (Fus.rightPathFirstTargetEquiv a b c d e)

/-- The inverse-orientation `F^{abj}_e` edge from the right-associated tree
to the pair tree.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
noncomputable def rightAssocToPairInversePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldPairMultiplicity a b c d e)
      (Fus.FourfoldRightAssocMultiplicity a b c d e) ℂ :=
  (Matrix.blockDiagonal' fun j => Fus.inversePrintedFMatrix a b j e ⊗ₖ
    (1 : Matrix (Fin (Fus.fusionMultiplicity c d j))
      (Fin (Fus.fusionMultiplicity c d j)) ℂ)).submatrix
        (Fus.rightPathSecondSourceEquiv a b c d e)
        (Fus.rightPathSecondTargetEquiv a b c d e)

/-- The three-edge printed-`F` composite from the fully left- to the fully right-associated tree.

Source: arXiv:1511.08090, equation `pentagoneq`, left-hand side, lines 280--281; its
orientation follows equation `Fmove`, lines 248--251. -/
noncomputable def threeEdgePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e)
      (Fus.FourfoldLeftAssocMultiplicity a b c d e) ℂ :=
  (Fus.middleToRightAssocPrintedFMatrix a b c d e *
    Fus.leftInnerToMiddlePrintedFMatrix a b c d e) *
      Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e

/-- The two-edge printed-`F` composite from the fully left- to the fully right-associated tree.

Source: arXiv:1511.08090, equation `pentagoneq`, right-hand side, lines 282--283; its
orientation follows equation `Fmove`, lines 248--251. -/
noncomputable def twoEdgePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e)
      (Fus.FourfoldLeftAssocMultiplicity a b c d e) ℂ :=
  Fus.pairToRightAssocPrintedFMatrix a b c d e *
    Fus.leftAssocToPairPrintedFMatrix a b c d e

/-- The inverse-orientation composite along the three-edge path, from the
fully right- to the fully left-associated tree.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
noncomputable def threeEdgeInversePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldLeftAssocMultiplicity a b c d e)
      (Fus.FourfoldRightAssocMultiplicity a b c d e) ℂ :=
  Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e *
    (Fus.middleToLeftInnerInversePrintedFMatrix a b c d e *
      Fus.rightAssocToMiddleInversePrintedFMatrix a b c d e)

/-- The inverse-orientation composite along the two-edge path, from the
fully right- to the fully left-associated tree.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
noncomputable def twoEdgeInversePrintedFMatrix (a b c d e : Λ) :
    Matrix (Fus.FourfoldLeftAssocMultiplicity a b c d e)
      (Fus.FourfoldRightAssocMultiplicity a b c d e) ℂ :=
  Fus.pairToLeftAssocInversePrintedFMatrix a b c d e *
    Fus.rightAssocToPairInversePrintedFMatrix a b c d e

private theorem rectangular_inverse_unique {l m : Type*}
    [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
    (A C : Matrix l m ℂ) (B : Matrix m l ℂ) (hAB : A * B = 1) (hBC : B * C = 1) :
    A = C := by
  calc
    A = A * 1 := (Matrix.mul_one A).symm
    _ = A * (B * C) := congrArg (A * ·) hBC.symm
    _ = (A * B) * C := (Matrix.mul_assoc A B C).symm
    _ = 1 * C := congrArg (· * C) hAB
    _ = C := Matrix.one_mul C

private theorem rightAssocToMiddleInverse_mul_middleToRightAssoc
    (a b c d e : Λ) :
    Fus.rightAssocToMiddleInversePrintedFMatrix a b c d e *
      Fus.middleToRightAssocPrintedFMatrix a b c d e = 1 := by
  unfold rightAssocToMiddleInversePrintedFMatrix
    middleToRightAssocPrintedFMatrix
  rw [Matrix.submatrix_mul_equiv _ _ _
      (Fus.leftPathThirdTargetEquiv a b c d e) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul,
    Fus.inversePrintedFMatrix_mul_printedFMatrix, Matrix.one_mul,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (i : Λ) → Matrix
      (Fus.LeftTripleMultiplicity b c d i ×
        Fin (Fus.fusionMultiplicity a i e))
      (Fus.LeftTripleMultiplicity b c d i ×
        Fin (Fus.fusionMultiplicity a i e)) ℂ)).submatrix
          (Fus.leftPathThirdSourceEquiv a b c d e)
          (Fus.leftPathThirdSourceEquiv a b c d e) = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

private theorem middleToLeftInnerInverse_mul_leftInnerToMiddle
    (a b c d e : Λ) :
    Fus.middleToLeftInnerInversePrintedFMatrix a b c d e *
      Fus.leftInnerToMiddlePrintedFMatrix a b c d e = 1 := by
  unfold middleToLeftInnerInversePrintedFMatrix
    leftInnerToMiddlePrintedFMatrix
  rw [Matrix.submatrix_mul_equiv _ _ _
      (Fus.leftPathSecondTargetEquiv a b c d e) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Fus.inversePrintedFMatrix_mul_printedFMatrix,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (h : Λ) → Matrix
      (Fin (Fus.fusionMultiplicity b c h) ×
        Fus.LeftTripleMultiplicity a h d e)
      (Fin (Fus.fusionMultiplicity b c h) ×
        Fus.LeftTripleMultiplicity a h d e) ℂ)).submatrix
          (Fus.leftPathSecondSourceEquiv a b c d e)
          (Fus.leftPathSecondSourceEquiv a b c d e) = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

private theorem leftInnerToLeftAssocInverse_mul_leftAssocToLeftInner
    (a b c d e : Λ) :
    Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e *
      Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e = 1 := by
  unfold leftInnerToLeftAssocInversePrintedFMatrix
    leftAssocToLeftInnerPrintedFMatrix
  rw [Matrix.submatrix_mul_equiv _ _ _
      (Fus.leftPathFirstTargetEquiv a b c d e) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul,
    Fus.inversePrintedFMatrix_mul_printedFMatrix, Matrix.one_mul,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (g : Λ) → Matrix
      (Fus.LeftTripleMultiplicity a b c g ×
        Fin (Fus.fusionMultiplicity g d e))
      (Fus.LeftTripleMultiplicity a b c g ×
        Fin (Fus.fusionMultiplicity g d e)) ℂ)).submatrix
          (Fus.leftPathFirstSourceEquiv a b c d e)
          (Fus.leftPathFirstSourceEquiv a b c d e) = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

private theorem leftAssocToPair_mul_pairToLeftAssocInverse
    (a b c d e : Λ) :
    Fus.leftAssocToPairPrintedFMatrix a b c d e *
      Fus.pairToLeftAssocInversePrintedFMatrix a b c d e = 1 := by
  unfold leftAssocToPairPrintedFMatrix
    pairToLeftAssocInversePrintedFMatrix
  rw [Matrix.submatrix_mul_equiv _ _ _
      (Fus.rightPathFirstSourceEquiv a b c d e) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Fus.printedFMatrix_mul_inversePrintedFMatrix,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (f : Λ) → Matrix
      (Fin (Fus.fusionMultiplicity a b f) ×
        Fus.RightTripleMultiplicity f c d e)
      (Fin (Fus.fusionMultiplicity a b f) ×
        Fus.RightTripleMultiplicity f c d e) ℂ)).submatrix
          (Fus.rightPathFirstTargetEquiv a b c d e)
          (Fus.rightPathFirstTargetEquiv a b c d e) = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

private theorem pairToRightAssoc_mul_rightAssocToPairInverse
    (a b c d e : Λ) :
    Fus.pairToRightAssocPrintedFMatrix a b c d e *
      Fus.rightAssocToPairInversePrintedFMatrix a b c d e = 1 := by
  unfold pairToRightAssocPrintedFMatrix
    rightAssocToPairInversePrintedFMatrix
  rw [Matrix.submatrix_mul_equiv _ _ _
      (Fus.rightPathSecondSourceEquiv a b c d e) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul,
    Fus.printedFMatrix_mul_inversePrintedFMatrix, Matrix.one_mul,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (j : Λ) → Matrix
      (Fus.RightTripleMultiplicity a b j e ×
        Fin (Fus.fusionMultiplicity c d j))
      (Fus.RightTripleMultiplicity a b j e ×
        Fin (Fus.fusionMultiplicity c d j)) ℂ)).submatrix
          (Fus.rightPathSecondTargetEquiv a b c d e)
          (Fus.rightPathSecondTargetEquiv a b c d e) = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

/-! ### Fourfold F-move identities -/

/-- The first edge of the three-edge path is the printed F-move on the first
three tensor factors, with the last fusion multiplicity and final bond
coordinate unchanged.

Source: arXiv:1511.08090, equations `Fmove` and `pentagoneq`, lines 248--251
and 279--283. -/
theorem leftInnerFourfoldSynthesis_mul_leftAssocToLeftInnerPrintedFMatrix
    (a b c d e : Λ) :
    Fus.leftInnerFourfoldSynthesis a b c d e *
        (Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ)) =
      Fus.leftAssocFourfoldSynthesis a b c d e := by
  classical
  funext x y
  rcases x with ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩
  rcases y with ⟨⟨f, g, mu, nu, rho⟩, z⟩
  simp only [leftAssocToLeftInnerPrintedFMatrix,
    leftPathFirstTargetEquiv, Equiv.coe_fn_mk, leftPathFirstSourceEquiv,
    Matrix.mul_apply, leftInnerFourfoldSynthesis, kroneckerMap_apply,
    submatrix_apply, blockDiagonal'_apply, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, mul_dite, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_dite_eq',
    cast_eq, leftAssocFourfoldSynthesis]
  have hF (yg : Fin (Fus.bondDim g)) := congrArg
    (fun M => M ⟨⟨xa, xb⟩, xc⟩ ⟨⟨f, mu, nu⟩, yg⟩)
      (Fus.rightTripleSynthesis_mul_printedFMatrix a b c g)
  simp only [Matrix.mul_apply, rightTripleSynthesis, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    leftTripleSynthesis] at hF
  have hSum := congrArg
    (fun q => ∑ yg, q yg * Fus.fusionTensor g d e rho (yg, xd) z)
    (funext hF)
  convert hSum using 1
  · simp_rw [Finset.sum_mul]
    conv_rhs =>
      rw [Finset.sum_comm]
      enter [2, h]
      rw [Finset.sum_comm]
      enter [2, sigma]
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro sigma _
    apply Finset.sum_congr rfl
    intro lambda _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro yh _
    apply Finset.sum_congr rfl
    intro yg _
    ring
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]

/-- The second edge of the three-edge path is the printed F-move on the
subtree with incoming labels `a`, `h`, and `d`.

Source: arXiv:1511.08090, equations `Fmove` and `pentagoneq`, lines 248--251
and 279--283. -/
theorem middleFourfoldSynthesis_mul_leftInnerToMiddlePrintedFMatrix
    (a b c d e : Λ) :
    Fus.middleFourfoldSynthesis a b c d e *
        (Fus.leftInnerToMiddlePrintedFMatrix a b c d e ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ)) =
      Fus.leftInnerFourfoldSynthesis a b c d e := by
  classical
  funext x y
  rcases x with ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩
  rcases y with ⟨⟨h, g, sigma, lambda, rho⟩, z⟩
  simp only [leftInnerToMiddlePrintedFMatrix,
    leftPathSecondTargetEquiv, Prod.mk.eta, Equiv.coe_fn_mk,
    leftPathSecondSourceEquiv, Matrix.mul_apply, middleFourfoldSynthesis,
    kroneckerMap_apply, submatrix_apply, blockDiagonal'_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, mul_dite, Fintype.sum_prod_type, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_dite_eq',
    cast_eq, Finset.sum_ite_irrel, leftInnerFourfoldSynthesis]
  have hF (yh : Fin (Fus.bondDim h)) := congrArg
    (fun M => M ⟨⟨xa, yh⟩, xd⟩ ⟨⟨g, lambda, rho⟩, z⟩)
      (Fus.rightTripleSynthesis_mul_printedFMatrix a h d e)
  simp only [Matrix.mul_apply, rightTripleSynthesis, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    leftTripleSynthesis] at hF
  have hSum := congrArg
    (fun q => ∑ yh, Fus.fusionTensor b c h sigma (xb, xc) yh * q yh)
    (funext hF)
  convert hSum using 1
  · simp_rw [Finset.mul_sum]
    conv_rhs =>
      rw [Finset.sum_comm]
      enter [2, i]
      rw [Finset.sum_comm]
      enter [2, omega]
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro omega _
    apply Finset.sum_congr rfl
    intro kappa _
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro yh _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro yi _
    ring
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro yh _
    apply Finset.sum_congr rfl
    intro yg _
    ring

/-- The third edge of the three-edge path is the printed F-move on the
subtree with incoming labels `b`, `c`, and `d`.

Source: arXiv:1511.08090, equations `Fmove` and `pentagoneq`, lines 248--251
and 279--283. -/
theorem rightAssocFourfoldSynthesis_mul_middleToRightAssocPrintedFMatrix
    (a b c d e : Λ) :
    Fus.rightAssocFourfoldSynthesis a b c d e *
        (Fus.middleToRightAssocPrintedFMatrix a b c d e ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ)) =
      Fus.middleFourfoldSynthesis a b c d e := by
  classical
  funext x y
  rcases x with ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩
  rcases y with ⟨⟨h, i, sigma, omega, kappa⟩, z⟩
  simp only [middleToRightAssocPrintedFMatrix,
    leftPathThirdTargetEquiv, Equiv.coe_fn_mk, leftPathThirdSourceEquiv,
    Matrix.mul_apply, rightAssocFourfoldSynthesis, kroneckerMap_apply,
    submatrix_apply, blockDiagonal'_apply, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, mul_dite, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_dite_eq',
    cast_eq, middleFourfoldSynthesis]
  have hF (yi : Fin (Fus.bondDim i)) := congrArg
    (fun M => M ⟨⟨xb, xc⟩, xd⟩ ⟨⟨h, sigma, omega⟩, yi⟩)
      (Fus.rightTripleSynthesis_mul_printedFMatrix b c d i)
  simp only [Matrix.mul_apply, rightTripleSynthesis, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    leftTripleSynthesis] at hF
  have hSum := congrArg
    (fun q => ∑ yi, q yi * Fus.fusionTensor a i e kappa (xa, yi) z)
    (funext hF)
  convert hSum using 1
  · simp_rw [Finset.sum_mul]
    conv_rhs =>
      rw [Finset.sum_comm]
      enter [2, j]
      rw [Finset.sum_comm]
      enter [2, gamma]
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro gamma _
    apply Finset.sum_congr rfl
    intro delta _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro yj _
    apply Finset.sum_congr rfl
    intro yi _
    ring
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]

/-- The first edge of the two-edge path is the printed F-move on the
subtree with incoming labels `f`, `c`, and `d`.

Source: arXiv:1511.08090, equations `Fmove` and `pentagoneq`, lines 248--251
and 279--283. -/
theorem pairFourfoldSynthesis_mul_leftAssocToPairPrintedFMatrix
    (a b c d e : Λ) :
    Fus.pairFourfoldSynthesis a b c d e *
        (Fus.leftAssocToPairPrintedFMatrix a b c d e ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ)) =
      Fus.leftAssocFourfoldSynthesis a b c d e := by
  classical
  funext x y
  rcases x with ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩
  rcases y with ⟨⟨f, g, mu, nu, rho⟩, z⟩
  simp only [leftAssocToPairPrintedFMatrix,
    rightPathFirstTargetEquiv, Prod.mk.eta, Equiv.coe_fn_mk,
    rightPathFirstSourceEquiv, Matrix.mul_apply, pairFourfoldSynthesis,
    kroneckerMap_apply, submatrix_apply, blockDiagonal'_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, mul_dite, Fintype.sum_prod_type, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_dite_eq',
    cast_eq, Finset.sum_ite_irrel, leftAssocFourfoldSynthesis]
  have hF (yf : Fin (Fus.bondDim f)) := congrArg
    (fun M => M ⟨⟨yf, xc⟩, xd⟩ ⟨⟨g, nu, rho⟩, z⟩)
      (Fus.rightTripleSynthesis_mul_printedFMatrix f c d e)
  simp only [Matrix.mul_apply, rightTripleSynthesis, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    leftTripleSynthesis] at hF
  have hSum := congrArg
    (fun q => ∑ yf, Fus.fusionTensor a b f mu (xa, xb) yf * q yf)
    (funext hF)
  convert hSum using 1
  · simp_rw [Finset.mul_sum]
    conv_rhs =>
      rw [Finset.sum_comm]
      enter [2, j]
      rw [Finset.sum_comm]
      enter [2, gamma]
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro gamma _
    apply Finset.sum_congr rfl
    intro tau _
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro yf _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro yj _
    ring
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro yf _
    apply Finset.sum_congr rfl
    intro yg _
    ring

/-- The second edge of the two-edge path is the printed F-move on the
subtree with incoming labels `a`, `b`, and `j`.

Source: arXiv:1511.08090, equations `Fmove` and `pentagoneq`, lines 248--251
and 279--283. -/
theorem rightAssocFourfoldSynthesis_mul_pairToRightAssocPrintedFMatrix
    (a b c d e : Λ) :
    Fus.rightAssocFourfoldSynthesis a b c d e *
        (Fus.pairToRightAssocPrintedFMatrix a b c d e ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ)) =
      Fus.pairFourfoldSynthesis a b c d e := by
  classical
  funext x y
  rcases x with ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩
  rcases y with ⟨⟨f, j, mu, gamma, tau⟩, z⟩
  simp only [pairToRightAssocPrintedFMatrix,
    rightPathSecondTargetEquiv, Prod.mk.eta, Equiv.coe_fn_mk,
    rightPathSecondSourceEquiv, Matrix.mul_apply,
    rightAssocFourfoldSynthesis, kroneckerMap_apply, submatrix_apply,
    blockDiagonal'_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    mul_dite, Fintype.sum_prod_type, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_dite_eq',
    cast_eq, Finset.sum_ite_irrel, pairFourfoldSynthesis]
  have hF (yj : Fin (Fus.bondDim j)) := congrArg
    (fun M => M ⟨⟨xa, xb⟩, yj⟩ ⟨⟨f, mu, tau⟩, z⟩)
      (Fus.rightTripleSynthesis_mul_printedFMatrix a b j e)
  simp only [Matrix.mul_apply, rightTripleSynthesis, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    leftTripleSynthesis] at hF
  have hSum := congrArg
    (fun q => ∑ yj, Fus.fusionTensor c d j gamma (xc, xd) yj * q yj)
    (funext hF)
  convert hSum using 1
  · simp_rw [Finset.mul_sum]
    conv_rhs =>
      rw [Finset.sum_comm]
      enter [2, i]
      rw [Finset.sum_comm]
      enter [2, delta]
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro delta _
    apply Finset.sum_congr rfl
    intro kappa _
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro yj _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro yi _
    ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro yj _
    apply Finset.sum_congr rfl
    intro yf _
    ring

/-- The three-edge path carries the fully left-associated synthesis to the
fully right-associated synthesis.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
theorem rightAssocFourfoldSynthesis_mul_threeEdgePrintedFMatrix
    (a b c d e : Λ) :
    Fus.rightAssocFourfoldSynthesis a b c d e *
        (Fus.threeEdgePrintedFMatrix a b c d e ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ)) =
      Fus.leftAssocFourfoldSynthesis a b c d e := by
  rw [threeEdgePrintedFMatrix, mul_kronecker_one, mul_kronecker_one,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Fus.rightAssocFourfoldSynthesis_mul_middleToRightAssocPrintedFMatrix,
    Fus.middleFourfoldSynthesis_mul_leftInnerToMiddlePrintedFMatrix]
  exact Fus.leftInnerFourfoldSynthesis_mul_leftAssocToLeftInnerPrintedFMatrix
    a b c d e

/-- The two-edge path carries the fully left-associated synthesis to the
fully right-associated synthesis.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
theorem rightAssocFourfoldSynthesis_mul_twoEdgePrintedFMatrix
    (a b c d e : Λ) :
    Fus.rightAssocFourfoldSynthesis a b c d e *
        (Fus.twoEdgePrintedFMatrix a b c d e ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ)) =
      Fus.leftAssocFourfoldSynthesis a b c d e := by
  rw [twoEdgePrintedFMatrix, mul_kronecker_one, ← Matrix.mul_assoc,
    Fus.rightAssocFourfoldSynthesis_mul_pairToRightAssocPrintedFMatrix]
  exact Fus.pairFourfoldSynthesis_mul_leftAssocToPairPrintedFMatrix
    a b c d e

/-- The two forward printed-`F` composites around the fourfold associahedron
are equal.

The proof compares their expansions into the terminal right-associated
fourfold fusion map and cancels with its explicit analysis map.  Thus the
pentagon follows from fusion-tensor biorthogonality and the elementary
three-block `F`-move, rather than from an assumed categorical pentagon.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283, in the
forward orientation fixed by equation `Fmove`, lines 248--251. -/
theorem threeEdgePrintedFMatrix_eq_twoEdgePrintedFMatrix
    (a b c d e : Λ) :
    Fus.threeEdgePrintedFMatrix a b c d e =
      Fus.twoEdgePrintedFMatrix a b c d e := by
  let I : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ := 1
  have hLift :
      Fus.threeEdgePrintedFMatrix a b c d e ⊗ₖ I =
        Fus.twoEdgePrintedFMatrix a b c d e ⊗ₖ I := by
    calc
      Fus.threeEdgePrintedFMatrix a b c d e ⊗ₖ I =
          (Fus.rightAssocFourfoldAnalysis a b c d e *
              Fus.rightAssocFourfoldSynthesis a b c d e) *
            (Fus.threeEdgePrintedFMatrix a b c d e ⊗ₖ I) := by
              rw [Fus.rightAssocFourfoldAnalysis_mul_synthesis, Matrix.one_mul]
      _ = Fus.rightAssocFourfoldAnalysis a b c d e *
            (Fus.rightAssocFourfoldSynthesis a b c d e *
              (Fus.threeEdgePrintedFMatrix a b c d e ⊗ₖ I)) := by
                rw [Matrix.mul_assoc]
      _ = Fus.rightAssocFourfoldAnalysis a b c d e *
            Fus.leftAssocFourfoldSynthesis a b c d e := by
              rw [Fus.rightAssocFourfoldSynthesis_mul_threeEdgePrintedFMatrix]
      _ = Fus.rightAssocFourfoldAnalysis a b c d e *
            (Fus.rightAssocFourfoldSynthesis a b c d e *
              (Fus.twoEdgePrintedFMatrix a b c d e ⊗ₖ I)) := by
                rw [Fus.rightAssocFourfoldSynthesis_mul_twoEdgePrintedFMatrix]
      _ = (Fus.rightAssocFourfoldAnalysis a b c d e *
              Fus.rightAssocFourfoldSynthesis a b c d e) *
            (Fus.twoEdgePrintedFMatrix a b c d e ⊗ₖ I) := by
              rw [Matrix.mul_assoc]
      _ = Fus.twoEdgePrintedFMatrix a b c d e ⊗ₖ I := by
            rw [Fus.rightAssocFourfoldAnalysis_mul_synthesis, Matrix.one_mul]
  apply Matrix.kronecker_one_injective (Fus.bondDim_pos e)
  simpa only [I] using hLift

/-- The inverse-orientation composites around the fourfold associahedron
are equal.  This is the matrix orientation printed in equation
`pentagoneq` of the source.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
theorem threeEdgeInversePrintedFMatrix_eq_twoEdgeInversePrintedFMatrix
    (a b c d e : Λ) :
    Fus.threeEdgeInversePrintedFMatrix a b c d e =
      Fus.twoEdgeInversePrintedFMatrix a b c d e := by
  have hThreeLeft :
      Fus.threeEdgeInversePrintedFMatrix a b c d e *
        Fus.threeEdgePrintedFMatrix a b c d e = 1 := by
    calc
      Fus.threeEdgeInversePrintedFMatrix a b c d e *
          Fus.threeEdgePrintedFMatrix a b c d e =
        Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e *
          (Fus.middleToLeftInnerInversePrintedFMatrix a b c d e *
            ((Fus.rightAssocToMiddleInversePrintedFMatrix a b c d e *
                Fus.middleToRightAssocPrintedFMatrix a b c d e) *
              Fus.leftInnerToMiddlePrintedFMatrix a b c d e) *
            Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e) := by
              simp only [threeEdgeInversePrintedFMatrix,
                threeEdgePrintedFMatrix, Matrix.mul_assoc]
      _ = Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e *
          (Fus.middleToLeftInnerInversePrintedFMatrix a b c d e *
            Fus.leftInnerToMiddlePrintedFMatrix a b c d e) *
          Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e := by
            rw [Fus.rightAssocToMiddleInverse_mul_middleToRightAssoc,
              Matrix.one_mul]
            simp only [Matrix.mul_assoc]
      _ = Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e *
          Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e := by
            rw [Fus.middleToLeftInnerInverse_mul_leftInnerToMiddle,
              Matrix.mul_one]
      _ = 1 := Fus.leftInnerToLeftAssocInverse_mul_leftAssocToLeftInner
        a b c d e
  have hTwoRight :
      Fus.twoEdgePrintedFMatrix a b c d e *
        Fus.twoEdgeInversePrintedFMatrix a b c d e = 1 := by
    calc
      Fus.twoEdgePrintedFMatrix a b c d e *
          Fus.twoEdgeInversePrintedFMatrix a b c d e =
        Fus.pairToRightAssocPrintedFMatrix a b c d e *
          ((Fus.leftAssocToPairPrintedFMatrix a b c d e *
              Fus.pairToLeftAssocInversePrintedFMatrix a b c d e) *
            Fus.rightAssocToPairInversePrintedFMatrix a b c d e) := by
              simp only [twoEdgePrintedFMatrix,
                twoEdgeInversePrintedFMatrix, Matrix.mul_assoc]
      _ = Fus.pairToRightAssocPrintedFMatrix a b c d e *
          Fus.rightAssocToPairInversePrintedFMatrix a b c d e := by
            rw [Fus.leftAssocToPair_mul_pairToLeftAssocInverse,
              Matrix.one_mul]
      _ = 1 := Fus.pairToRightAssoc_mul_rightAssocToPairInverse
        a b c d e
  have hThreeRight :
      Fus.threeEdgePrintedFMatrix a b c d e *
        Fus.twoEdgeInversePrintedFMatrix a b c d e = 1 := by
    rw [Fus.threeEdgePrintedFMatrix_eq_twoEdgePrintedFMatrix]
    exact hTwoRight
  exact rectangular_inverse_unique _ _ _ hThreeLeft hThreeRight

/-- The literal indexed pentagon equation for the inverse-orientation
`F`-matrix entries.

The upper and lower multiplicity indices follow equation `pentagoneq` of
the source.  They are opposite to the forward matrix orientation fixed by
equation `Fmove`.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
theorem inversePrintedFMatrix_pentagon
    (a b c d e f g j i : Λ)
    (mu : Fin (Fus.fusionMultiplicity a b f))
    (nu : Fin (Fus.fusionMultiplicity f c g))
    (rho : Fin (Fus.fusionMultiplicity g d e))
    (gamma : Fin (Fus.fusionMultiplicity c d j))
    (delta : Fin (Fus.fusionMultiplicity b j i))
    (kappa : Fin (Fus.fusionMultiplicity a i e)) :
    (∑ h : Λ, ∑ sigma : Fin (Fus.fusionMultiplicity b c h),
      ∑ lambda : Fin (Fus.fusionMultiplicity a h g),
      ∑ omega : Fin (Fus.fusionMultiplicity h d i),
        Fus.inversePrintedFMatrix a b c g ⟨f, mu, nu⟩
            ⟨h, sigma, lambda⟩ *
          Fus.inversePrintedFMatrix a h d e ⟨g, lambda, rho⟩
            ⟨i, omega, kappa⟩ *
          Fus.inversePrintedFMatrix b c d i ⟨h, sigma, omega⟩
            ⟨j, gamma, delta⟩) =
      ∑ tau : Fin (Fus.fusionMultiplicity f j e),
        Fus.inversePrintedFMatrix f c d e ⟨g, nu, rho⟩
            ⟨j, gamma, tau⟩ *
          Fus.inversePrintedFMatrix a b j e ⟨f, mu, tau⟩
            ⟨i, delta, kappa⟩ := by
  have h := congrArg
    (fun M => M ⟨f, g, mu, nu, rho⟩ ⟨j, i, gamma, delta, kappa⟩)
    (Fus.threeEdgeInversePrintedFMatrix_eq_twoEdgeInversePrintedFMatrix
      a b c d e)
  simpa only [mul_assoc, threeEdgeInversePrintedFMatrix,
    leftInnerToLeftAssocInversePrintedFMatrix, leftPathFirstSourceEquiv,
    Equiv.coe_fn_mk, leftPathFirstTargetEquiv,
    middleToLeftInnerInversePrintedFMatrix, leftPathSecondSourceEquiv,
    Prod.mk.eta, leftPathSecondTargetEquiv,
    rightAssocToMiddleInversePrintedFMatrix, leftPathThirdSourceEquiv,
    leftPathThirdTargetEquiv, Matrix.mul_apply, submatrix_apply,
    blockDiagonal'_apply, kroneckerMap_apply, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, ite_mul, one_mul, zero_mul, mul_dite, dite_mul,
    Fintype.sum_sigma, Finset.sum_dite_irrel, Fintype.sum_prod_type,
    Finset.sum_const_zero, Finset.sum_dite_eq', Finset.mem_univ,
    ↓reduceIte, cast_eq, Finset.sum_ite_eq', Finset.sum_dite_eq,
    Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mul_sum,
    twoEdgeInversePrintedFMatrix, pairToLeftAssocInversePrintedFMatrix,
    rightPathFirstSourceEquiv, rightPathFirstTargetEquiv,
    rightAssocToPairInversePrintedFMatrix, rightPathSecondSourceEquiv,
    rightPathSecondTargetEquiv] using h

end MPOTensor.CompleteZipperFusionFamily
