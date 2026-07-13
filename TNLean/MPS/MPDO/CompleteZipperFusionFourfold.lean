/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionInverse

/-!
# Fourfold fusion trees for complete zipper data

The five parenthesizations of four MPO blocks give five multiplicity spaces at a fixed final
label.  Their coordinates are the fusion labels and multiplicity indices printed in the pentagon
equation of arXiv:1511.08090.  This file also defines the corresponding fourfold fusion maps and
the five lifted, printed-orientation `F`-matrices along the associahedron.

These are categorical fusion multiplicities from `CompleteZipperFusionFamily`; they are not the
positive-diagonal weighted coordinates of `BNTFusionIsometryFamily`.

**Local fix (equation `pentagoneq`):** The source prints the entries in equation
`pentagoneq` with the opposite upper/lower placement from equation `Fmove`.  The forward edge
matrices below follow `Fmove`: rows are right-tree coordinates and columns are left-tree
coordinates.  The literal index placement in `pentagoneq` therefore belongs to the inverse edge
matrices.  This correction is documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

No pentagon equality is asserted in this file.  Its proof must identify the two composites with
the same fourfold fusion map and cancel a fusion analysis map.

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

/-! ### The five multiplicity spaces -/

/-- The bond space of four MPO blocks, associated to the leftmost parenthesization. -/
abbrev FourfoldBond (a b c d : Λ) : Type :=
  ((Fin (Fus.bondDim a) × Fin (Fus.bondDim b)) × Fin (Fus.bondDim c)) ×
    Fin (Fus.bondDim d)

/-- Multiplicity coordinates `(f, g, mu, nu, rho)` for `(((a b) c) d) -> e`.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
abbrev FourfoldLeftAssocMultiplicity (a b c d e : Λ) : Type u :=
  (f : Λ) × (g : Λ) × Fin (Fus.fusionMultiplicity a b f) ×
    Fin (Fus.fusionMultiplicity f c g) × Fin (Fus.fusionMultiplicity g d e)

/-- Multiplicity coordinates `(h, g, sigma, lambda, rho)` for `((a (b c)) d) -> e`.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
abbrev FourfoldLeftInnerMultiplicity (a b c d e : Λ) : Type u :=
  (h : Λ) × (g : Λ) × Fin (Fus.fusionMultiplicity b c h) ×
    Fin (Fus.fusionMultiplicity a h g) × Fin (Fus.fusionMultiplicity g d e)

/-- Multiplicity coordinates `(h, i, sigma, omega, kappa)` for `a ((b c) d) -> e`.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
abbrev FourfoldMiddleMultiplicity (a b c d e : Λ) : Type u :=
  (h : Λ) × (i : Λ) × Fin (Fus.fusionMultiplicity b c h) ×
    Fin (Fus.fusionMultiplicity h d i) × Fin (Fus.fusionMultiplicity a i e)

/-- Multiplicity coordinates `(f, j, mu, gamma, tau)` for `(a b) (c d) -> e`.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
abbrev FourfoldPairMultiplicity (a b c d e : Λ) : Type u :=
  (f : Λ) × (j : Λ) × Fin (Fus.fusionMultiplicity a b f) ×
    Fin (Fus.fusionMultiplicity c d j) × Fin (Fus.fusionMultiplicity f j e)

/-- Multiplicity coordinates `(j, i, gamma, delta, kappa)` for `a (b (c d)) -> e`.

Source: arXiv:1511.08090, equation `pentagoneq`, lines 279--283. -/
abbrev FourfoldRightAssocMultiplicity (a b c d e : Λ) : Type u :=
  (j : Λ) × (i : Λ) × Fin (Fus.fusionMultiplicity c d j) ×
    Fin (Fus.fusionMultiplicity b j i) × Fin (Fus.fusionMultiplicity a i e)

/-! ### Fourfold fusion maps -/

/-- The fusion map for `(((a b) c) d) -> e`.

Its column `(f, g, mu, nu, rho, z)` is
`(((X^f_{ab,mu} tensor 1) X^g_{fc,nu}) tensor 1) X^e_{gd,rho}`.

Source: arXiv:1511.08090, line 279 and the leftmost tree in Figure `pentagon`. -/
noncomputable def leftAssocFourfoldSynthesis (a b c d e : Λ) :
    Matrix (Fus.FourfoldBond a b c d)
      (Fus.FourfoldLeftAssocMultiplicity a b c d e × Fin (Fus.bondDim e)) ℂ :=
  fun ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ ⟨⟨f, g, mu, nu, rho⟩, z⟩ =>
    ∑ yf : Fin (Fus.bondDim f), ∑ yg : Fin (Fus.bondDim g),
      Fus.fusionTensor a b f mu (xa, xb) yf *
        Fus.fusionTensor f c g nu (yf, xc) yg *
          Fus.fusionTensor g d e rho (yg, xd) z

/-- The fusion map for `((a (b c)) d) -> e`.

Source: arXiv:1511.08090, lines 279--283 and Figure `pentagon`. -/
noncomputable def leftInnerFourfoldSynthesis (a b c d e : Λ) :
    Matrix (Fus.FourfoldBond a b c d)
      (Fus.FourfoldLeftInnerMultiplicity a b c d e × Fin (Fus.bondDim e)) ℂ :=
  fun ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ ⟨⟨h, g, sigma, lambda, rho⟩, z⟩ =>
    ∑ yh : Fin (Fus.bondDim h), ∑ yg : Fin (Fus.bondDim g),
      Fus.fusionTensor b c h sigma (xb, xc) yh *
        Fus.fusionTensor a h g lambda (xa, yh) yg *
          Fus.fusionTensor g d e rho (yg, xd) z

/-- The fusion map for `a ((b c) d) -> e`.

Source: arXiv:1511.08090, lines 279--283 and Figure `pentagon`. -/
noncomputable def middleFourfoldSynthesis (a b c d e : Λ) :
    Matrix (Fus.FourfoldBond a b c d)
      (Fus.FourfoldMiddleMultiplicity a b c d e × Fin (Fus.bondDim e)) ℂ :=
  fun ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ ⟨⟨h, i, sigma, omega, kappa⟩, z⟩ =>
    ∑ yh : Fin (Fus.bondDim h), ∑ yi : Fin (Fus.bondDim i),
      Fus.fusionTensor b c h sigma (xb, xc) yh *
        Fus.fusionTensor h d i omega (yh, xd) yi *
          Fus.fusionTensor a i e kappa (xa, yi) z

/-- The fusion map for `(a b) (c d) -> e`.

Source: arXiv:1511.08090, lines 279--283 and Figure `pentagon`. -/
noncomputable def pairFourfoldSynthesis (a b c d e : Λ) :
    Matrix (Fus.FourfoldBond a b c d)
      (Fus.FourfoldPairMultiplicity a b c d e × Fin (Fus.bondDim e)) ℂ :=
  fun ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ ⟨⟨f, j, mu, gamma, tau⟩, z⟩ =>
    ∑ yf : Fin (Fus.bondDim f), ∑ yj : Fin (Fus.bondDim j),
      Fus.fusionTensor a b f mu (xa, xb) yf *
        Fus.fusionTensor c d j gamma (xc, xd) yj *
          Fus.fusionTensor f j e tau (yf, yj) z

/-- The fusion map for `a (b (c d)) -> e`.

Source: arXiv:1511.08090, line 279 and the rightmost tree in Figure `pentagon`. -/
noncomputable def rightAssocFourfoldSynthesis (a b c d e : Λ) :
    Matrix (Fus.FourfoldBond a b c d)
      (Fus.FourfoldRightAssocMultiplicity a b c d e × Fin (Fus.bondDim e)) ℂ :=
  fun ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ ⟨⟨j, i, gamma, delta, kappa⟩, z⟩ =>
    ∑ yj : Fin (Fus.bondDim j), ∑ yi : Fin (Fus.bondDim i),
      Fus.fusionTensor c d j gamma (xc, xd) yj *
        Fus.fusionTensor b j i delta (xb, yj) yi *
          Fus.fusionTensor a i e kappa (xa, yi) z

/-- The analysis map for the right-associated fourfold fusion tree.

Its product with `rightAssocFourfoldSynthesis` will cancel the final expansion in the proof of
the pentagon.

Source: arXiv:1511.08090, fusion left inverses at line 161 and lines 279--283. -/
noncomputable def rightAssocFourfoldAnalysis (a b c d e : Λ) :
    Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e × Fin (Fus.bondDim e))
      (Fus.FourfoldBond a b c d) ℂ :=
  fun ⟨⟨j, i, gamma, delta, kappa⟩, z⟩ ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ =>
    ∑ yi : Fin (Fus.bondDim i), ∑ yj : Fin (Fus.bondDim j),
      Fus.fusionTensorLeftInverse a i e kappa z (xa, yi) *
        Fus.fusionTensorLeftInverse b j i delta yi (xb, yj) *
          Fus.fusionTensorLeftInverse c d j gamma yj (xc, xd)

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

end MPOTensor.CompleteZipperFusionFamily
