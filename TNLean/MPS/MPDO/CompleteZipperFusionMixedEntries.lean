/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionMixedOrientation

/-!
# Indexed mixed pentagon for complete zipper fusion data

The mixed fourfold matrix identity has two forward comparisons followed by
one inverse comparison on its left-hand side. Evaluating its entries gives
the finite sums below, with every spectator multiplicity eliminated.

For an operator/operator/operator/state quadruple in the triangular fusion
family, the four forward coefficients become the actual action L matrices.
The remaining inverse coefficient has the analysis orientation of GLM23's
F symbol. The present theorem is stated for the constructed matrices of an
arbitrary complete zipper fusion family; no coherence equation is assumed.

**Local fix (multiplicity indices):** The inverse entry has the left-tree
pair `(mu, nu)` as its row and the right-tree pair `(sigma, lambda)` as its
column. This is the corrected placement in GLM23's coupled pentagon; see
`docs/paper-gaps/glm23_multiplicity_l_indices.tex`.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `coupledpent`,
  lines 554--562.
* arXiv:1511.08090, `Fmove` and `pentagoneq`, lines 248--299.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
  (Fus : CompleteZipperFusionFamily Λ p)

/-- The indexed mixed pentagon for the actual complete-zipper comparisons.

The summation on the left runs over the intermediate label `k` and its three
multiplicities. The sum on the right runs only over the multiplicity of
`f d -> i`. All sums are over their exact finite spaces, including empty
ones. Forward entries use right-tree rows and left-tree columns; the single
inverse entry uses the opposite orientation.

Source: GLM23, `coupledpent`, lines 554--562, with the multiplicity-index
correction recorded above. -/
theorem printedFMatrix_mixed_pentagon
    (a b c d e f g j i : Λ)
    (sigma : Fin (Fus.fusionMultiplicity b c f))
    (lambda : Fin (Fus.fusionMultiplicity a f g))
    (rho : Fin (Fus.fusionMultiplicity g d e))
    (gamma : Fin (Fus.fusionMultiplicity c d j))
    (delta : Fin (Fus.fusionMultiplicity b j i))
    (kappa : Fin (Fus.fusionMultiplicity a i e)) :
    (∑ k : Λ, ∑ tau : Fin (Fus.fusionMultiplicity k j e),
      ∑ mu : Fin (Fus.fusionMultiplicity a b k),
      ∑ nu : Fin (Fus.fusionMultiplicity k c g),
        Fus.printedFMatrix a b j e ⟨i, delta, kappa⟩ ⟨k, mu, tau⟩ *
          Fus.printedFMatrix k c d e ⟨j, gamma, tau⟩ ⟨g, nu, rho⟩ *
          Fus.inversePrintedFMatrix a b c g ⟨k, mu, nu⟩
            ⟨f, sigma, lambda⟩) =
      ∑ omega : Fin (Fus.fusionMultiplicity f d i),
        Fus.printedFMatrix b c d i ⟨j, gamma, delta⟩ ⟨f, sigma, omega⟩ *
          Fus.printedFMatrix a f d e ⟨i, omega, kappa⟩ ⟨g, lambda, rho⟩ := by
  classical
  -- These entry formulas are definitionally the five public lifted matrices.
  -- Spelling out their coordinates avoids naming the private path equivalences.
  let E : Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e)
      (Fus.FourfoldPairMultiplicity a b c d e) ℂ :=
    fun ⟨j', i', gamma', delta', kappa'⟩ ⟨k, j'', mu, gamma'', tau⟩ =>
      (Matrix.blockDiagonal' fun t => Fus.printedFMatrix a b t e ⊗ₖ
        (1 : Matrix (Fin (Fus.fusionMultiplicity c d t))
          (Fin (Fus.fusionMultiplicity c d t)) ℂ))
        ⟨j', ⟨i', delta', kappa'⟩, gamma'⟩ ⟨j'', ⟨k, mu, tau⟩, gamma''⟩
  let D : Matrix (Fus.FourfoldPairMultiplicity a b c d e)
      (Fus.FourfoldLeftAssocMultiplicity a b c d e) ℂ :=
    fun ⟨k, j', mu, gamma', tau⟩ ⟨k', g', mu', nu, rho'⟩ =>
      (Matrix.blockDiagonal' fun t =>
        (1 : Matrix (Fin (Fus.fusionMultiplicity a b t))
          (Fin (Fus.fusionMultiplicity a b t)) ℂ) ⊗ₖ Fus.printedFMatrix t c d e)
        ⟨k, mu, ⟨j', gamma', tau⟩⟩ ⟨k', mu', ⟨g', nu, rho'⟩⟩
  let Q : Matrix (Fus.FourfoldLeftAssocMultiplicity a b c d e)
      (Fus.FourfoldLeftInnerMultiplicity a b c d e) ℂ :=
    fun ⟨k, g', mu, nu, rho'⟩ ⟨f', g'', sigma', lambda', rho''⟩ =>
      (Matrix.blockDiagonal' fun t => Fus.inversePrintedFMatrix a b c t ⊗ₖ
        (1 : Matrix (Fin (Fus.fusionMultiplicity t d e))
          (Fin (Fus.fusionMultiplicity t d e)) ℂ))
        ⟨g', ⟨k, mu, nu⟩, rho'⟩ ⟨g'', ⟨f', sigma', lambda'⟩, rho''⟩
  let C : Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e)
      (Fus.FourfoldMiddleMultiplicity a b c d e) ℂ :=
    fun ⟨j', i', gamma', delta', kappa'⟩ ⟨f', i'', sigma', omega, kappa''⟩ =>
      (Matrix.blockDiagonal' fun t => Fus.printedFMatrix b c d t ⊗ₖ
        (1 : Matrix (Fin (Fus.fusionMultiplicity a t e))
          (Fin (Fus.fusionMultiplicity a t e)) ℂ))
        ⟨i', ⟨j', gamma', delta'⟩, kappa'⟩ ⟨i'', ⟨f', sigma', omega⟩, kappa''⟩
  let B : Matrix (Fus.FourfoldMiddleMultiplicity a b c d e)
      (Fus.FourfoldLeftInnerMultiplicity a b c d e) ℂ :=
    fun ⟨f', i', sigma', omega, kappa'⟩ ⟨f'', g', sigma'', lambda', rho'⟩ =>
      (Matrix.blockDiagonal' fun t =>
        (1 : Matrix (Fin (Fus.fusionMultiplicity b c t))
          (Fin (Fus.fusionMultiplicity b c t)) ℂ) ⊗ₖ Fus.printedFMatrix a t d e)
        ⟨f', sigma', ⟨i', omega, kappa'⟩⟩ ⟨f'', sigma'', ⟨g', lambda', rho'⟩⟩
  have h := congrArg
    (fun M => M ⟨j, i, gamma, delta, kappa⟩ ⟨f, g, sigma, lambda, rho⟩)
    (Fus.twoEdgePrintedFMatrix_mul_leftInnerToLeftAssocInverse a b c d e)
  change ((E * D) * Q) ⟨j, i, gamma, delta, kappa⟩
      ⟨f, g, sigma, lambda, rho⟩ =
    (C * B) ⟨j, i, gamma, delta, kappa⟩ ⟨f, g, sigma, lambda, rho⟩ at h
  rw [Matrix.mul_assoc] at h
  change
    (∑ y : Fus.FourfoldPairMultiplicity a b c d e,
      E ⟨j, i, gamma, delta, kappa⟩ y *
        ∑ x : Fus.FourfoldLeftAssocMultiplicity a b c d e,
          D y x * Q x ⟨f, g, sigma, lambda, rho⟩) =
      ∑ z : Fus.FourfoldMiddleMultiplicity a b c d e,
        C ⟨j, i, gamma, delta, kappa⟩ z *
          B z ⟨f, g, sigma, lambda, rho⟩ at h
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  simpa only [E, D, Q, C, B, blockDiagonal'_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, mul_dite, dite_mul,
    Fintype.sum_sigma, Finset.sum_dite_irrel, Fintype.sum_prod_type,
    Finset.sum_const_zero, Finset.sum_dite_eq', Finset.mem_univ,
    ↓reduceIte, cast_eq, Finset.sum_ite_eq', Finset.sum_dite_eq,
    Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mul_sum, mul_assoc] using h

end MPOTensor.CompleteZipperFusionFamily
