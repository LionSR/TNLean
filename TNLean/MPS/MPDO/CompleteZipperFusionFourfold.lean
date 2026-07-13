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
equation of arXiv:1511.08090.  This file defines the corresponding fourfold fusion maps and the
explicit analysis of the right-associated map.

These are categorical fusion multiplicities from `CompleteZipperFusionFamily`; they are not the
positive-diagonal weighted coordinates of `BNTFusionIsometryFamily`.

The lifted $F$-matrices, equality of the two paths, and literal indexed pentagon are given in
`CompleteZipperFusionPentagon`.

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

private noncomputable def fixedFinalSynthesis (a b e : Λ) :
    Matrix (Fin (Fus.bondDim a) × Fin (Fus.bondDim b))
      (Fin (Fus.fusionMultiplicity a b e) × Fin (Fus.bondDim e)) ℂ :=
  fun x y => Fus.fusionTensor a b e y.1 x y.2

private noncomputable def fixedFinalAnalysis (a b e : Λ) :
    Matrix (Fin (Fus.fusionMultiplicity a b e) × Fin (Fus.bondDim e))
      (Fin (Fus.bondDim a) × Fin (Fus.bondDim b)) ℂ :=
  fun x y => Fus.fusionTensorLeftInverse a b e x.1 x.2 y

private theorem fixedFinalAnalysis_mul_synthesis (a b e : Λ) :
    Fus.fixedFinalAnalysis a b e * Fus.fixedFinalSynthesis a b e = 1 := by
  funext ⟨mu, z⟩ ⟨nu, w⟩
  have h := congrArg
    (fun M => M ⟨e, mu, z⟩ ⟨e, nu, w⟩) (Fus.analysis_mul_synthesis a b)
  simpa [fixedFinalAnalysis, fixedFinalSynthesis, fusionTensorLeftInverse,
    fusionTensor, Matrix.mul_apply, Matrix.one_apply] using h

private abbrev RightFourfoldFirstStage (a b c d : Λ) : Type u :=
  Fin (Fus.bondDim a) × Fus.RightTripleIndex b c d

private def rightFourfoldBondEquiv (a b c d : Λ) :
    Fus.FourfoldBond a b c d ≃
      Fin (Fus.bondDim a) × Fus.TripleBond b c d where
  toFun
    | ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ => ⟨xa, ⟨⟨xb, xc⟩, xd⟩⟩
  invFun
    | ⟨xa, ⟨⟨xb, xc⟩, xd⟩⟩ => ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩
  left_inv := by rintro ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩; rfl
  right_inv := by rintro ⟨xa, ⟨⟨xb, xc⟩, xd⟩⟩; rfl

private def rightFourfoldFirstStageEquiv (a b c d : Λ) :
    Fus.RightFourfoldFirstStage a b c d ≃
      (i : Λ) × (Fus.RightTripleMultiplicity b c d i ×
        (Fin (Fus.bondDim a) × Fin (Fus.bondDim i))) where
  toFun
    | ⟨xa, ⟨i, m, yi⟩⟩ => ⟨i, m, xa, yi⟩
  invFun
    | ⟨i, m, xa, yi⟩ => ⟨xa, ⟨i, m, yi⟩⟩
  left_inv := by rintro ⟨xa, ⟨i, m, yi⟩⟩; rfl
  right_inv := by rintro ⟨i, m, xa, yi⟩; rfl

private abbrev RightFourfoldFinalNested (a b c d e : Λ) : Type u :=
  (i : Λ) × (Fus.RightTripleMultiplicity b c d i ×
    (Fin (Fus.fusionMultiplicity a i e) × Fin (Fus.bondDim e)))

private def rightFourfoldFinalEquiv (a b c d e : Λ) :
    Fus.FourfoldRightAssocMultiplicity a b c d e × Fin (Fus.bondDim e) ≃
      Fus.RightFourfoldFinalNested a b c d e where
  toFun
    | ⟨⟨j, i, gamma, delta, kappa⟩, z⟩ =>
        ⟨i, ⟨⟨j, gamma, delta⟩, ⟨kappa, z⟩⟩⟩
  invFun
    | ⟨i, ⟨⟨j, gamma, delta⟩, ⟨kappa, z⟩⟩⟩ =>
        ⟨⟨j, i, gamma, delta, kappa⟩, z⟩
  left_inv := by rintro ⟨⟨j, i, gamma, delta, kappa⟩, z⟩; rfl
  right_inv := by rintro ⟨i, ⟨⟨j, gamma, delta⟩, ⟨kappa, z⟩⟩⟩; rfl

private noncomputable def rightFourfoldFirstSynthesis (a b c d : Λ) :
    Matrix (Fus.FourfoldBond a b c d)
      (Fus.RightFourfoldFirstStage a b c d) ℂ :=
  ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
    Fus.rightTripleSynthesisFull b c d).submatrix
      (Fus.rightFourfoldBondEquiv a b c d) (Equiv.refl _)

private noncomputable def rightFourfoldFirstAnalysis (a b c d : Λ) :
    Matrix (Fus.RightFourfoldFirstStage a b c d)
      (Fus.FourfoldBond a b c d) ℂ :=
  ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
    Fus.rightTripleAnalysisFull b c d).submatrix
      (Equiv.refl _) (Fus.rightFourfoldBondEquiv a b c d)

private noncomputable def rightFourfoldSecondSynthesis (a b c d e : Λ) :
    Matrix (Fus.RightFourfoldFirstStage a b c d)
      (Fus.FourfoldRightAssocMultiplicity a b c d e × Fin (Fus.bondDim e)) ℂ :=
  (Matrix.blockDiagonal' fun i =>
    (1 : Matrix (Fus.RightTripleMultiplicity b c d i)
      (Fus.RightTripleMultiplicity b c d i) ℂ) ⊗ₖ
        Fus.fixedFinalSynthesis a i e).submatrix
          (Fus.rightFourfoldFirstStageEquiv a b c d)
          (Fus.rightFourfoldFinalEquiv a b c d e)

private noncomputable def rightFourfoldSecondAnalysis (a b c d e : Λ) :
    Matrix (Fus.FourfoldRightAssocMultiplicity a b c d e × Fin (Fus.bondDim e))
      (Fus.RightFourfoldFirstStage a b c d) ℂ :=
  (Matrix.blockDiagonal' fun i =>
    (1 : Matrix (Fus.RightTripleMultiplicity b c d i)
      (Fus.RightTripleMultiplicity b c d i) ℂ) ⊗ₖ
        Fus.fixedFinalAnalysis a i e).submatrix
          (Fus.rightFourfoldFinalEquiv a b c d e)
          (Fus.rightFourfoldFirstStageEquiv a b c d)

private theorem rightFourfoldSynthesis_eq_stages (a b c d e : Λ) :
    Fus.rightAssocFourfoldSynthesis a b c d e =
      Fus.rightFourfoldFirstSynthesis a b c d *
        Fus.rightFourfoldSecondSynthesis a b c d e := by
  classical
  funext ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩ ⟨⟨j, i, gamma, delta, kappa⟩, z⟩
  simp only [rightAssocFourfoldSynthesis, rightFourfoldFirstSynthesis,
    rightFourfoldBondEquiv, Equiv.coe_fn_mk, Equiv.coe_refl,
    rightFourfoldSecondSynthesis, rightFourfoldFirstStageEquiv,
    rightFourfoldFinalEquiv, Matrix.mul_apply, submatrix_apply, id_eq,
    kroneckerMap_apply, Matrix.one_apply, rightTripleSynthesisFull,
    rightTripleSynthesis, ite_mul, one_mul, zero_mul, blockDiagonal'_apply,
    fixedFinalSynthesis, mul_dite, mul_ite, mul_zero, Fintype.sum_prod_type,
    Fintype.sum_sigma, Finset.sum_dite_irrel, Finset.sum_const_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ↓reduceIte, cast_eq,
    Sigma.mk.injEq, Finset.sum_ite_irrel]
  rw [Finset.sum_eq_single xa
    (fun x _ hx => by simp [Ne.symm hx])
    (fun h => absurd (Finset.mem_univ xa) h)]
  rw [Finset.sum_eq_single j
    (fun x _ hx => by simp [hx])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp only [true_and, if_true, heq_eq_eq]
  rw [Finset.sum_eq_single gamma
    (fun x _ hx => by simp [hx])
    (fun h => absurd (Finset.mem_univ gamma) h)]
  simp only [Prod.mk.injEq, true_and]
  rw [Finset.sum_eq_single delta
    (fun x _ hx => by simp [hx])
    (fun h => absurd (Finset.mem_univ delta) h)]
  simp only [if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem rightFourfoldAnalysis_eq_stages (a b c d e : Λ) :
    Fus.rightAssocFourfoldAnalysis a b c d e =
      Fus.rightFourfoldSecondAnalysis a b c d e *
        Fus.rightFourfoldFirstAnalysis a b c d := by
  classical
  funext ⟨⟨j, i, gamma, delta, kappa⟩, z⟩ ⟨⟨⟨xa, xb⟩, xc⟩, xd⟩
  simp only [rightAssocFourfoldAnalysis, rightFourfoldSecondAnalysis,
    rightFourfoldFinalEquiv, Equiv.coe_fn_mk, rightFourfoldFirstStageEquiv,
    rightFourfoldFirstAnalysis, Equiv.coe_refl, rightFourfoldBondEquiv,
    Matrix.mul_apply, submatrix_apply, blockDiagonal'_apply,
    kroneckerMap_apply, Matrix.one_apply, fixedFinalAnalysis, ite_mul,
    one_mul, zero_mul, id_eq, rightTripleAnalysisFull, rightTripleAnalysis,
    mul_ite, dite_mul, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_irrel, Fintype.sum_sigma, Finset.sum_dite_irrel,
    Finset.sum_const_zero, Finset.sum_dite_eq, Finset.mem_univ,
    ↓reduceIte, cast_eq, Sigma.mk.injEq, Finset.sum_ite_eq']
  rw [Finset.sum_eq_single j
    (fun x _ hx => by simp [Ne.symm hx])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp only [true_and, heq_eq_eq]
  rw [Finset.sum_eq_single gamma
    (fun x _ hx => by simp [Ne.symm hx])
    (fun h => absurd (Finset.mem_univ gamma) h)]
  simp only [Prod.mk.injEq, true_and]
  rw [Finset.sum_eq_single delta
    (fun x _ hx => by simp [Ne.symm hx])
    (fun h => absurd (Finset.mem_univ delta) h)]
  simp only [if_true, Finset.mul_sum, mul_assoc]

private theorem rightFourfoldFirstAnalysis_mul_synthesis (a b c d : Λ) :
    Fus.rightFourfoldFirstAnalysis a b c d *
      Fus.rightFourfoldFirstSynthesis a b c d = 1 := by
  unfold rightFourfoldFirstAnalysis rightFourfoldFirstSynthesis
  rw [Matrix.submatrix_mul_equiv _ _ _ (Fus.rightFourfoldBondEquiv a b c d) _,
    ← Matrix.mul_kronecker_mul, Fus.rightTripleAnalysisFull_mul_synthesis,
    Matrix.one_mul, Matrix.one_kronecker_one]
  rfl

private theorem rightFourfoldSecondAnalysis_mul_synthesis (a b c d e : Λ) :
    Fus.rightFourfoldSecondAnalysis a b c d e *
      Fus.rightFourfoldSecondSynthesis a b c d e = 1 := by
  unfold rightFourfoldSecondAnalysis rightFourfoldSecondSynthesis
  rw [Matrix.submatrix_mul_equiv _ _ _
      (Fus.rightFourfoldFirstStageEquiv a b c d) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul, Fus.fixedFinalAnalysis_mul_synthesis,
    Matrix.one_mul, Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (i : Λ) → Matrix
      (Fus.RightTripleMultiplicity b c d i ×
        (Fin (Fus.fusionMultiplicity a i e) × Fin (Fus.bondDim e)))
      (Fus.RightTripleMultiplicity b c d i ×
        (Fin (Fus.fusionMultiplicity a i e) × Fin (Fus.bondDim e))) ℂ)).submatrix
          (Fus.rightFourfoldFinalEquiv a b c d e)
          (Fus.rightFourfoldFinalEquiv a b c d e) = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

/-- The right-associated fourfold analysis is a left inverse of its synthesis.

This is the threefold application of the fusion-tensor biorthogonality relation, starting with
the innermost fusion of `c` and `d` and ending with the fusion into the final label `e`.

Source: arXiv:1511.08090, the fusion left inverses at line 161 and the rightmost fourfold tree
in equation `pentagoneq`, lines 279--283. -/
theorem rightAssocFourfoldAnalysis_mul_synthesis (a b c d e : Λ) :
    Fus.rightAssocFourfoldAnalysis a b c d e *
      Fus.rightAssocFourfoldSynthesis a b c d e = 1 := by
  rw [Fus.rightFourfoldSynthesis_eq_stages, Fus.rightFourfoldAnalysis_eq_stages,
    Matrix.mul_assoc, ← Matrix.mul_assoc (Fus.rightFourfoldFirstAnalysis a b c d),
    Fus.rightFourfoldFirstAnalysis_mul_synthesis, Matrix.one_mul,
    Fus.rightFourfoldSecondAnalysis_mul_synthesis]
end MPOTensor.CompleteZipperFusionFamily
