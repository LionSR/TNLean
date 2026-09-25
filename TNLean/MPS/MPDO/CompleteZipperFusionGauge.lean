/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.MPDO.CompleteZipperFusionInverse

/-!
# Gauge covariance of the complete zipper F-matrices

The fusion tensors of a complete zipper fusion family are fixed only up to an invertible
change of basis of each multiplicity space: replacing $X^c_{ab,\mu}$ by
$\sum_\nu (Y^c_{ab})_{\nu\mu} X^c_{ab,\nu}$ and the left inverses by the inverse change
leaves the biorthogonality, zipper and reconstruction identities unchanged.  Under this
change the printed $F$-matrix of arXiv:1511.08090, equation `Fmove`, transforms by the
two tree gauges: on the left tree by $Y^e_{ab}\otimes Y^d_{ec}$, and on the right tree by
the inverse of $Y^f_{bc}\otimes Y^d_{af}$.

## Main definitions

* `MPOTensor.CompleteZipperFusionFamily.regauge`: the complete zipper fusion family with
  gauge-transformed fusion tensors and left inverses.
* `MPOTensor.CompleteZipperFusionFamily.leftTreeGauge`,
  `MPOTensor.CompleteZipperFusionFamily.rightTreeGauge`: the induced gauge on the
  multiplicity spaces of the two fusion trees.

## Main statements

* `MPOTensor.CompleteZipperFusionFamily.eq_printedFMatrix_of_rightTripleSynthesis_mul`:
  the printed $F$-matrix is the unique solution of equation `Fmove`.
* `MPOTensor.CompleteZipperFusionFamily.rightTreeGauge_mul_printedFMatrix_regauge`,
  `MPOTensor.CompleteZipperFusionFamily.printedFMatrix_regauge`: the gauge transformation
  law of the printed $F$-matrix.
* `MPOTensor.CompleteZipperFusionFamily.inversePrintedFMatrix_regauge`: the gauge
  transformation law of the inverse $F$-matrix.

## References

* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 164--166 (the gauge freedom of the fusion
  tensors) and lines 248--251 (equation `Fmove`).
* arXiv:2203.12563, `REsubmission.tex`, lines 415--422 (the induced transformation of the
  $F$-symbols).
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

/-! ### Uniqueness of the printed F-matrix -/

/-- The right-associated fixed-final analysis map is a left inverse of the right-associated
fixed-final synthesis map.

Source: arXiv:1511.08090, the biorthogonality relation at line 161, applied twice. -/
theorem rightTripleAnalysis_mul_rightTripleSynthesis (a b c d : Λ) :
    Fus.rightTripleAnalysis a b c d * Fus.rightTripleSynthesis a b c d = 1 := by
  funext x y
  have h := congrArg (fun M => M ⟨d, x⟩ ⟨d, y⟩) (Fus.rightTripleAnalysisFull_mul_synthesis a b c)
  simpa [Matrix.mul_apply, rightTripleAnalysisFull, rightTripleSynthesisFull,
    Matrix.one_apply] using h

/-- **Uniqueness of the printed F-matrix.** Any multiplicity matrix that carries the
right-associated fusion tensors to the left-associated ones, as in equation `Fmove`, is the
printed $F$-matrix.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, and the biorthogonality relation
at line 161. -/
theorem eq_printedFMatrix_of_rightTripleSynthesis_mul (a b c d : Λ)
    (G : Matrix (Fus.RightTripleMultiplicity a b c d) (Fus.LeftTripleMultiplicity a b c d) ℂ)
    (hG : Fus.rightTripleSynthesis a b c d *
        (G ⊗ₖ (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) =
      Fus.leftTripleSynthesis a b c d) :
    G = Fus.printedFMatrix a b c d := by
  apply Matrix.kronecker_one_injective (Fus.bondDim_pos d)
  have hF := Fus.rightTripleSynthesis_mul_printedFMatrix a b c d
  calc
    _ = (Fus.rightTripleAnalysis a b c d * Fus.rightTripleSynthesis a b c d) *
        (G ⊗ₖ (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) := by
      rw [Fus.rightTripleAnalysis_mul_rightTripleSynthesis, Matrix.one_mul]
    _ = (Fus.rightTripleAnalysis a b c d * Fus.rightTripleSynthesis a b c d) *
        (Fus.printedFMatrix a b c d ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) := by
      rw [Matrix.mul_assoc, hG, Matrix.mul_assoc, hF]
    _ = _ := by rw [Fus.rightTripleAnalysis_mul_rightTripleSynthesis, Matrix.one_mul]

/-! ### The gauge-transformed family -/

/-- A fusion gauge: an invertible matrix on each multiplicity space $\mathbb C^{N_{ab}^c}$.

Source: arXiv:1511.08090, lines 164--166; arXiv:2203.12563, lines 415--416. -/
abbrev FusionGauge : Type u :=
  ∀ a b c : Λ, GL (Fin (Fus.fusionMultiplicity a b c)) ℂ

variable {Fus}

/-- The block-diagonal matrix $\bigoplus_c Y^c_{ab}\otimes 1_{\chi_c}$ acting on the fusion
coordinates of the pair `a b`. -/
noncomputable def pairGauge (Y : Fus.FusionGauge) (a b : Λ) :
    Matrix ((c : Λ) × (Fin (Fus.fusionMultiplicity a b c) × Fin (Fus.bondDim c)))
      ((c : Λ) × (Fin (Fus.fusionMultiplicity a b c) × Fin (Fus.bondDim c))) ℂ :=
  Matrix.blockDiagonal' fun c =>
    ((Y a b c : GL (Fin (Fus.fusionMultiplicity a b c)) ℂ) :
        Matrix (Fin (Fus.fusionMultiplicity a b c)) (Fin (Fus.fusionMultiplicity a b c)) ℂ) ⊗ₖ
      (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ)

/-- The inverse block-diagonal matrix $\bigoplus_c (Y^c_{ab})^{-1}\otimes 1_{\chi_c}$. -/
noncomputable def pairGaugeInv (Y : Fus.FusionGauge) (a b : Λ) :
    Matrix ((c : Λ) × (Fin (Fus.fusionMultiplicity a b c) × Fin (Fus.bondDim c)))
      ((c : Λ) × (Fin (Fus.fusionMultiplicity a b c) × Fin (Fus.bondDim c))) ℂ :=
  Matrix.blockDiagonal' fun c =>
    (((Y a b c)⁻¹ : GL (Fin (Fus.fusionMultiplicity a b c)) ℂ) :
        Matrix (Fin (Fus.fusionMultiplicity a b c)) (Fin (Fus.fusionMultiplicity a b c)) ℂ) ⊗ₖ
      (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ)

/-- `pairGaugeInv` is a left inverse of `pairGauge`. -/
theorem pairGaugeInv_mul_pairGauge (Y : Fus.FusionGauge) (a b : Λ) :
    pairGaugeInv Y a b * pairGauge Y a b = 1 := by
  rw [pairGaugeInv, pairGauge, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1
  funext c
  rw [Pi.one_apply, ← Matrix.mul_kronecker_mul, Units.inv_mul, Matrix.one_mul,
    Matrix.one_kronecker_one]

/-- `pairGaugeInv` is a right inverse of `pairGauge`. -/
theorem pairGauge_mul_pairGaugeInv (Y : Fus.FusionGauge) (a b : Λ) :
    pairGauge Y a b * pairGaugeInv Y a b = 1 := by
  rw [pairGaugeInv, pairGauge, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1
  funext c
  rw [Pi.one_apply, ← Matrix.mul_kronecker_mul, Units.mul_inv, Matrix.one_mul,
    Matrix.one_kronecker_one]

/-- The fusion gauges commute with the direct sum of block letters, because they act only on
the multiplicity factors. -/
private theorem blockDiagonal_gauge_comm {ι : Type*} [DecidableEq ι] {m n : ι → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)] [Fintype ι]
    (Y : ∀ i, Matrix (m i) (m i) ℂ) (B : ∀ i, Matrix (n i) (n i) ℂ) :
    Matrix.blockDiagonal' (fun i => (1 : Matrix (m i) (m i) ℂ) ⊗ₖ B i) *
        Matrix.blockDiagonal' (fun i => Y i ⊗ₖ (1 : Matrix (n i) (n i) ℂ)) =
      Matrix.blockDiagonal' (fun i => Y i ⊗ₖ (1 : Matrix (n i) (n i) ℂ)) *
        Matrix.blockDiagonal' (fun i => (1 : Matrix (m i) (m i) ℂ) ⊗ₖ B i) := by
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_one]

variable (Fus)

/-- **The gauge-transformed complete zipper fusion family.** The fusion tensors are replaced
by $X'^c_{ab,\mu}=\sum_\nu (Y^c_{ab})_{\nu\mu}X^c_{ab,\nu}$ and the left inverses by the
inverse change of basis; the blocks, multiplicities and block left inverse are unchanged.

Source: arXiv:1511.08090, lines 164--166 (every transformed set of fusion tensors again
satisfies equation `gauge`); arXiv:2203.12563, lines 415--416.

The definition is reducible so that the bond dimensions and multiplicities of the regauged
family are syntactically those of the original family. -/
@[reducible] noncomputable def regauge (Y : Fus.FusionGauge) : CompleteZipperFusionFamily Λ p where
  bondDim := Fus.bondDim
  bondDim_pos := Fus.bondDim_pos
  tensor := Fus.tensor
  tensor_injective := Fus.tensor_injective
  fusionMultiplicity := Fus.fusionMultiplicity
  fusionSynthesis a b := Fus.fusionSynthesis a b * pairGauge Y a b
  fusionAnalysis a b := pairGaugeInv Y a b * Fus.fusionAnalysis a b
  analysis_mul_synthesis a b := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Fus.fusionAnalysis a b),
      Fus.analysis_mul_synthesis, Matrix.one_mul, pairGaugeInv_mul_pairGauge]
  pairLetter_mul_synthesis a b i k := by
    rw [← Matrix.mul_assoc, Fus.pairLetter_mul_synthesis, Matrix.mul_assoc, Matrix.mul_assoc,
      pairGauge, blockDiagonal_gauge_comm]
  analysis_mul_pairLetter a b i k := by
    rw [Matrix.mul_assoc, Fus.analysis_mul_pairLetter, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      pairGaugeInv, blockDiagonal_gauge_comm]
  pairLetter_eq_synthesis_mul_directSum_mul_analysis a b i k := by
    have hcomm := blockDiagonal_gauge_comm
      (fun c => ((Y a b c : GL (Fin (Fus.fusionMultiplicity a b c)) ℂ) :
        Matrix (Fin (Fus.fusionMultiplicity a b c)) (Fin (Fus.fusionMultiplicity a b c)) ℂ))
      (fun c => Fus.tensor c i k)
    rw [Fus.pairLetter_eq_synthesis_mul_directSum_mul_analysis]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (pairGauge Y a b), pairGauge, ← hcomm, ← pairGauge, Matrix.mul_assoc,
      ← Matrix.mul_assoc (pairGauge Y a b), pairGauge_mul_pairGaugeInv, Matrix.one_mul]
  blockLeftInverse := Fus.blockLeftInverse
  blockLeftInverse_apply := Fus.blockLeftInverse_apply

/-- The regauged fusion tensors are the prescribed combinations of the original ones. -/
theorem regauge_fusionTensor (Y : Fus.FusionGauge) (a b c : Λ)
    (μ : Fin (Fus.fusionMultiplicity a b c)) (x : Fin (Fus.bondDim a) × Fin (Fus.bondDim b))
    (z : Fin (Fus.bondDim c)) :
    (Fus.regauge Y).fusionTensor a b c μ x z =
      ∑ ν, Fus.fusionTensor a b c ν x z *
        (Y a b c : Matrix (Fin (Fus.fusionMultiplicity a b c))
          (Fin (Fus.fusionMultiplicity a b c)) ℂ) ν μ := by
  simp only [fusionTensor, regauge, pairGauge, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single c
    (fun c' _ hc' => Finset.sum_eq_zero fun q _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc', mul_zero])
    (fun h => absurd (Finset.mem_univ c) h)]
  simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-! ### The tree gauges -/

/-- The gauge $\bigoplus_e Y^e_{ab}\otimes Y^d_{ec}$ induced on the left-tree multiplicity
space.

Source: arXiv:2203.12563, lines 417--422. -/
noncomputable def leftTreeGauge (Y : Fus.FusionGauge) (a b c d : Λ) :
    Matrix (Fus.LeftTripleMultiplicity a b c d) (Fus.LeftTripleMultiplicity a b c d) ℂ :=
  Matrix.blockDiagonal' fun e =>
    ((Y a b e : GL _ ℂ) : Matrix _ _ ℂ) ⊗ₖ ((Y e c d : GL _ ℂ) : Matrix _ _ ℂ)

/-- The gauge $\bigoplus_f Y^f_{bc}\otimes Y^d_{af}$ induced on the right-tree multiplicity
space.

Source: arXiv:2203.12563, lines 417--422. -/
noncomputable def rightTreeGauge (Y : Fus.FusionGauge) (a b c d : Λ) :
    Matrix (Fus.RightTripleMultiplicity a b c d) (Fus.RightTripleMultiplicity a b c d) ℂ :=
  Matrix.blockDiagonal' fun f =>
    ((Y b c f : GL _ ℂ) : Matrix _ _ ℂ) ⊗ₖ ((Y a f d : GL _ ℂ) : Matrix _ _ ℂ)

/-- The inverse of `rightTreeGauge`, $\bigoplus_f (Y^f_{bc})^{-1}\otimes (Y^d_{af})^{-1}$. -/
noncomputable def rightTreeGaugeInv (Y : Fus.FusionGauge) (a b c d : Λ) :
    Matrix (Fus.RightTripleMultiplicity a b c d) (Fus.RightTripleMultiplicity a b c d) ℂ :=
  Matrix.blockDiagonal' fun f =>
    (((Y b c f)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) ⊗ₖ (((Y a f d)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)

/-- The inverse of `leftTreeGauge`, $\bigoplus_e (Y^e_{ab})^{-1}\otimes (Y^d_{ec})^{-1}$. -/
noncomputable def leftTreeGaugeInv (Y : Fus.FusionGauge) (a b c d : Λ) :
    Matrix (Fus.LeftTripleMultiplicity a b c d) (Fus.LeftTripleMultiplicity a b c d) ℂ :=
  Matrix.blockDiagonal' fun e =>
    (((Y a b e)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) ⊗ₖ (((Y e c d)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)

/-- `rightTreeGaugeInv` is a left inverse of `rightTreeGauge`. -/
theorem rightTreeGaugeInv_mul_rightTreeGauge (Y : Fus.FusionGauge) (a b c d : Λ) :
    Fus.rightTreeGaugeInv Y a b c d * Fus.rightTreeGauge Y a b c d = 1 := by
  rw [rightTreeGaugeInv, rightTreeGauge, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1
  funext e
  rw [Pi.one_apply, ← Matrix.mul_kronecker_mul, Units.inv_mul, Units.inv_mul,
    Matrix.one_kronecker_one]

/-- `rightTreeGaugeInv` is a right inverse of `rightTreeGauge`. -/
theorem rightTreeGauge_mul_rightTreeGaugeInv (Y : Fus.FusionGauge) (a b c d : Λ) :
    Fus.rightTreeGauge Y a b c d * Fus.rightTreeGaugeInv Y a b c d = 1 := by
  rw [rightTreeGaugeInv, rightTreeGauge, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1
  funext e
  rw [Pi.one_apply, ← Matrix.mul_kronecker_mul, Units.mul_inv, Units.mul_inv,
    Matrix.one_kronecker_one]

/-- `leftTreeGaugeInv` is a left inverse of `leftTreeGauge`. -/
theorem leftTreeGaugeInv_mul_leftTreeGauge (Y : Fus.FusionGauge) (a b c d : Λ) :
    Fus.leftTreeGaugeInv Y a b c d * Fus.leftTreeGauge Y a b c d = 1 := by
  rw [leftTreeGaugeInv, leftTreeGauge, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1
  funext e
  rw [Pi.one_apply, ← Matrix.mul_kronecker_mul, Units.inv_mul, Units.inv_mul,
    Matrix.one_kronecker_one]

/-- `leftTreeGaugeInv` is a right inverse of `leftTreeGauge`. -/
theorem leftTreeGauge_mul_leftTreeGaugeInv (Y : Fus.FusionGauge) (a b c d : Λ) :
    Fus.leftTreeGauge Y a b c d * Fus.leftTreeGaugeInv Y a b c d = 1 := by
  rw [leftTreeGaugeInv, leftTreeGauge, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1
  funext e
  rw [Pi.one_apply, ← Matrix.mul_kronecker_mul, Units.mul_inv, Units.mul_inv,
    Matrix.one_kronecker_one]

/-- The regauged left-associated synthesis map is the original one followed by the
left-tree gauge. -/
theorem regauge_leftTripleSynthesis (Y : Fus.FusionGauge) (a b c d : Λ) :
    (Fus.regauge Y).leftTripleSynthesis a b c d =
      Fus.leftTripleSynthesis a b c d *
        (Fus.leftTreeGauge Y a b c d ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) := by
  funext ⟨⟨xa, xb⟩, xc⟩ ⟨⟨e, μ, ν⟩, z⟩
  change (∑ y : Fin (Fus.bondDim e),
      (Fus.regauge Y).fusionTensor a b e μ
        ((xa, xb) : Fin (Fus.bondDim a) × Fin (Fus.bondDim b)) y *
      (Fus.regauge Y).fusionTensor e c d ν
        ((y, xc) : Fin (Fus.bondDim e) × Fin (Fus.bondDim c)) z) = _
  simp only [regauge_fusionTensor]
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sigma]
  rw [Finset.sum_eq_single e
    (fun e' _ he' => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ => by
      rw [Matrix.kronecker_apply, leftTreeGauge, Matrix.blockDiagonal'_apply_ne _ _ _ he',
        zero_mul, mul_zero])
    (fun h => absurd (Finset.mem_univ e) h)]
  simp only [Matrix.kronecker_apply, leftTreeGauge, Matrix.blockDiagonal'_apply_eq,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Fintype.sum_prod_type, leftTripleSynthesis, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The regauged right-associated synthesis map is the original one followed by the
right-tree gauge. -/
theorem regauge_rightTripleSynthesis (Y : Fus.FusionGauge) (a b c d : Λ) :
    (Fus.regauge Y).rightTripleSynthesis a b c d =
      Fus.rightTripleSynthesis a b c d *
        (Fus.rightTreeGauge Y a b c d ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) := by
  funext ⟨⟨xa, xb⟩, xc⟩ ⟨⟨f, l, s⟩, z⟩
  change (∑ y : Fin (Fus.bondDim f),
      (Fus.regauge Y).fusionTensor b c f l
        ((xb, xc) : Fin (Fus.bondDim b) × Fin (Fus.bondDim c)) y *
      (Fus.regauge Y).fusionTensor a f d s
        ((xa, y) : Fin (Fus.bondDim a) × Fin (Fus.bondDim f)) z) = _
  simp only [regauge_fusionTensor]
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sigma]
  rw [Finset.sum_eq_single f
    (fun f' _ hf' => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ => by
      rw [Matrix.kronecker_apply, rightTreeGauge, Matrix.blockDiagonal'_apply_ne _ _ _ hf',
        zero_mul, mul_zero])
    (fun h => absurd (Finset.mem_univ f) h)]
  simp only [Matrix.kronecker_apply, rightTreeGauge, Matrix.blockDiagonal'_apply_eq,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Fintype.sum_prod_type, rightTripleSynthesis, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! ### Transformation of the F-matrices -/

/-- **Gauge covariance of the printed F-matrix**: $F' = G_R^{-1}\,F\,G_L$, the transformation
of arXiv:2203.12563, lines 417--422, in the orientation of equation `Fmove` of
arXiv:1511.08090.  The right-hand side satisfies equation `Fmove` for the regauged family, so
it is the printed $F$-matrix of that family by uniqueness
(`eq_printedFMatrix_of_rightTripleSynthesis_mul`). -/
theorem printedFMatrix_regauge (Y : Fus.FusionGauge) (a b c d : Λ) :
    (Fus.regauge Y).printedFMatrix a b c d =
      Fus.rightTreeGaugeInv Y a b c d * Fus.printedFMatrix a b c d *
        Fus.leftTreeGauge Y a b c d := by
  refine ((Fus.regauge Y).eq_printedFMatrix_of_rightTripleSynthesis_mul a b c d _ ?_).symm
  rw [regauge_rightTripleSynthesis, regauge_leftTripleSynthesis, Matrix.mul_assoc,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Fus.rightTreeGauge_mul_rightTreeGaugeInv, Matrix.one_mul,
    ← Fus.rightTripleSynthesis_mul_printedFMatrix, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one]

/-- **Gauge covariance of the printed F-matrix**, intertwining form:
$G_R\,F' = F\,G_L$, where $F'$ is the printed $F$-matrix of the regauged family and $G_L$,
$G_R$ are the induced gauges of the two fusion trees.

Source: arXiv:2203.12563, lines 415--422; arXiv:1511.08090, lines 164--166 and equation
`Fmove`, lines 248--251. -/
theorem rightTreeGauge_mul_printedFMatrix_regauge (Y : Fus.FusionGauge) (a b c d : Λ) :
    Fus.rightTreeGauge Y a b c d * (Fus.regauge Y).printedFMatrix a b c d =
      Fus.printedFMatrix a b c d * Fus.leftTreeGauge Y a b c d := by
  rw [Fus.printedFMatrix_regauge, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Fus.rightTreeGauge_mul_rightTreeGaugeInv, Matrix.one_mul]

/-- **Gauge covariance of the inverse F-matrix**: $(F')^{-1} = G_L^{-1}\,F^{-1}\,G_R$.

Source: arXiv:2203.12563, lines 417--422; arXiv:1511.08090, equation `Fmove`, lines
248--251. -/
theorem inversePrintedFMatrix_regauge (Y : Fus.FusionGauge) (a b c d : Λ) :
    (Fus.regauge Y).inversePrintedFMatrix a b c d =
      Fus.leftTreeGaugeInv Y a b c d * Fus.inversePrintedFMatrix a b c d *
        Fus.rightTreeGauge Y a b c d := by
  set F' : Matrix (Fus.RightTripleMultiplicity a b c d) (Fus.LeftTripleMultiplicity a b c d) ℂ :=
    (Fus.regauge Y).printedFMatrix a b c d with hF'def
  set G' : Matrix (Fus.LeftTripleMultiplicity a b c d) (Fus.RightTripleMultiplicity a b c d) ℂ :=
    (Fus.regauge Y).inversePrintedFMatrix a b c d
  set X := Fus.leftTreeGaugeInv Y a b c d * Fus.inversePrintedFMatrix a b c d *
    Fus.rightTreeGauge Y a b c d
  have hFX : F' * X = 1 := by
    rw [hF'def, Fus.printedFMatrix_regauge]
    simp only [X, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Fus.leftTreeGauge Y a b c d), Fus.leftTreeGauge_mul_leftTreeGaugeInv,
      Matrix.one_mul, ← Matrix.mul_assoc (Fus.printedFMatrix a b c d),
      Fus.printedFMatrix_mul_inversePrintedFMatrix, Matrix.one_mul,
      Fus.rightTreeGaugeInv_mul_rightTreeGauge]
  have hGF : G' * F' = 1 := (Fus.regauge Y).inversePrintedFMatrix_mul_printedFMatrix a b c d
  calc
    G' = (G' * F') * X := by rw [Matrix.mul_assoc, hFX, Matrix.mul_one]
    _ = X := by rw [hGF, Matrix.one_mul]

end MPOTensor.CompleteZipperFusionFamily
