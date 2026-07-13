/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionSupport

/-!
# The printed F-move

This file constructs the printed-orientation F-move after the equality of the
left- and right-associated product-MPO supports has been derived from the
source hypotheses.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

universe u

namespace CompleteZipperFusionFamily

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

/-- The source-oriented full change of triple-fusion basis.  It maps the
left-associated fusion coordinates to the right-associated fusion coordinates.

Its orientation is opposite to `BNTFusionIsometryFamily.tripleFusionComparison`:
the rows are right-tree coordinates and the columns are left-tree coordinates.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251. -/
noncomputable def fullPrintedFMatrix (a b c : Λ) :
    Matrix (Fus.RightTripleIndex a b c) (Fus.LeftTripleIndex a b c) ℂ :=
  Fus.rightTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c

/-- The source-oriented full comparison intertwines the two direct sums of
final-block letters.

Source: arXiv:1511.08090, equations `zippercondition2`, `pentagon3`, and the
argument at lines 247--277. -/
theorem rightTripleDirectSumLetter_mul_fullPrintedFMatrix
    (a b c : Λ) (i l : Fin p) :
    Fus.rightTripleDirectSumLetter a b c i l * Fus.fullPrintedFMatrix a b c =
      Fus.fullPrintedFMatrix a b c * Fus.leftTripleDirectSumLetter a b c i l := by
  unfold fullPrintedFMatrix
  calc
    Fus.rightTripleDirectSumLetter a b c i l *
          (Fus.rightTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c) =
        (Fus.rightTripleDirectSumLetter a b c i l *
          Fus.rightTripleAnalysisFull a b c) * Fus.leftTripleSynthesisFull a b c := by
      rw [Matrix.mul_assoc]
    _ = (Fus.rightTripleAnalysisFull a b c * Fus.tripleProductLetter a b c i l) *
        Fus.leftTripleSynthesisFull a b c := by
      rw [Fus.rightTripleAnalysisFull_mul_tripleProductLetter]
    _ = Fus.rightTripleAnalysisFull a b c *
        (Fus.tripleProductLetter a b c i l * Fus.leftTripleSynthesisFull a b c) := by
      rw [Matrix.mul_assoc]
    _ = Fus.rightTripleAnalysisFull a b c *
        (Fus.leftTripleSynthesisFull a b c *
          Fus.leftTripleDirectSumLetter a b c i l) := by
      rw [Fus.tripleProductLetter_mul_leftTripleSynthesisFull]
    _ = (Fus.rightTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c) *
        Fus.leftTripleDirectSumLetter a b c i l := by
      rw [Matrix.mul_assoc]

/-- The full source-oriented comparison carries the right-associated synthesis
map to the left-associated synthesis map. -/
theorem rightTripleSynthesisFull_mul_fullPrintedFMatrix (a b c : Λ) :
    Fus.rightTripleSynthesisFull a b c * Fus.fullPrintedFMatrix a b c =
      Fus.leftTripleSynthesisFull a b c := by
  unfold fullPrintedFMatrix
  calc
    Fus.rightTripleSynthesisFull a b c *
          (Fus.rightTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c) =
        (Fus.rightTripleSynthesisFull a b c *
          Fus.rightTripleAnalysisFull a b c) * Fus.leftTripleSynthesisFull a b c := by
      rw [Matrix.mul_assoc]
    _ = (Fus.leftTripleSynthesisFull a b c *
          Fus.leftTripleAnalysisFull a b c) * Fus.leftTripleSynthesisFull a b c := by
      rw [Fus.leftTripleSupport_eq_rightTripleSupport]
    _ = Fus.leftTripleSynthesisFull a b c *
        (Fus.leftTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c) := by
      rw [Matrix.mul_assoc]
    _ = Fus.leftTripleSynthesisFull a b c := by
      rw [Fus.leftTripleAnalysisFull_mul_synthesis, Matrix.mul_one]

/-- The full comparison in the opposite orientation. -/
noncomputable def fullInversePrintedFMatrix (a b c : Λ) :
    Matrix (Fus.LeftTripleIndex a b c) (Fus.RightTripleIndex a b c) ℂ :=
  Fus.leftTripleAnalysisFull a b c * Fus.rightTripleSynthesisFull a b c

/-- The two full comparison matrices are inverse in this order. -/
theorem fullPrintedFMatrix_mul_fullInversePrintedFMatrix (a b c : Λ) :
    Fus.fullPrintedFMatrix a b c * Fus.fullInversePrintedFMatrix a b c = 1 := by
  unfold fullPrintedFMatrix fullInversePrintedFMatrix
  calc
    (Fus.rightTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c) *
          (Fus.leftTripleAnalysisFull a b c * Fus.rightTripleSynthesisFull a b c) =
        Fus.rightTripleAnalysisFull a b c *
          ((Fus.leftTripleSynthesisFull a b c *
            Fus.leftTripleAnalysisFull a b c) *
              Fus.rightTripleSynthesisFull a b c) := by
      simp only [Matrix.mul_assoc]
    _ = Fus.rightTripleAnalysisFull a b c *
          ((Fus.rightTripleSynthesisFull a b c *
            Fus.rightTripleAnalysisFull a b c) *
              Fus.rightTripleSynthesisFull a b c) := by
      rw [Fus.leftTripleSupport_eq_rightTripleSupport]
    _ = Fus.rightTripleAnalysisFull a b c *
        (Fus.rightTripleSynthesisFull a b c *
          (Fus.rightTripleAnalysisFull a b c *
            Fus.rightTripleSynthesisFull a b c)) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Fus.rightTripleAnalysisFull_mul_synthesis, Matrix.mul_one,
        Fus.rightTripleAnalysisFull_mul_synthesis]

/-- The two full comparison matrices are inverse in the other order. -/
theorem fullInversePrintedFMatrix_mul_fullPrintedFMatrix (a b c : Λ) :
    Fus.fullInversePrintedFMatrix a b c * Fus.fullPrintedFMatrix a b c = 1 := by
  unfold fullPrintedFMatrix fullInversePrintedFMatrix
  calc
    (Fus.leftTripleAnalysisFull a b c * Fus.rightTripleSynthesisFull a b c) *
          (Fus.rightTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c) =
        Fus.leftTripleAnalysisFull a b c *
          ((Fus.rightTripleSynthesisFull a b c *
            Fus.rightTripleAnalysisFull a b c) *
              Fus.leftTripleSynthesisFull a b c) := by
      simp only [Matrix.mul_assoc]
    _ = Fus.leftTripleAnalysisFull a b c *
          ((Fus.leftTripleSynthesisFull a b c *
            Fus.leftTripleAnalysisFull a b c) *
              Fus.leftTripleSynthesisFull a b c) := by
      rw [← Fus.leftTripleSupport_eq_rightTripleSupport]
    _ = Fus.leftTripleAnalysisFull a b c *
        (Fus.leftTripleSynthesisFull a b c *
          (Fus.leftTripleAnalysisFull a b c *
            Fus.leftTripleSynthesisFull a b c)) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Fus.leftTripleAnalysisFull_mul_synthesis, Matrix.mul_one,
        Fus.leftTripleAnalysisFull_mul_synthesis]

/-- Include a fixed final label in the right-associated full coordinate space. -/
def rightFinalRow (a b c d : Λ) :
    Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d) →
      Fus.RightTripleIndex a b c :=
  fun x => ⟨d, x⟩

/-- Include a fixed final label in the left-associated full coordinate space. -/
def leftFinalRow (a b c d : Λ) :
    Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d) →
      Fus.LeftTripleIndex a b c :=
  fun x => ⟨d, x⟩

/-- The one-letter coefficient which selects the block with final label `d`.

Source: arXiv:1511.08090, the simultaneous inverse at lines 269--277. -/
private noncomputable def finalBlockSelector (d : Λ) (ik : Fin p × Fin p) : ℂ :=
  ∑ x : Fin (Fus.bondDim d), Fus.blockLeftInverse ⟨d, x, x⟩ ik

private theorem finalBlockSelector_apply (d e : Λ)
    (x y : Fin (Fus.bondDim e)) :
    (∑ i : Fin p, ∑ k : Fin p,
      Fus.finalBlockSelector d (i, k) * Fus.tensor e i k x y) =
      if h : d = e then if _ : h ▸ x = y then 1 else 0 else 0 := by
  classical
  simp only [finalBlockSelector, Finset.sum_mul]
  calc
    (∑ i : Fin p, ∑ k : Fin p, ∑ z : Fin (Fus.bondDim d),
        Fus.blockLeftInverse ⟨d, z, z⟩ (i, k) * Fus.tensor e i k x y) =
        ∑ z : Fin (Fus.bondDim d), ∑ i : Fin p, ∑ k : Fin p,
          Fus.blockLeftInverse ⟨d, z, z⟩ (i, k) * Fus.tensor e i k x y := by
      calc
        _ = ∑ i : Fin p, ∑ z : Fin (Fus.bondDim d), ∑ k : Fin p,
            Fus.blockLeftInverse ⟨d, z, z⟩ (i, k) * Fus.tensor e i k x y := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = if h : d = e then if _ : h ▸ x = y then 1 else 0 else 0 := by
      by_cases h : d = e
      · subst e
        simp_rw [Fus.blockLeftInverse_apply d d]
        simp
      · simp_rw [Fus.blockLeftInverse_apply d e]
        simp [h]

private theorem finalBlockSelector_sum (d e : Λ) :
    (∑ i : Fin p, ∑ k : Fin p,
      Fus.finalBlockSelector d (i, k) •
        (Fus.tensor e i k : Matrix (Fin (Fus.bondDim e))
          (Fin (Fus.bondDim e)) ℂ)) =
      if d = e then 1 else 0 := by
  classical
  funext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fus.finalBlockSelector_apply d e x y]
  by_cases h : d = e
  · subst e
    simp [Matrix.one_apply]
  · simp [h]

private theorem rectangularIntertwiner_eq_zero (d e : Λ) (hde : d ≠ e)
    (C : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim e)) ℂ)
    (hC : ∀ (i k : Fin p), Fus.tensor d i k * C = C * Fus.tensor e i k) :
    C = 0 := by
  classical
  calc
    C = (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) * C := by
      rw [Matrix.one_mul]
    _ = (∑ i : Fin p, ∑ k : Fin p,
          Fus.finalBlockSelector d (i, k) • Fus.tensor d i k) * C := by
      rw [Fus.finalBlockSelector_sum d d]
      simp
    _ = ∑ i : Fin p, ∑ k : Fin p,
          (Fus.finalBlockSelector d (i, k) • Fus.tensor d i k) * C := by
      rw [Matrix.sum_mul]
      congr 1
      funext i
      rw [Matrix.sum_mul]
    _ = ∑ i : Fin p, ∑ k : Fin p,
          C * (Fus.finalBlockSelector d (i, k) • Fus.tensor e i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rw [Matrix.smul_mul, Matrix.mul_smul, hC]
    _ = C * (∑ i : Fin p, ∑ k : Fin p,
          Fus.finalBlockSelector d (i, k) • Fus.tensor e i k) := by
      rw [Matrix.mul_sum]
      congr 1
      funext i
      rw [Matrix.mul_sum]
    _ = C * (0 : Matrix (Fin (Fus.bondDim e)) (Fin (Fus.bondDim e)) ℂ) := by
      rw [Fus.finalBlockSelector_sum d e, if_neg hde]
    _ = 0 := Matrix.mul_zero C

/-- The bond-amplified corner of the printed comparison at a fixed final label. -/
noncomputable def printedFMatrixAmplified (a b c d : Λ) :
    Matrix (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ :=
  (Fus.fullPrintedFMatrix a b c).submatrix
    (Fus.rightFinalRow a b c d) (Fus.leftFinalRow a b c d)

/-- The full printed comparison has no corner between distinct final labels.

The simultaneous inverse of the block letters extracts the identity in one
final block and zero in every other block.

Source: arXiv:1511.08090, the simultaneous inverse and fixed-final extraction
at lines 269--277. -/
theorem fullPrintedFMatrix_finalSector_eq_zero
    (a b c d d' : Λ) (hdd' : d ≠ d') :
    (Fus.fullPrintedFMatrix a b c).submatrix
      (Fus.rightFinalRow a b c d) (Fus.leftFinalRow a b c d') = 0 := by
  funext x y
  rcases x with ⟨mR, x⟩
  rcases y with ⟨mL, y⟩
  rcases mR with ⟨f, l, s⟩
  rcases mL with ⟨e, μ, ν⟩
  let mR : Fus.RightTripleMultiplicity a b c d := ⟨f, l, s⟩
  let mL : Fus.LeftTripleMultiplicity a b c d' := ⟨e, μ, ν⟩
  let C : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d')) ℂ :=
    fun u v => Fus.fullPrintedFMatrix a b c
      (Fus.rightFinalRow a b c d ⟨mR, u⟩)
      (Fus.leftFinalRow a b c d' ⟨mL, v⟩)
  have hC : ∀ (i k : Fin p), Fus.tensor d i k * C = C * Fus.tensor d' i k := by
    intro i k
    funext u v
    have hFull := Fus.rightTripleDirectSumLetter_mul_fullPrintedFMatrix a b c i k
    have hEntry := congrArg
      (fun M => M (Fus.rightFinalRow a b c d ⟨mR, u⟩)
        (Fus.leftFinalRow a b c d' ⟨mL, v⟩)) hFull
    have hLeft :
        (Fus.rightTripleDirectSumLetter a b c i k *
          Fus.fullPrintedFMatrix a b c)
            (Fus.rightFinalRow a b c d ⟨mR, u⟩)
            (Fus.leftFinalRow a b c d' ⟨mL, v⟩) =
          ∑ z : Fin (Fus.bondDim d), Fus.tensor d i k u z *
            Fus.fullPrintedFMatrix a b c
              (Fus.rightFinalRow a b c d ⟨mR, z⟩)
              (Fus.leftFinalRow a b c d' ⟨mL, v⟩) := by
      rw [Matrix.mul_apply, Fintype.sum_sigma]
      rw [Finset.sum_eq_single d
        (fun q _ hq => Finset.sum_eq_zero fun z _ => by
          rw [rightTripleDirectSumLetter, rightFinalRow,
            Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hq), zero_mul])
        (fun h => absurd (Finset.mem_univ d) h)]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single mR
        (fun q _ hq => Finset.sum_eq_zero fun z _ => by
          rw [rightTripleDirectSumLetter, rightFinalRow,
            Matrix.blockDiagonal'_apply_eq]
          simp only [kroneckerMap_apply, Matrix.one_apply,
            if_neg (Ne.symm hq), zero_mul])
        (fun h => absurd (Finset.mem_univ mR) h)]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [rightTripleDirectSumLetter, rightFinalRow, leftFinalRow,
        Matrix.blockDiagonal'_apply_eq]
    have hRight :
        (Fus.fullPrintedFMatrix a b c * Fus.leftTripleDirectSumLetter a b c i k)
            (Fus.rightFinalRow a b c d ⟨mR, u⟩)
            (Fus.leftFinalRow a b c d' ⟨mL, v⟩) =
          ∑ z : Fin (Fus.bondDim d'),
            Fus.fullPrintedFMatrix a b c
              (Fus.rightFinalRow a b c d ⟨mR, u⟩)
              (Fus.leftFinalRow a b c d' ⟨mL, z⟩) *
                Fus.tensor d' i k z v := by
      rw [Matrix.mul_apply, Fintype.sum_sigma]
      rw [Finset.sum_eq_single d'
        (fun q _ hq => Finset.sum_eq_zero fun z _ => by
          rw [leftTripleDirectSumLetter, leftFinalRow,
            Matrix.blockDiagonal'_apply_ne _ _ _ hq, mul_zero])
        (fun h => absurd (Finset.mem_univ d') h)]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single mL
        (fun q _ hq => Finset.sum_eq_zero fun z _ => by
          simp [leftTripleDirectSumLetter, rightFinalRow, leftFinalRow,
            Matrix.blockDiagonal'_apply_eq, hq])
        (fun h => absurd (Finset.mem_univ mL) h)]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [leftTripleDirectSumLetter, rightFinalRow, leftFinalRow,
        Matrix.blockDiagonal'_apply_eq]
    exact hLeft.symm.trans (hEntry.trans hRight)
  have hZero := Fus.rectangularIntertwiner_eq_zero d d' hdd' C hC
  exact congrArg (fun M => M x y) hZero

/-- The fixed-final corner of the printed comparison acts only on fusion
multiplicity coordinates.

Source: arXiv:1511.08090, the injectivity argument and tensor-factor
conclusion at lines 269--277. -/
theorem exists_printedFMatrixAmplified_eq_kronecker_one (a b c d : Λ) :
    ∃ F : Matrix (Fus.RightTripleMultiplicity a b c d)
        (Fus.LeftTripleMultiplicity a b c d) ℂ,
      Fus.printedFMatrixAmplified a b c d =
        F ⊗ₖ (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) := by
  apply Matrix.exists_eq_kronecker_one_of_intertwines_span_eq_top
    (Fus.tensor d).toMPSTensor (Fus.printedFMatrixAmplified a b c d)
    (Fus.tensor_injective d).span_eq_top
  intro ij
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ij
  have hFull := Fus.rightTripleDirectSumLetter_mul_fullPrintedFMatrix a b c i k
  funext x y
  rcases x with ⟨mR, x⟩
  rcases y with ⟨mL, y⟩
  have hEntry := congrArg
    (fun M => M (Fus.rightFinalRow a b c d ⟨mR, x⟩)
      (Fus.leftFinalRow a b c d ⟨mL, y⟩)) hFull
  have hLeft :
      (Fus.rightTripleDirectSumLetter a b c i k * Fus.fullPrintedFMatrix a b c)
          (Fus.rightFinalRow a b c d ⟨mR, x⟩)
          (Fus.leftFinalRow a b c d ⟨mL, y⟩) =
        ∑ z : Fin (Fus.bondDim d), Fus.tensor d i k x z *
          Fus.fullPrintedFMatrix a b c
            (Fus.rightFinalRow a b c d ⟨mR, z⟩)
            (Fus.leftFinalRow a b c d ⟨mL, y⟩) := by
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single d
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        rw [rightTripleDirectSumLetter, rightFinalRow,
          Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hq), zero_mul])
      (fun h => absurd (Finset.mem_univ d) h)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single mR
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        rw [rightTripleDirectSumLetter, rightFinalRow,
          Matrix.blockDiagonal'_apply_eq]
        simp only [kroneckerMap_apply, Matrix.one_apply,
          if_neg (Ne.symm hq), zero_mul])
      (fun h => absurd (Finset.mem_univ mR) h)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [rightTripleDirectSumLetter, rightFinalRow, leftFinalRow,
      Matrix.blockDiagonal'_apply_eq]
  have hRight :
      (Fus.fullPrintedFMatrix a b c * Fus.leftTripleDirectSumLetter a b c i k)
          (Fus.rightFinalRow a b c d ⟨mR, x⟩)
          (Fus.leftFinalRow a b c d ⟨mL, y⟩) =
        ∑ z : Fin (Fus.bondDim d),
          Fus.fullPrintedFMatrix a b c
            (Fus.rightFinalRow a b c d ⟨mR, x⟩)
            (Fus.leftFinalRow a b c d ⟨mL, z⟩) * Fus.tensor d i k z y := by
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single d
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        rw [leftTripleDirectSumLetter, leftFinalRow,
          Matrix.blockDiagonal'_apply_ne _ _ _ hq, mul_zero])
      (fun h => absurd (Finset.mem_univ d) h)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single mL
      (fun q _ hq => Finset.sum_eq_zero fun z _ => by
        simp [leftTripleDirectSumLetter, rightFinalRow, leftFinalRow,
          Matrix.blockDiagonal'_apply_eq, hq])
      (fun h => absurd (Finset.mem_univ mL) h)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [leftTripleDirectSumLetter, rightFinalRow, leftFinalRow,
      Matrix.blockDiagonal'_apply_eq]
  have hSimple := hLeft.symm.trans (hEntry.trans hRight)
  simpa [printedFMatrixAmplified, MPOTensor.toMPSTensor,
    Matrix.submatrix_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply] using hSimple

/-- The printed $F$-matrix.  Its rows are the right-tree indices
$(f,\lambda,\sigma)$ and its columns are the left-tree indices
$(e,\mu,\nu)$.  It is the multiplicity factor of
$R_d^+L_d$, where $R_d^+L_d$ acts as this matrix tensored with the identity on
the final bond space.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, and the
fixed-final extraction at lines 269--277. -/
noncomputable def printedFMatrix (a b c d : Λ) :
    Matrix (Fus.RightTripleMultiplicity a b c d)
      (Fus.LeftTripleMultiplicity a b c d) ℂ :=
  Classical.choose (Fus.exists_printedFMatrixAmplified_eq_kronecker_one a b c d)

/-- The bond-amplified fixed-final comparison is the printed $F$-matrix
tensored with the identity. -/
theorem printedFMatrixAmplified_eq_kronecker_one (a b c d : Λ) :
    Fus.printedFMatrixAmplified a b c d =
      Fus.printedFMatrix a b c d ⊗ₖ
        (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ) :=
  Classical.choose_spec (Fus.exists_printedFMatrixAmplified_eq_kronecker_one a b c d)

/-- **The printed F-move.**  The left-associated triple fusion tensors are
linear combinations of the right-associated triple fusion tensors:
\[
 (X^e_{ab,\mu}\otimes 1)X^d_{ec,\nu}
 =\sum_{f,\lambda,\sigma}
   (F^{abc}_d)^{f\lambda\sigma}_{e\mu\nu}
   (1\otimes X^f_{bc,\lambda})X^d_{af,\sigma}.
\]

The statement assumes only the complete zipper fusion family above.  It does
not use the length-independence, selector, or present-blocking hypotheses of
the restricted positive-diagonal specialization.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251, with the
fixed-final argument at lines 252--277. -/
theorem rightTripleSynthesis_mul_printedFMatrix (a b c d : Λ) :
    Fus.rightTripleSynthesis a b c d *
        (Fus.printedFMatrix a b c d ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim d)) (Fin (Fus.bondDim d)) ℂ)) =
      Fus.leftTripleSynthesis a b c d := by
  rw [← Fus.printedFMatrixAmplified_eq_kronecker_one a b c d]
  funext x y
  have hFull := Fus.rightTripleSynthesisFull_mul_fullPrintedFMatrix a b c
  have hEntry := congrArg
    (fun M => M x (Fus.leftFinalRow a b c d y)) hFull
  rw [Matrix.mul_apply, Fintype.sum_sigma] at hEntry
  rw [Finset.sum_eq_single d
    (fun e _ hed => Finset.sum_eq_zero fun q _ => by
      have hZero : Fus.fullPrintedFMatrix a b c ⟨e, q⟩
          (Fus.leftFinalRow a b c d y) = 0 := by
        simpa [Matrix.submatrix_apply, rightFinalRow, leftFinalRow] using
          congrArg (fun M => M q y)
            (Fus.fullPrintedFMatrix_finalSector_eq_zero a b c e d hed)
      rw [hZero, mul_zero])
    (fun h => absurd (Finset.mem_univ d) h)] at hEntry
  simpa [Matrix.mul_apply, printedFMatrixAmplified, Matrix.submatrix_apply,
    rightTripleSynthesisFull, leftTripleSynthesisFull, rightFinalRow,
    leftFinalRow] using hEntry

end CompleteZipperFusionFamily

end MPOTensor
