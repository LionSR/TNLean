/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Algebra.Combinatorics.GeneralizeDecide
import TNLean.MPS.Examples.CZY.CZYReduced

/-!
# CZY fusion maps

The printed fusion matrices in arXiv:2509.03600, Section II and Appendix B,
satisfy the local intertwining identities, and the two full bond-space fusions
at `(1,1,1)` differ by a minus sign.

**Local fix (associativity):** The printed relation for every triple fails on the full
virtual space. At `(0,0,0)` no complex scalar relates the two maps. The corrected statement, on
the images of the three-layer physical letters, is proved in
`TNLean/MPS/Examples/CZY/CZYFusionAssociativity.lean`. The source assertion, counterexample and
corrected formulation are recorded in `docs/paper-gaps/lmsvkl25_czy_associator.tex`.
-/

noncomputable section

open scoped Matrix Kronecker BigOperators

namespace CZYCompression

open MPSTensor CZXCompression

/-- The first three rows of the integer matrix `√2 X₁₁`
(arXiv:2509.03600, Appendix B, main.tex lines 664–673 and 716). -/
def czyY11Int : Matrix (Fin 3) (Fin 4) ℤ := czyX11Int.submatrix Fin.castSucc id

/-- The first two rows of `X₀₁`
(arXiv:2509.03600, Appendix B, main.tex lines 675–687 and 716). -/
def czyY01Int : Matrix (Fin 2) (Fin 6) ℤ := !![0, 0, 1, 0, 0, -1; 0, 0, 0, 1, -1, 0]

/-- The first two rows of `X₁₀`
(arXiv:2509.03600, Appendix B, main.tex lines 689–701 and 716). -/
def czyY10Int : Matrix (Fin 2) (Fin 6) ℤ := !![0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 1, 0]

/-- The printed fusion map `Y₁₁`, with normalization `1 / √2`
(arXiv:2509.03600, Appendix B, main.tex lines 664–673 and 716). -/
def czyY11 : Matrix (Fin 3) (Fin 4) ℂ := Complex.invSqrtTwo • complexOfInt czyY11Int

/-- The printed fusion map `Y₀₁`
(arXiv:2509.03600, Appendix B, main.tex lines 675–687 and 716). -/
def czyY01 : Matrix (Fin 2) (Fin 6) ℂ := complexOfInt czyY01Int

/-- The printed fusion map `Y₁₀`
(arXiv:2509.03600, Appendix B, main.tex lines 689–701 and 716). -/
def czyY10 : Matrix (Fin 2) (Fin 6) ℂ := complexOfInt czyY10Int

/-- The fusion map is precisely the first three rows of the existing change of basis. -/
theorem czyY11_eq_submatrix : czyY11 = czyX11.submatrix Fin.castSucc id := by rfl

private theorem czyY11Int_fusion (i k : Fin 2) :
    czyY11Int * mulIntTensor czyIntTensor czyIntTensor i k =
    czyReducedIntTensor i k * czyY11Int := by
  revert_decide_kernel i k

private theorem czyY01Int_fusion (i k : Fin 2) :
    czyY01Int * mulIntTensor czyReducedIntTensor czyIntTensor i k =
    czyIntTensor i k * czyY01Int := by
  revert_decide_kernel i k

private theorem czyY10Int_fusion (i k : Fin 2) :
    czyY10Int * mulIntTensor czyIntTensor czyReducedIntTensor i k =
    czyIntTensor i k * czyY10Int := by
  revert_decide_kernel i k

/-- The two printed fusions at `(1,1,1)` differ by a minus sign
(arXiv:2509.03600, Section II, main.tex lines 283–294). This is an equality on the full
triple bond space; it does not assert the scalar relation at other triples. -/
theorem czyFusion_nontrivial_triple :
    czyY01 * (czyY11 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm =
    -(czyY10 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ czyY11).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [czyY01, czyY10, czyY11, czyY01Int, czyY10Int, czyY11Int, czyX11Int,
      complexOfInt, complexOfRing, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.one_apply]

/-- No scalar relates the printed fusions at `(0,0,0)`: the entry `(0,24)` is two on the
left and zero on the right. This refutes the unrestricted relation in arXiv:2509.03600,
Section II, main.tex lines 283–294; see `docs/paper-gaps/lmsvkl25_czy_associator.tex`. -/
theorem czyFusion_printed_neutral_no_scalar : ¬ ∃ ω : ℂ,
    complexOfInt czyY00Int *
      ((complexOfInt czyY00Int) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm =
    ω • (complexOfInt czyY00Int *
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (complexOfInt czyY00Int)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  rintro ⟨ω, h⟩
  have he := congrArg (fun M => M 0 24) h
  norm_num [czyY00Int, complexOfInt, complexOfRing, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.one_apply] at he

/-- The printed one-sided fusion identity
(arXiv:2509.03600, Section II, eq:Ydef, main.tex lines 249–253). -/
theorem czyY01_fusion (i k : Fin 2) : czyY01 * MPOTensor.mulTensor czyReducedTensor czyTensor i k =
    czyTensor i k * czyY01 := by
  rw [show MPOTensor.mulTensor czyReducedTensor czyTensor i k =
      complexOfInt (mulIntTensor czyReducedIntTensor czyIntTensor i k) from
    mulTensor_complexOfRing _ czyReducedIntTensor czyIntTensor i k]
  simpa only [czyY01, czyTensor, complexOfInt_mul]
    using congrArg complexOfInt (czyY01Int_fusion i k)

/-- The printed one-sided fusion identity
(arXiv:2509.03600, Section II, eq:Ydef, main.tex lines 249–253). -/
theorem czyY10_fusion (i k : Fin 2) : czyY10 * MPOTensor.mulTensor czyTensor czyReducedTensor i k =
    czyTensor i k * czyY10 := by
  rw [show MPOTensor.mulTensor czyTensor czyReducedTensor i k =
      complexOfInt (mulIntTensor czyIntTensor czyReducedIntTensor i k) from
    mulTensor_complexOfRing _ czyIntTensor czyReducedIntTensor i k]
  simpa only [czyY10, czyTensor, complexOfInt_mul]
    using congrArg complexOfInt (czyY10Int_fusion i k)

/-- The printed one-sided fusion identity
(arXiv:2509.03600, Section II, eq:Ydef, main.tex lines 249–253). -/
theorem czyY11_fusion (i k : Fin 2) : czyY11 * MPOTensor.mulTensor czyTensor czyTensor i k =
    czyReducedTensor i k * czyY11 := by
  rw [show MPOTensor.mulTensor czyTensor czyTensor i k =
      complexOfInt (mulIntTensor czyIntTensor czyIntTensor i k) from
    mulTensor_complexOfRing _ czyIntTensor czyIntTensor i k]
  simp only [czyY11, czyReducedTensor, Matrix.smul_mul, Matrix.mul_smul,
    ← complexOfInt_mul]
  exact congrArg (fun M => Complex.invSqrtTwo • complexOfInt M) (czyY11Int_fusion i k)

end CZYCompression
