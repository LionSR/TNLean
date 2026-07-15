/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTTripleFusionSeparation

/-!
# Unitarity of fixed-final triple-fusion comparisons

Under the positive trace-power and length-independence hypotheses,
positive-length final-label selectors make the full triple-fusion comparison
unitary and separate its distinct final-label sectors. Reordering the full
direct sums by their final label therefore makes every diagonal sector corner
unitary. If the selected final tensor is injective, the amplified commutant
argument writes this corner as \(F_\varepsilon \otimes 1\). Positivity of the
bond dimension then permits cancellation of the identity factor, proving both
unitarity identities for \(F_\varepsilon\).

These conclusions remain conditional on simultaneous final-label selectors
and injectivity at the present blocking. The comparison used here has the
opposite orientation from the matrix printed in equation (Fmove) of
arXiv:1511.08090. No pentagon identity is asserted.

## References

* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, lines 247--280
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 995--1010
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace Matrix

universe u

/-- A diagonal corner of a right-unitary matrix over dependent direct sums is
right-unitary when all off-diagonal corners in the same row vanish.

Source: direct-sum matrix bookkeeping for the fixed-output-channel argument in
arXiv:1511.08090, lines 247--277. -/
theorem sigmaDiagonal_mul_conjTranspose_eq_one
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {L R : ι → Type*} [∀ i, DecidableEq (L i)] [∀ i, Fintype (R i)]
    (C : Matrix ((i : ι) × L i) ((i : ι) × R i) ℂ)
    (hunit : C * Cᴴ = 1)
    (hoff : ∀ i j, j ≠ i →
      C.submatrix (fun x : L i => ⟨i, x⟩) (fun y : R j => ⟨j, y⟩) = 0)
    (i : ι) :
    C.submatrix (fun x : L i => ⟨i, x⟩) (fun y : R i => ⟨i, y⟩) *
        (C.submatrix (fun x : L i => ⟨i, x⟩) (fun y : R i => ⟨i, y⟩))ᴴ = 1 := by
  ext x y
  have hentry := congrArg (fun M => M ⟨i, x⟩ ⟨i, y⟩) hunit
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Matrix.submatrix_apply, Fintype.sum_sigma] at hentry ⊢
  rw [Finset.sum_eq_single i] at hentry
  · by_cases hxy : x = y
    · subst y
      simpa using hentry
    · have hsigma : Sigma.mk i x ≠ Sigma.mk i y := by
        intro h
        cases h
        exact hxy rfl
      simp only [hxy, hsigma, ↓reduceIte] at hentry ⊢
      exact hentry
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro z _
    have hz := congrArg (fun M => M x z) (hoff i j hji)
    simp only [Matrix.submatrix_apply, Matrix.zero_apply] at hz
    simp [hz]
  · simp

/-- A diagonal corner of a left-unitary matrix over dependent direct sums is
left-unitary when all off-diagonal corners in the same column vanish.

Source: direct-sum matrix bookkeeping for the fixed-output-channel argument in
arXiv:1511.08090, lines 247--277. -/
theorem sigmaDiagonal_conjTranspose_mul_eq_one
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {L R : ι → Type*} [∀ i, Fintype (L i)] [∀ i, DecidableEq (R i)]
    (C : Matrix ((i : ι) × L i) ((i : ι) × R i) ℂ)
    (hunit : Cᴴ * C = 1)
    (hoff : ∀ i j, j ≠ i →
      C.submatrix (fun x : L j => ⟨j, x⟩) (fun y : R i => ⟨i, y⟩) = 0)
    (i : ι) :
    (C.submatrix (fun x : L i => ⟨i, x⟩) (fun y : R i => ⟨i, y⟩))ᴴ *
        C.submatrix (fun x : L i => ⟨i, x⟩) (fun y : R i => ⟨i, y⟩) = 1 := by
  ext x y
  have hentry := congrArg (fun M => M ⟨i, x⟩ ⟨i, y⟩) hunit
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Matrix.submatrix_apply, Fintype.sum_sigma] at hentry ⊢
  rw [Finset.sum_eq_single i] at hentry
  · by_cases hxy : x = y
    · subst y
      simpa using hentry
    · have hsigma : Sigma.mk i x ≠ Sigma.mk i y := by
        intro h
        cases h
        exact hxy rfl
      simp only [hxy, hsigma, ↓reduceIte] at hentry ⊢
      exact hentry
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro z _
    have hz := congrArg (fun M => M z x) (hoff i j hji)
    simp only [Matrix.submatrix_apply, Matrix.zero_apply] at hz
    simp [hz]
  · simp

private theorem mul_conjTranspose_eq_one_of_kronecker_one
    {m n : Type*} [DecidableEq m] [Fintype n]
    {D : ℕ} (hD : 0 < D)
    (F : Matrix m n ℂ)
    (hF : (F ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
      (F ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ = 1) :
    F * Fᴴ = 1 := by
  let b : Fin D := ⟨0, hD⟩
  ext i j
  have hentry := congrArg (fun M => M (i, b) (j, b)) hF
  simpa [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.one_apply, b] using hentry

private theorem conjTranspose_mul_eq_one_of_kronecker_one
    {m n : Type*} [Fintype m] [DecidableEq n]
    {D : ℕ} (hD : 0 < D)
    (F : Matrix m n ℂ)
    (hF : (F ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ *
      (F ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) = 1) :
    Fᴴ * F = 1 := by
  let b : Fin D := ⟨0, hD⟩
  ext i j
  have hentry := congrArg (fun M => M (i, b) (j, b)) hF
  simpa [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.one_apply, b] using hentry

end Matrix

namespace MPOTensor.BNTFusionIsometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

/-- The canonical reordering which places the final label before the left
fixed-final index.

Source: index bookkeeping for arXiv:1511.08090, equation (Fmove), whose fixed
output label is denoted by d. -/
def leftTripleFinalEquiv (α β γ : Λ) :
    Fam.LeftTripleFusionIndex α β γ ≃
      (ε : Λ) × Fam.LeftFinalIndex α β γ ε where
  toFun
    | ⟨δ, ε, μ, ν, b⟩ => ⟨ε, δ, μ, ν, b⟩
  invFun
    | ⟨ε, δ, μ, ν, b⟩ => ⟨δ, ε, μ, ν, b⟩
  left_inv x := by rcases x with ⟨δ, ε, μ, ν, b⟩; rfl
  right_inv x := by rcases x with ⟨ε, δ, μ, ν, b⟩; rfl

/-- The canonical reordering which places the final label before the right
fixed-final index.

Source: index bookkeeping for arXiv:1511.08090, equation (Fmove), whose fixed
output label is denoted by d. -/
def rightTripleFinalEquiv (α β γ : Λ) :
    Fam.RightTripleFusionIndex α β γ ≃
      (ε : Λ) × Fam.RightFinalIndex α β γ ε where
  toFun
    | ⟨δ, ε, μ, ν, b⟩ => ⟨ε, δ, μ, ν, b⟩
  invFun
    | ⟨ε, δ, μ, ν, b⟩ => ⟨δ, ε, μ, ν, b⟩
  left_inv x := by rcases x with ⟨δ, ε, μ, ν, b⟩; rfl
  right_inv x := by rcases x with ⟨ε, δ, μ, ν, b⟩; rfl

@[simp] private theorem leftTripleFinalEquiv_symm_sigmaMk
    (α β γ ε : Λ) (x : Fam.LeftFinalIndex α β γ ε) :
    (Fam.leftTripleFinalEquiv α β γ).symm ⟨ε, x⟩ =
      Fam.leftFinalRow α β γ ε x := by
  rcases x with ⟨δ, μ, ν, b⟩
  rfl

@[simp] private theorem rightTripleFinalEquiv_symm_sigmaMk
    (α β γ ε : Λ) (x : Fam.RightFinalIndex α β γ ε) :
    (Fam.rightTripleFinalEquiv α β γ).symm ⟨ε, x⟩ =
      Fam.rightFinalRow α β γ ε x := by
  rcases x with ⟨δ, μ, ν, b⟩
  rfl

private theorem leftTripleFinalEquiv_symm_comp (α β γ ε : Λ) :
    (Fam.leftTripleFinalEquiv α β γ).symm ∘
        (fun x : Fam.LeftFinalIndex α β γ ε => ⟨ε, x⟩) =
      Fam.leftFinalRow α β γ ε := by
  funext x
  exact Fam.leftTripleFinalEquiv_symm_sigmaMk α β γ ε x

private theorem rightTripleFinalEquiv_symm_comp (α β γ ε : Λ) :
    (Fam.rightTripleFinalEquiv α β γ).symm ∘
        (fun x : Fam.RightFinalIndex α β γ ε => ⟨ε, x⟩) =
      Fam.rightFinalRow α β γ ε := by
  funext x
  exact Fam.rightTripleFinalEquiv_symm_sigmaMk α β γ ε x

/-- **A fixed-final comparison corner has a right adjoint inverse.**

Suppose that common words of one positive length separate the final-label
tensors and that the positive trace-power coefficients are independent of the
positive chain length. Then each diagonal final-sector corner of the full
triple-fusion comparison satisfies \(C_\varepsilon C_\varepsilon^\dagger=1\).

**Scope restriction (simultaneous final-label separation):** the selector
hypothesis is not derived from the fusion-isometry family; see
docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex.

Source: arXiv:1511.08090, lines 247--277, especially the simultaneous inverse
at line 269; arXiv:1606.00608, lines 995--1010. -/
theorem tripleFusionComparison_finalSector_mul_conjTranspose_eq_one
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S)
    (α β γ ε : Λ) :
    (Fam.tripleFusionComparison α β γ).submatrix
          (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε) *
        ((Fam.tripleFusionComparison α β γ).submatrix
          (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε))ᴴ = 1 := by
  let C := Fam.tripleFusionComparison α β γ
  let C' := C.submatrix (Fam.leftTripleFinalEquiv α β γ).symm
    (Fam.rightTripleFinalEquiv α β γ).symm
  have hunit : C' * C'ᴴ = 1 := by
    unfold C'
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ (Fam.rightTripleFinalEquiv α β γ).symm _,
      Fam.tripleFusionComparison_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
        c hχ hLI hS hSel, Matrix.submatrix_one_equiv]
  have hoff : ∀ i j, j ≠ i →
      C'.submatrix
        (fun x : Fam.LeftFinalIndex α β γ i => ⟨i, x⟩)
        (fun y : Fam.RightFinalIndex α β γ j => ⟨j, y⟩) = 0 := by
    intro i j hji
    simpa only [C', Matrix.submatrix_submatrix,
      leftTripleFinalEquiv_symm_comp, rightTripleFinalEquiv_symm_comp] using
      Fam.tripleFusionComparison_finalSector_submatrix_eq_zero
        c hχ hLI hSel α β γ i j hji
  simpa only [C', Matrix.submatrix_submatrix,
    leftTripleFinalEquiv_symm_comp, rightTripleFinalEquiv_symm_comp] using
    Matrix.sigmaDiagonal_mul_conjTranspose_eq_one C' hunit hoff ε

/-- **A fixed-final comparison corner also has a left adjoint inverse.**

Under the same positive-length selector and length-independence hypotheses,
every diagonal corner satisfies
\(C_\varepsilon^\dagger C_\varepsilon=1\).

Together the two identities make the fixed-final bond-space comparison
unitary. No identification with the orientation of the printed \(F\)-matrix,
and no pentagon identity, is asserted.

**Scope restriction (simultaneous final-label separation):** the selector
hypothesis is not derived from the fusion-isometry family; see
docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex.

Source: arXiv:1511.08090, lines 247--277, especially the simultaneous inverse
at line 269; arXiv:1606.00608, lines 995--1010. -/
theorem conjTranspose_mul_tripleFusionComparison_finalSector_eq_one
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S)
    (α β γ ε : Λ) :
    ((Fam.tripleFusionComparison α β γ).submatrix
          (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε))ᴴ *
        (Fam.tripleFusionComparison α β γ).submatrix
          (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε) = 1 := by
  let C := Fam.tripleFusionComparison α β γ
  let C' := C.submatrix (Fam.leftTripleFinalEquiv α β γ).symm
    (Fam.rightTripleFinalEquiv α β γ).symm
  have hunit : C'ᴴ * C' = 1 := by
    unfold C'
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ (Fam.leftTripleFinalEquiv α β γ).symm _,
      Fam.conjTranspose_mul_tripleFusionComparison_eq_one_of_lengthIndependent_of_selectorWords
        c hχ hLI hS hSel, Matrix.submatrix_one_equiv]
  have hoff : ∀ i j, j ≠ i →
      C'.submatrix
        (fun x : Fam.LeftFinalIndex α β γ j => ⟨j, x⟩)
        (fun y : Fam.RightFinalIndex α β γ i => ⟨i, y⟩) = 0 := by
    intro i j hji
    simpa only [C', Matrix.submatrix_submatrix,
      leftTripleFinalEquiv_symm_comp, rightTripleFinalEquiv_symm_comp] using
      Fam.tripleFusionComparison_finalSector_submatrix_eq_zero
        c hχ hLI hSel α β γ j i hji.symm
  simpa only [C', Matrix.submatrix_submatrix,
    leftTripleFinalEquiv_symm_comp, rightTripleFinalEquiv_symm_comp] using
    Matrix.sigmaDiagonal_conjTranspose_mul_eq_one C' hunit hoff ε

/-- **Conditional unitarity of the fixed-final multiplicity matrix.**

Suppose the positive trace-power coefficients are independent of the positive
chain length, common words of one positive length separate the final-label
tensors, the selected final tensor is injective at the present blocking, and
its bond dimension is positive. Then the diagonal final-sector corner is
\(F_\varepsilon\otimes 1_{D_\varepsilon}\), where
\[
  F_\varepsilon F_\varepsilon^\dagger=1,
  \qquad
  F_\varepsilon^\dagger F_\varepsilon=1.
\]
Thus the multiplicity matrix is two-sided unitary, and in particular
invertible. The positive bond-dimension assumption is necessary for cancelling
the identity Kronecker factor; injectivity alone is vacuous on a zero-dimensional
bond space.

**Scope restriction (injectivity and simultaneous final-label separation):**
neither injectivity at the present blocking nor the selector hypothesis is
derived from the fusion-isometry family. This is documented in
docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex.

The comparison used here has the opposite orientation from the matrix printed
in equation (Fmove) of arXiv:1511.08090. No convention-identification or
pentagon identity is asserted.

Source: arXiv:1511.08090, equation (Fmove) and lines 247--280, especially the
simultaneous inverse at line 269 and the tensor-factor conclusion at line 277;
arXiv:1606.00608, lines 995--1010. -/
theorem exists_tripleFusionComparison_finalSector_eq_kronecker_one_and_unitary
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S)
    (α β γ ε : Λ)
    (hε : MPSTensor.IsInjective (Fam.tensor ε).toMPSTensor)
    (hD : 0 < Fam.bondDim ε) :
    ∃ F : Matrix (Fam.LeftFinalMultiplicity α β γ ε)
        (Fam.RightFinalMultiplicity α β γ ε) ℂ,
      ((Fam.tripleFusionComparison α β γ).submatrix
          (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε)).submatrix
            (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm =
          F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ) ∧
        F * Fᴴ = 1 ∧ Fᴴ * F = 1 := by
  obtain ⟨F, hF, -⟩ :=
    Fam.exists_tripleFusionComparison_finalSector_eq_kronecker_one_of_separation
      c hχ hLI hSel α β γ ε hε
  let C := (Fam.tripleFusionComparison α β γ).submatrix
    (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε)
  have hCC : C * Cᴴ = 1 :=
    Fam.tripleFusionComparison_finalSector_mul_conjTranspose_eq_one
      c hχ hLI hS hSel α β γ ε
  have hCdagC : Cᴴ * C = 1 :=
    Fam.conjTranspose_mul_tripleFusionComparison_finalSector_eq_one
      c hχ hLI hS hSel α β γ ε
  have hFFdag :
      (F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ)) *
          (F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ))ᴴ = 1 := by
    rw [← hF, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _
        (Fam.rightFinalIndexEquiv α β γ ε).symm _,
      hCC, Matrix.submatrix_one_equiv]
  have hFdagF :
      (F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ))ᴴ *
          (F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ)) = 1 := by
    rw [← hF, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _
        (Fam.leftFinalIndexEquiv α β γ ε).symm _,
      hCdagC, Matrix.submatrix_one_equiv]
  exact ⟨F, hF,
    Matrix.mul_conjTranspose_eq_one_of_kronecker_one hD F hFFdag,
    Matrix.conjTranspose_mul_eq_one_of_kronecker_one hD F hFdagF⟩

end MPOTensor.BNTFusionIsometryFamily
