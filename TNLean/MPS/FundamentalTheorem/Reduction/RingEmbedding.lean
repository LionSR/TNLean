/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Kraus.Injectivity
import TNLean.Algebra.ComplexOfRing
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.MPDO.ActionTensor
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Bond-space products and actions over a ring embedded in the complex numbers

**Source.** None: this is infrastructure of this development for exact arithmetic in the worked
examples, and no paper states it.

**Formalized here.** The worked examples of compression data are given by matrices over a
commutative ring with decidable equality, and their word evaluations, bond-space products and
actions are decided in that ring before being transported to the complex matrices by an
entrywise ring homomorphism. This file records word evaluation, the bond-space product and the
bond-space action over an arbitrary commutative ring, the last two in the bond order of
`finProdFinEquiv` that `MPOTensor.mulTensor` and `MPOTensor.actTensor` use, together with their
compatibility with the entrywise image of `MPSTensor.complexOfRing`, and the normality
certificate that every worked example over such a ring reads off a decided table of words.

## Main definitions

* `MPSTensor.evalWordR`: word evaluation of a tensor over a commutative ring.
* `MPSTensor.mulTensorR`: the bond-space product of two matrix product operator tensors over a
  commutative ring.
* `MPSTensor.actTensorR`: the bond-space action of a matrix product operator tensor over a
  commutative ring on a matrix product state tensor over the same ring.

## Main results

* `MPSTensor.evalWord_complexOfRing`: word evaluation commutes with the entrywise image.
* `MPSTensor.mulTensor_complexOfRing`, `MPSTensor.actTensor_complexOfRing`: the bond-space
  product and action commute with the entrywise image.
* `MPSTensor.mulTensor_smul_complexOfRing`: the bond-space product of two entrywise images each
  rescaled by one complex scalar is the square of that scalar times the entrywise image of the
  bond-space product.
* `MPSTensor.isNBlkInjective_of_complexOfRing_smul_single`,
  `MPSTensor.isNormal_of_complexOfRing_smul_single`, `MPSTensor.isNormal_of_complexOfRing_single`:
  block injectivity and normality from a decided table expressing every matrix unit, scaled by
  one element with nonzero image, as a combination of words of one length.
* `MPSTensor.isNormal_of_complexOfRing_letter_eq_smul_single`: normality of a rescaled tensor
  whose letters realise every matrix unit up to a coefficient with nonzero image.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {R : Type*} [CommRing R] (f : R →+* ℂ) {d D D₁ D₂ : ℕ}

/-! ### Word evaluation -/

/-- Word evaluation of a tensor over a commutative ring, `A^{i₁} ⋯ A^{iₙ}`, matching
`Kraus.evalWord`. -/
def evalWordR (A : Fin d → Matrix (Fin D) (Fin D) R) :
    List (Fin d) → Matrix (Fin D) (Fin D) R
  | [] => 1
  | i :: w => A i * evalWordR A w

/-- Word evaluation commutes with the entrywise image. -/
theorem evalWord_complexOfRing (A : Fin d → Matrix (Fin D) (Fin D) R) (w : List (Fin d)) :
    Kraus.evalWord (fun i => complexOfRing f (A i)) w = complexOfRing f (evalWordR A w) := by
  induction w with
  | nil => rw [Kraus.evalWord, evalWordR, complexOfRing_one]
  | cons i w ih => rw [Kraus.evalWord, evalWordR, ih, complexOfRing_mul]

/-- **Block injectivity from a decided table of scaled matrix units.** If for every matrix unit
`E_{ij}` finitely many words of one length `N` of a tensor over `R` combine, with coefficients in
`R`, to `c • E_{ij}` for one `c` whose image is nonzero, then the words of length `N` of the
complex tensor span the full matrix algebra. -/
theorem isNBlkInjective_of_complexOfRing_smul_single {A : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (AR : Fin d → Matrix (Fin D) (Fin D) R) (hA : ∀ a, A a = complexOfRing f (AR a)) {N : ℕ}
    {κ : Type*} [Fintype κ] (word : Fin D → Fin D → κ → Fin N → Fin d)
    (coeff : Fin D → Fin D → κ → R) {c : R} (hc : f c ≠ 0)
    (h : ∀ i j, ∑ k, coeff i j k • evalWordR AR (List.ofFn (word i j k)) =
      c • Matrix.single i j 1) :
    Kraus.IsNBlkInjective A N := by
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan]
  set T := Submodule.span ℂ
    (Set.range fun w : Fin N → Fin d => Kraus.evalWord A (List.ofFn w)) with hT
  have hA' : A = fun a => complexOfRing f (AR a) := funext hA
  refine T.eq_top_of_forall_single_mem fun i j => ?_
  have h1 := congrArg (complexOfRing f) (h i j)
  rw [complexOfRing_sum, complexOfRing_smul, complexOfRing_single] at h1
  have hmem : ∑ k, complexOfRing f
      (coeff i j k • evalWordR AR (List.ofFn (word i j k))) ∈ T := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [complexOfRing_smul, ← evalWord_complexOfRing, ← hA']
    exact T.smul_mem _ (Submodule.subset_span ⟨word i j k, rfl⟩)
  rw [h1] at hmem
  have h2 := T.smul_mem (f c)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

/-- **Normality from a decided table of scaled matrix units**: the certificate of
`isNBlkInjective_of_complexOfRing_smul_single` at a positive length `N` shows that the complex
tensor is normal at blocking length `N`. -/
theorem isNormal_of_complexOfRing_smul_single {A : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (AR : Fin d → Matrix (Fin D) (Fin D) R) (hA : ∀ a, A a = complexOfRing f (AR a)) {N : ℕ}
    (hN : 0 < N) {κ : Type*} [Fintype κ] (word : Fin D → Fin D → κ → Fin N → Fin d)
    (coeff : Fin D → Fin D → κ → R) {c : R} (hc : f c ≠ 0)
    (h : ∀ i j, ∑ k, coeff i j k • evalWordR AR (List.ofFn (word i j k)) =
      c • Matrix.single i j 1) :
    Kraus.IsNormal A :=
  ⟨N, hN, isNBlkInjective_of_complexOfRing_smul_single f AR hA word coeff hc h⟩

/-- **Normality from a decided table of matrix units**: the unscaled case `c = 1` of
`isNormal_of_complexOfRing_smul_single`. -/
theorem isNormal_of_complexOfRing_single {A : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (AR : Fin d → Matrix (Fin D) (Fin D) R) (hA : ∀ a, A a = complexOfRing f (AR a)) {N : ℕ}
    (hN : 0 < N) {κ : Type*} [Fintype κ] (word : Fin D → Fin D → κ → Fin N → Fin d)
    (coeff : Fin D → Fin D → κ → R)
    (h : ∀ i j, ∑ k, coeff i j k • evalWordR AR (List.ofFn (word i j k)) =
      Matrix.single i j 1) :
    Kraus.IsNormal A :=
  isNormal_of_complexOfRing_smul_single f AR hA hN word coeff (c := 1)
    (by rw [map_one]; exact one_ne_zero) fun i j => (h i j).trans (one_smul _ _).symm

/-- **Normality from letters that are scaled matrix units.** If the letters of a tensor are the
images of matrices over `R` rescaled by one nonzero complex number, and every matrix unit
`E_{xy}` is a multiple, with a coefficient of nonzero image, of one letter, then the letters
span the full matrix algebra and the tensor is normal at blocking length one. -/
theorem isNormal_of_complexOfRing_letter_eq_smul_single {A : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (AR : Fin d → Matrix (Fin D) (Fin D) R) {c : ℂ} (hc : c ≠ 0)
    (hA : ∀ a, A a = c • complexOfRing f (AR a)) (ℓ : Fin D → Fin D → Fin d)
    (w : Fin D → Fin D → R) (hw : ∀ x y, f (w x y) ≠ 0)
    (h : ∀ x y, AR (ℓ x y) = w x y • Matrix.single x y 1) :
    Kraus.IsNormal A := by
  refine Kraus.IsInjective.isNormal
    (Submodule.eq_top_of_forall_single_mem _ fun x y => ?_)
  have hAl : A (ℓ x y) = (c * f (w x y)) • Matrix.single x y (1 : ℂ) := by
    rw [hA, h x y, complexOfRing_smul, complexOfRing_single, smul_smul]
  have hmul := Submodule.smul_mem (Submodule.span ℂ (Set.range A)) (c * f (w x y))⁻¹
    (Submodule.subset_span (Set.mem_range_self (ℓ x y)))
  rwa [hAl, smul_smul, inv_mul_cancel₀ (mul_ne_zero hc (hw x y)), one_smul] at hmul

/-! ### Bond-space products and actions -/

/-- The bond-space product of two tensors over a commutative ring,
`(M · N)^{ik} = ∑_j M^{ij} ⊗ N^{jk}`, in the bond order of `finProdFinEquiv`, matching
`MPOTensor.mulTensor`. -/
def mulTensorR (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (i k : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) R :=
  (∑ j : Fin d, (M i j) ⊗ₖ (N j k)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The bond-space action of a matrix product operator tensor over a commutative ring on a
matrix product state tensor over the same ring, `(M · A)^i = ∑_j M^{ij} ⊗ A^j`, in the bond
order of `finProdFinEquiv`, matching `MPOTensor.actTensor`. -/
def actTensorR (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (A : Fin d → Matrix (Fin D₂) (Fin D₂) R) (i : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) R :=
  (∑ j : Fin d, (M i j) ⊗ₖ (A j)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The bond-space product of two tensors rescaled by one complex scalar is the entrywise image
of their bond-space product, rescaled by the square of that scalar. -/
theorem mulTensor_smul_complexOfRing (c : ℂ)
    (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (i k : Fin d) :
    MPOTensor.mulTensor (fun i j => c • complexOfRing f (M i j))
        (fun i j => c • complexOfRing f (N i j)) i k =
      (c * c) • complexOfRing f (mulTensorR M N i k) := by
  ext x y
  simp only [MPOTensor.mulTensor_apply, mulTensorR, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kroneckerMap_apply, complexOfRing_apply, smul_eq_mul, map_sum,
    map_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The bond-space product commutes with the entrywise image. -/
theorem mulTensor_complexOfRing (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (i k : Fin d) :
    MPOTensor.mulTensor (fun i j => complexOfRing f (M i j))
        (fun i j => complexOfRing f (N i j)) i k =
      complexOfRing f (mulTensorR M N i k) := by
  simpa using mulTensor_smul_complexOfRing f 1 M N i k

/-- The bond-space action commutes with the entrywise image. -/
theorem actTensor_complexOfRing (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (A : Fin d → Matrix (Fin D₂) (Fin D₂) R) (i : Fin d) :
    MPOTensor.actTensor (fun i j => complexOfRing f (M i j))
        (fun j => complexOfRing f (A j)) i =
      complexOfRing f (actTensorR M A i) := by
  ext x y
  simp only [MPOTensor.actTensor_apply, actTensorR, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, complexOfRing_apply, map_sum, map_mul]

end MPSTensor
