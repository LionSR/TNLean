/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MatrixPolar

/-!
# Uniqueness of the polar decomposition

The polar decomposition `M = V P` of `Matrix.polarIso` and `Matrix.polarPos` is unique in the
following sense: if `M = W Q` with `Q` positive semidefinite and `Wᴴ W = E`, where `E` is an
orthogonal projector with the same range as `Q`, then `Q = polarPos M`, `E = polarSupport M`,
and `W = polarIso M`.  The log-depth preparation of matrix product states uses this to identify
the product of the layers of its tree circuit with the isometry of the blocked tensor.

## Main declarations

* `Matrix.mul_eq_self_of_conjTranspose_mul_self_eq` — a partial isometry is fixed by its
  initial projector: `Wᴴ W = E` gives `W E = W`.
* `Matrix.eq_of_range_eq_of_isHermitian_idempotent` — two orthogonal projectors with the same
  range are equal.
* `Matrix.polarPos_eq_of_eq_mul`, `Matrix.polarSupport_eq_of_eq_mul`,
  `Matrix.polarIso_eq_of_eq_mul` — uniqueness of the three polar factors.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), text after eq. (16): the product of the tree
  layers is a partial isometry, so "by uniqueness of the polar decomposition" it is the
  isometry `V` of the blocked tensor.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- **A partial isometry is fixed by its initial projector**: if `Wᴴ W = E` for an orthogonal
projector `E`, then `W E = W`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `V†V = Π` for the projector `Π` onto the initial space of `V`. -/
theorem mul_eq_self_of_conjTranspose_mul_self_eq {W : Matrix ι κ ℂ} {E : Matrix κ κ ℂ}
    (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E) : W * E = W := by
  have h : (W * E - W)ᴴ * (W * E - W) = 0 := by
    have hexp : (W * E - W)ᴴ * (W * E - W) =
        E * (Wᴴ * W) * E - E * (Wᴴ * W) - (Wᴴ * W) * E + Wᴴ * W := by
      rw [conjTranspose_sub, conjTranspose_mul, hE.eq]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [hexp, hW, hEE, hEE, sub_self, zero_sub, neg_add_cancel]
  exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp h)

omit [Fintype ι] [DecidableEq κ] in
/-- An idempotent `E` fixes every matrix `Q` whose range lies in the range of `E`. -/
theorem mul_eq_self_of_range_le {ρ : Type*} {E : Matrix κ κ ℂ} {Q : Matrix κ ρ ℂ}
    [Fintype ρ] (hEE : E * E = E)
    (hran : LinearMap.range Q.mulVecLin ≤ LinearMap.range E.mulVecLin) : E * Q = Q := by
  refine ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨u, hu⟩ := hran ⟨v, rfl⟩
  change E *ᵥ u = Q *ᵥ v at hu
  rw [← mulVec_mulVec, ← hu, mulVec_mulVec, hEE]

omit [Fintype ι] [DecidableEq κ] in
/-- If `Y Q = 0` and the range of `E` lies in the range of `Q`, then `Y E = 0`. -/
theorem mul_eq_zero_of_mul_eq_zero_of_range_le {ρ : Type*} [Fintype ρ] {Y : Matrix ι κ ℂ}
    {E : Matrix κ κ ℂ} {Q : Matrix κ ρ ℂ} (hY : Y * Q = 0)
    (hran : LinearMap.range E.mulVecLin ≤ LinearMap.range Q.mulVecLin) : Y * E = 0 := by
  refine ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨u, hu⟩ := hran ⟨v, rfl⟩
  change Q *ᵥ u = E *ᵥ v at hu
  rw [← mulVec_mulVec, ← hu, mulVec_mulVec, hY, zero_mulVec, zero_mulVec]

omit [DecidableEq κ] in
/-- **Two orthogonal projectors with the same range are equal.** -/
theorem eq_of_range_eq_of_isHermitian_idempotent {E F : Matrix κ κ ℂ} (hE : E.IsHermitian)
    (hEE : E * E = E) (hF : F.IsHermitian) (hFF : F * F = F)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range F.mulVecLin) : E = F := by
  have hFE : F * E = E := mul_eq_self_of_range_le hFF hran.le
  have hEF : E * F = F := mul_eq_self_of_range_le hEE hran.ge
  calc E = Eᴴ := hE.eq.symm
    _ = (F * E)ᴴ := by rw [hFE]
    _ = E * F := by rw [conjTranspose_mul, hE.eq, hF.eq]
    _ = F := hEF

omit [DecidableEq κ] in
/-- The Gram matrix of a product `W Q` with `Wᴴ W = E`, `E Q = Q`, and `Q` Hermitian is
`Q Q`. -/
private lemma gram_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.IsHermitian) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEQ : E * Q = Q) :
    Mᴴ * M = Q * Q := by
  have hQE : Q * E = Q := by
    rw [← hQ.eq, ← hE.eq, ← conjTranspose_mul, hEQ]
  rw [hM, conjTranspose_mul, hQ.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW,
    ← Matrix.mul_assoc, hQE]

/-- **Uniqueness of the positive part of the polar decomposition**: if `M = W Q` with `Q`
positive semidefinite and `Wᴴ W = E` for an orthogonal projector `E` with the same range as
`Q`, then `Q = polarPos M`.

arXiv:2307.01696, text after eq. (16): "by uniqueness of the polar decomposition". -/
theorem polarPos_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.PosSemidef) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin) :
    polarPos M = Q := by
  have hEQ : E * Q = Q := mul_eq_self_of_range_le hEE hran.ge
  rw [polarPos, gram_eq_of_eq_mul hM hQ.isHermitian hW hE hEQ]
  exact CFC.sqrt_mul_self Q (nonneg_iff_posSemidef.mpr hQ)

/-- **Uniqueness of the support projector of the polar decomposition**: under the hypotheses of
`Matrix.polarPos_eq_of_eq_mul`, `E = polarSupport M`. -/
theorem polarSupport_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.PosSemidef) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin) :
    polarSupport M = E := by
  refine eq_of_range_eq_of_isHermitian_idempotent (isHermitian_polarSupport M)
    (polarSupport_mul_polarSupport M) hE hEE ?_
  rw [range_polarSupport, polarPos_eq_of_eq_mul hM hQ hW hE hEE hran, hran]

/-- **Uniqueness of the partial isometry of the polar decomposition**: if `M = W Q` with `Q`
positive semidefinite and `Wᴴ W = E` for an orthogonal projector `E` with the same range as
`Q`, then `W = polarIso M`.

arXiv:2307.01696, text after eq. (16): the product of the tree layers "is a partial isometry
[...], so by uniqueness of the polar decomposition it equals `V`". -/
theorem polarIso_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.PosSemidef) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin) :
    polarIso M = W := by
  have hPos := polarPos_eq_of_eq_mul hM hQ hW hE hEE hran
  have hSupp := polarSupport_eq_of_eq_mul hM hQ hW hE hEE hran
  have hV : polarIso M * E = polarIso M := by
    rw [← hSupp]
    exact mul_eq_self_of_conjTranspose_mul_self_eq (conjTranspose_polarIso_mul_polarIso M)
      (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M)
  have hWE : W * E = W := mul_eq_self_of_conjTranspose_mul_self_eq hW hE hEE
  have hdiff : (polarIso M - W) * Q = 0 := by
    rw [Matrix.sub_mul, ← hPos, polarIso_mul_polarPos, hPos, ← hM, sub_self]
  have hdiffE := mul_eq_zero_of_mul_eq_zero_of_range_le hdiff hran.le
  rw [Matrix.sub_mul, hV, hWE, sub_eq_zero] at hdiffE
  exact hdiffE

end Matrix
