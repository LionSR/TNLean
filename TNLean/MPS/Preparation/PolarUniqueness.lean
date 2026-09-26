/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.TripartiteDecorrelation
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
* `Matrix.polarPos_eq_of_eq_mul`, `Matrix.polarSupport_eq_of_eq_mul`,
  `Matrix.polarIso_eq_of_eq_mul` — uniqueness of the three polar factors.
* `Matrix.conjTranspose_polarIso_mul_self` — `V† M = P`.
* `Matrix.polarPos_eq_of_mul_self_eq`, `Matrix.polarSupport_eq_of_range_eq` — the positive part
  and the support projector are determined by a positive square root of `Mᴴ M` and by its range.
* `Matrix.exists_polarIso_eq_mul` — the partial isometry is `V = M R` for some `R`.
* `Matrix.conjTranspose_polarIso_mul_eq_zero`,
  `Matrix.conjTranspose_polarIso_mul_polarIso_eq_zero` — orthogonality `Mᴴ M' = 0` passes to
  the partial isometries.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and the sentence before it: the
  layers of the tree circuit act "to the same effect" as the polar decomposition of the directly
  blocked tensor. The source asserts this without proof; the uniqueness of the polar
  decomposition proved here is the step that identifies the product of the layers with the
  isometry `V` of the blocked tensor.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- **A partial isometry is fixed by its initial projector**: if `Wᴴ W = E` for an orthogonal
projector `E`, then `W E = W`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors" (the paragraph containing eq. (S7)): `V†V = Π` for `Π` the projector onto the image
of `P`. -/
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

Supplied step for arXiv:2307.01696, eq. (16): the source asserts that the tree layers act "to
the same effect" as blocking; uniqueness of the polar decomposition, which the source does not
state, identifies the positive parts. -/
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
  refine TripartiteDecorrelation.hermitian_idempotent_eq_of_range_eq _ _
    (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M) hE hEE ?_
  simp only [Matrix.toLin'_apply']
  rw [range_polarSupport, polarPos_eq_of_eq_mul hM hQ hW hE hEE hran, hran]

/-- **Uniqueness of the partial isometry of the polar decomposition**: if `M = W Q` with `Q`
positive semidefinite and `Wᴴ W = E` for an orthogonal projector `E` with the same range as
`Q`, then `W = polarIso M`.

Supplied step for arXiv:2307.01696, eq. (16): the source asserts that the tree layers act "to
the same effect" as blocking; uniqueness of the polar decomposition, which the source does not
state, identifies the product of the layers with the isometry `V`. -/
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

/-! ### Consequences for the polar factors -/

/-- The partial isometry of the polar decomposition pulls a matrix back to its positive part:
`V† M = P`. This is `V†V = Π` and `Π P = P` (arXiv:2307.01696, Supplemental Material, "Proof of
Lemma 1 and extension to non-normal tensors") applied to `M = V P`. -/
theorem conjTranspose_polarIso_mul_self (M : Matrix ι κ ℂ) :
    (polarIso M)ᴴ * M = polarPos M := by
  calc (polarIso M)ᴴ * M = (polarIso M)ᴴ * (polarIso M * polarPos M) := by
        rw [polarIso_mul_polarPos]
    _ = polarPos M := by
        rw [← Matrix.mul_assoc, conjTranspose_polarIso_mul_polarIso, polarSupport_mul_polarPos]

/-- The positive part of the polar decomposition is the positive semidefinite square root of
`Mᴴ M`: any positive semidefinite `Q` with `Q Q = Mᴴ M` is `polarPos M`. -/
theorem polarPos_eq_of_mul_self_eq {M : Matrix ι κ ℂ} {Q : Matrix κ κ ℂ} (hQ : Q.PosSemidef)
    (h : Q * Q = Mᴴ * M) : polarPos M = Q := by
  rw [polarPos, ← h]
  exact CFC.sqrt_mul_self Q (nonneg_iff_posSemidef.mpr hQ)

omit [Fintype ι] [DecidableEq κ] in
/-- Two square matrices with `E Q = Q` and `Q R = E` have the same range. -/
theorem range_mulVecLin_eq_of_mul_eq {E Q R : Matrix κ κ ℂ} (h₁ : E * Q = Q) (h₂ : Q * R = E) :
    LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨R *ᵥ v, by simp [mulVec_mulVec, h₂]⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨Q *ᵥ v, by simp [mulVec_mulVec, h₁]⟩

/-- The support projector of the polar decomposition is the orthogonal projector onto the range
of the positive part: any Hermitian idempotent `E` with that range is `polarSupport M`. -/
theorem polarSupport_eq_of_range_eq {M : Matrix ι κ ℂ} {E : Matrix κ κ ℂ} (hE : E.IsHermitian)
    (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range (polarPos M).mulVecLin) :
    polarSupport M = E := by
  refine TripartiteDecorrelation.hermitian_idempotent_eq_of_range_eq _ _
    (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M) hE hEE ?_
  simp only [Matrix.toLin'_apply']
  rw [range_polarSupport, hran]

section Orthogonal

omit [Fintype κ] [DecidableEq κ] in
/-- If the range of `X` lies in the range of `Y`, then `X = Y R` for some `R`. -/
theorem exists_mul_eq_of_range_le {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']
    {X : Matrix κ ρ' ℂ} {Y : Matrix κ ρ ℂ}
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range Y.mulVecLin) :
    ∃ R : Matrix ρ ρ' ℂ, Y * R = X := by
  classical
  choose u hu using fun c : ρ' => h ⟨Pi.single c 1, rfl⟩
  refine ⟨of fun a c => u c a, ?_⟩
  ext a c
  have h1 := congrFun (hu c) a
  simp only [mulVecLin_apply, mulVec, dotProduct] at h1
  rw [mul_apply]
  simpa [Pi.single_apply] using h1

/-- The positive part has a right factor onto the support projector: `P R = Π` for some `R`. -/
theorem exists_polarPos_mul_eq_polarSupport (M : Matrix ι κ ℂ) :
    ∃ R : Matrix κ κ ℂ, polarPos M * R = polarSupport M :=
  exists_mul_eq_of_range_le (range_polarSupport M).le

/-- The partial isometry of the polar decomposition factors through the matrix: `V = M R` for
some `R` (arXiv:2307.01696, Supplemental Material, the polar decomposition `B = V P` with
`V†V = Π`). -/
theorem exists_polarIso_eq_mul (M : Matrix ι κ ℂ) : ∃ R : Matrix κ κ ℂ, polarIso M = M * R := by
  obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport M
  refine ⟨R, ?_⟩
  have hV : polarIso M * polarSupport M = polarIso M :=
    mul_eq_self_of_conjTranspose_mul_self_eq (conjTranspose_polarIso_mul_polarIso M)
      (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M)
  rw [← hV, ← hR, ← Matrix.mul_assoc, polarIso_mul_polarPos]

variable {κ' : Type*} [Fintype κ'] [DecidableEq κ']

omit [Fintype κ'] [DecidableEq κ'] in
/-- If `Mᴴ M' = 0`, then `Vᴴ M' = 0` for the partial isometry `V` of `M`. -/
theorem conjTranspose_polarIso_mul_eq_zero {M : Matrix ι κ ℂ} {M' : Matrix ι κ' ℂ}
    (h : Mᴴ * M' = 0) : (polarIso M)ᴴ * M' = 0 := by
  obtain ⟨R, hR⟩ := exists_polarIso_eq_mul M
  rw [hR, conjTranspose_mul, Matrix.mul_assoc, h, Matrix.mul_zero]

/-- If `Mᴴ M' = 0`, the partial isometries of `M` and `M'` have orthogonal ranges:
`Vᴴ V' = 0`. -/
theorem conjTranspose_polarIso_mul_polarIso_eq_zero {M : Matrix ι κ ℂ} {M' : Matrix ι κ' ℂ}
    (h : Mᴴ * M' = 0) : (polarIso M)ᴴ * polarIso M' = 0 := by
  obtain ⟨R', hR'⟩ := exists_polarIso_eq_mul M'
  rw [hR', ← Matrix.mul_assoc, conjTranspose_polarIso_mul_eq_zero h, Matrix.zero_mul]

end Orthogonal

end Matrix
