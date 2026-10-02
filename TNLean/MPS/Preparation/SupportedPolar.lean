/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.MPS.Preparation.PolarUniqueness

/-!
# Polar decomposition of a tensor injective on a set of bond pairs

A tensor `B : MPSTensor n D` is *injective on* a set `S` of pairs of bond indices
(`MPSTensor.IsInjectiveOn`) if its matrices vanish outside the entries `S` and span all matrices
supported on `S`. For `S` the rectangle `[0, a) × [0, b)` this may be read as injectivity, in
the sense of the span of its matrices, of a tensor with bond dimensions `a` and `b` padded with
zeros to `D × D` matrices; no rectangular tensor is defined here, and that reading is not proved.

For such a tensor the polar decomposition `B = V P` has support projector `Π`, `V†V = Π`, equal
to the coordinate projector onto `S` (`MPSTensor.polarSupportMatrix_eq_diagonal`): the isometric
factor `V` is an isometry on the inputs `S` and vanishes on the others. In arXiv:2307.01696,
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors", the isometry
satisfies `V†V = Π` with `Π` the projector onto the image of `P`; under injectivity on `S` this
`Π` is the coordinate projector onto `S`.

## Main results

* `Matrix.polarSupport_eq_diagonal_of_support` — the support projector of a matrix whose columns
  vanish outside `S` and which is injective on vectors supported on `S` is the coordinate
  projector onto `S`.
* `MPSTensor.polarSupportMatrix_eq_diagonal` — the same for a tensor injective on `S`.
* `MPSTensor.sum_star_polarIsoMatrix_mul` — the columns of `V` are orthonormal on `S` and vanish
  outside.
* `MPSTensor.polarPosTensor_eq_zero` — the positive part has no component outside `S`.
* `MPSTensor.exists_polarIsoMatrix_eq_sum` — `V = B G` for some matrix `G` on the bond pairs.

## References

* arXiv:2307.01696, paragraph "Approximation through the fixed-point state" (the polar
  decomposition `B = V P`) and Supplemental Material, "Proof of Lemma 1 and extension to
  non-normal tensors" (`V†V = Π`).
-/

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **The support projector of a matrix supported on a set of columns.** If the columns of `M`
outside `S` vanish and `M` is injective on the vectors supported on `S`, then the support
projector `Π` of the polar decomposition of `M` is the coordinate projector onto `S`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors":
`V†V = Π` with `Π` the projector onto the range of `P`. -/
theorem polarSupport_eq_diagonal_of_support {M : Matrix ι κ ℂ} {S : Set κ}
    [DecidablePred (· ∈ S)] (h0 : ∀ i p, p ∉ S → M i p = 0)
    (hinj : ∀ x : κ → ℂ, (∀ p, p ∉ S → x p = 0) → M *ᵥ x = 0 → x = 0) :
    polarSupport M = diagonal fun p => if p ∈ S then 1 else 0 := by
  set E : Matrix κ κ ℂ := diagonal fun p => if p ∈ S then 1 else 0 with hEdef
  have hEh : Eᴴ = E := by
    rw [hEdef, diagonal_conjTranspose]
    congr 1
    funext p
    split_ifs <;> simp_all
  have hME : M * E = M := by
    ext i p
    rw [hEdef, mul_diagonal]
    by_cases hp : p ∈ S
    · simp [hp]
    · simp [hp, h0 i p hp]
  have hPh : (polarPos M)ᴴ = polarPos M := (posSemidef_polarPos M).isHermitian
  have hSh : (polarSupport M)ᴴ = polarSupport M := isHermitian_polarSupport M
  have h1 : M * (1 - E) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hME, sub_self]
  have h2 : polarPos M * (1 - E) = 0 := by
    refine conjTranspose_mul_self_eq_zero.mp ?_
    rw [conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc (polarPos M),
      polarPos_mul_polarPos, Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.mul_zero]
  obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport M
  have h3 : polarSupport M = polarSupport M * E := by
    have h : polarSupport M * (1 - E) = 0 := by
      rw [← hSh, ← hR, conjTranspose_mul, hPh, Matrix.mul_assoc, h2, Matrix.mul_zero]
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  have h4 : E = E * polarSupport M := by
    have hX : M * (E * (1 - polarSupport M)) = 0 := by
      rw [← Matrix.mul_assoc, hME, Matrix.mul_sub, Matrix.mul_one, mul_polarSupport, sub_self]
    have h : E * (1 - polarSupport M) = 0 := by
      ext p c
      have hx := hinj (fun p => (E * (1 - polarSupport M)) p c)
        (fun p hp => by simp [hEdef, diagonal_mul, hp]) (funext fun i => by
          have := congrFun (congrFun hX i) c
          simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
      simpa using congrFun hx p
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  calc polarSupport M = (polarSupport M)ᴴ := hSh.symm
    _ = (polarSupport M * E)ᴴ := by rw [← h3]
    _ = E * polarSupport M := by rw [conjTranspose_mul, hEh, hSh]
    _ = E := h4.symm

end Matrix

namespace MPSTensor

variable {n D : ℕ}

/-- A tensor is **injective on** a set `S` of pairs of bond indices if its matrices vanish
outside the entries `S` and span every matrix unit `|α⟩⟨β|` with `(α, β) ∈ S`. For the rectangle
`S = [0, a) × [0, b)` this may be read as injectivity of `B` viewed as a zero-padded tensor with
bond dimensions `a` and `b`, whose matrices span all `a × b` matrices; that reading is a gloss,
not a statement proved here. For `S` the set of all pairs it is `Kraus.IsInjective`
(`MPSTensor.isInjectiveOn_univ_iff`).

arXiv:2307.01696, footnote to the paragraph "Approximation through the fixed-point state": the
blocked tensors are assumed injective. -/
def IsInjectiveOn (B : MPSTensor n D) (S : Set (Fin D × Fin D)) : Prop :=
  (∀ i p, p ∉ S → B i p.1 p.2 = 0) ∧
    ∀ p ∈ S, Matrix.single p.1 p.2 (1 : ℂ) ∈ Submodule.span ℂ (Set.range B)

/-- Injectivity on all pairs is injectivity. -/
theorem isInjectiveOn_univ_iff {B : MPSTensor n D} :
    IsInjectiveOn B Set.univ ↔ Kraus.IsInjective B := by
  refine ⟨fun h => ?_, fun h => ⟨fun _ _ hp => absurd (Set.mem_univ _) hp,
    fun _ _ => h.span_eq_top ▸ Submodule.mem_top⟩⟩
  exact Submodule.eq_top_of_forall_single_mem _ fun i j => h.2 (i, j) (Set.mem_univ _)

/-- A tensor injective on `S` is injective, as a map `ℂ^{D²} → ℂ^n`, on the vectors supported
on `S`. -/
theorem IsInjectiveOn.eq_zero_of_mulVec_eq_zero {B : MPSTensor n D} {S : Set (Fin D × Fin D)}
    (hB : IsInjectiveOn B S) {x : Fin D × Fin D → ℂ} (hx : ∀ p, p ∉ S → x p = 0)
    (h : (physicalMatrix B).mulVec x = 0) : x = 0 := by
  classical
  let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Y => ∑ p : Fin D × Fin D, Y p.1 p.2 * x p
      map_add' := fun Y Z => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c Y => by simp [mul_assoc, Finset.mul_sum] }
  have hker : Submodule.span ℂ (Set.range B) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := congrFun h i
    simpa [f, Matrix.mulVec, dotProduct, physicalMatrix] using this
  funext p
  by_cases hp : p ∈ S
  · have := hker (hB.2 p hp)
    simpa [f, Matrix.single_apply, ← Prod.ext_iff, Finset.sum_ite_eq] using this
  · exact hx p hp

/-- **The support projector of a tensor injective on `S`** is the coordinate projector onto `S`:
`V†V = Π_S`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors":
`V†V = Π`. -/
theorem polarSupportMatrix_eq_diagonal {B : MPSTensor n D} {S : Set (Fin D × Fin D)}
    [DecidablePred (· ∈ S)] (hB : IsInjectiveOn B S) :
    polarSupportMatrix B = Matrix.diagonal fun x => if virtualPairEquiv D x ∈ S then 1 else 0 := by
  rw [polarSupportMatrix,
    Matrix.polarSupport_eq_diagonal_of_support (M := physicalMatrix B) (S := S)
      (fun i p hp => hB.1 i p hp) (fun x hx h => hB.eq_zero_of_mulVec_eq_zero hx h),
    Matrix.submatrix_diagonal_equiv]
  rfl

/-- **The columns of the isometric factor** of a tensor injective on `S`:
`∑ᵢ (V_{ix})^* V_{iy}` is `1` if `x = y` lies in `S` and `0` otherwise. -/
theorem sum_star_polarIsoMatrix_mul {B : MPSTensor n D} {S : Set (Fin D × Fin D)}
    [DecidablePred (· ∈ S)] (hB : IsInjectiveOn B S) (x y : Fin (D * D)) :
    ∑ i, star (polarIsoMatrix B i x) * polarIsoMatrix B i y =
      if x = y ∧ virtualPairEquiv D x ∈ S then 1 else 0 := by
  have h := congrFun (congrFun (conjTranspose_polarIsoMatrix_mul_polarIsoMatrix B) x) y
  rw [polarSupportMatrix_eq_diagonal hB, Matrix.mul_apply, Matrix.diagonal_apply] at h
  simp only [Matrix.conjTranspose_apply] at h
  rw [h]
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- The positive part of a tensor injective on `S` has no component outside `S`: `P^x = 0` for
the pairs `x ∉ S`, as `Π P = P`. -/
theorem polarPosTensor_eq_zero {B : MPSTensor n D} {S : Set (Fin D × Fin D)}
    (hB : IsInjectiveOn B S) {x : Fin (D * D)} (hx : virtualPairEquiv D x ∉ S) :
    polarPosTensor B x = 0 := by
  classical
  rw [← rotatePhysical_polarSupportMatrix B, rotatePhysical_apply,
    polarSupportMatrix_eq_diagonal hB]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; simp
  · simp

/-- **The isometric factor factors through the tensor**: `V = B G` for some matrix `G` on the
bond pairs, `V_{ix} = ∑ₐ B^i_{a} G_{a x}`, for every tensor.

arXiv:2307.01696, eq. (13), where `G = P⁻¹` for injective `B`; in general `G` is a right factor
of `P` onto the support projector, as in the Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors". -/
theorem exists_polarIsoMatrix_eq_sum (B : MPSTensor n D) :
    ∃ G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ, ∀ i x, polarIsoMatrix B i x =
      ∑ a, B i (virtualPairEquiv D a).1 (virtualPairEquiv D a).2 * G a x := by
  obtain ⟨R, hR⟩ := Matrix.exists_polarIso_eq_mul (physicalMatrix B)
  refine ⟨R.submatrix (virtualPairEquiv D) (virtualPairEquiv D), fun i x => ?_⟩
  rw [polarIsoMatrix, Matrix.submatrix_apply, hR, Matrix.mul_apply,
    ← (virtualPairEquiv D).sum_comp]
  rfl

end MPSTensor
