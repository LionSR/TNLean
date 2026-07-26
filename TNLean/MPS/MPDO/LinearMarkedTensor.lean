/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.HorizontalBNT
import TNLean.MPS.MPDO.RepresentativeGroupedMarkedLemmaL

/-!
# Marked tensors in the span of the physical letters

A family of scalar coefficients on the physical alphabet gives a marked
letter by taking the corresponding linear combination of the local tensor
matrices.  Such marked letters commute with weighted direct sums and are
covariant under a common virtual similarity.

For a tensor in literal horizontal canonical form, equality of every closed
chain with one such marked letter implies equality of the marked tensors.
The proof passes to the representative-indexed sector decomposition, applies
representative-grouped marked separation, and returns through the literal
block-diagonal gauge.

The restriction to the physical-letter span is essential: closed chains do
not detect arbitrary off-diagonal matrices between repeated sectors.

## Main results

* `linearMarkedTensor`: a marked tensor formed from linear combinations of
  the physical letters.
* `SectorDecomposition.linearMarkedTensor_toTensor_eq_markedTensor`: linear
  marking commutes with the representative-grouped weighted direct sum.
* `linearMarkedTensor_gauge`: linear marking is covariant under a common
  virtual similarity.
* `MPOTensor.IsHorizontalCF.linearMarkedTensor_eq_of_trace_agree`: closed
  marked-chain equality separates physical-letter marks in normalized
  BNT-refined horizontal form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.3, Lemma L, lines 1835--1858, and Proposition 4.13,
  lines 1909--1919.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d e D : ℕ}

/-- The marked tensor obtained by taking prescribed linear combinations of
the physical letters.

For coefficients `f u z`, the marked letter indexed by `u` is
`sum_z f u z • A z`.  This is the class of marks induced by a linear map on
the physical index in arXiv:1606.00608, Appendix C.3, lines 1835--1858. -/
noncomputable def linearMarkedTensor
    (f : Fin e → Fin d → ℂ) (A : MPSTensor d D) : MPSTensor e D :=
  fun u ↦ ∑ z : Fin d, f u z • A z

/-- Linear marking commutes with a weighted block-diagonal direct sum.

This is the direct-sum expansion used for the physical first-site marks in
arXiv:1606.00608, Appendix C.3, lines 1842--1858. -/
theorem linearMarkedTensor_toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (f : Fin e → Fin d → ℂ) (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k)) :
    linearMarkedTensor f (toTensorFromBlocks μ A) =
      toTensorFromBlocks μ (fun k ↦ linearMarkedTensor f (A k)) := by
  classical
  funext u
  change (∑ z, f u z •
      Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k ↦ μ k • A k z)) =
    Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv
      (Matrix.blockDiagonal' fun k ↦ μ k • ∑ z, f u z • A k z)
  simp_rw [← (Matrix.reindexLinearEquiv ℂ ℂ
    finSigmaFinEquiv finSigmaFinEquiv).map_smul]
  rw [← map_sum]
  congr 1
  funext a b
  rw [Matrix.sum_apply]
  simp_rw [Matrix.smul_apply]
  by_cases h : a.1 = b.1
  · simp_rw [Matrix.blockDiagonal'_apply, dif_pos h]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    calc
      ∑ z, f u z * (μ a.1 * A a.1 z a.2 (cast _ b.2)) =
          ∑ z, μ a.1 * (f u z * A a.1 z a.2 (cast _ b.2)) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = μ a.1 * ∑ z, f u z * A a.1 z a.2 (cast _ b.2) :=
        (Finset.mul_sum ..).symm
  · simp_rw [Matrix.blockDiagonal'_apply, dif_neg h]
    simp

namespace SectorDecomposition

/-- Linear marking of the total sector tensor is the weighted direct sum of
the corresponding marks on its minimal representatives.

This is the representative-grouped form of the first-site decomposition in
arXiv:1606.00608, Appendix C.3, lines 1842--1858. -/
theorem linearMarkedTensor_toTensor_eq_markedTensor
    (S : SectorDecomposition d) (f : Fin e → Fin d → ℂ) :
    linearMarkedTensor f S.toTensor =
      S.markedTensor (fun j ↦ linearMarkedTensor f (S.basis j)) := by
  rw [S.toTensor_eq_toTensorFromBlocks_flat,
    linearMarkedTensor_toTensorFromBlocks]
  rfl

end SectorDecomposition

/-- Linear marking is covariant under a common virtual similarity.

This is the virtual-gauge transport of the physical first-site mark used in
arXiv:1606.00608, Proposition 4.13, lines 1909--1919. -/
theorem linearMarkedTensor_gauge {A B : MPSTensor d D}
    (f : Fin e → Fin d → ℂ) (X : GL (Fin D) ℂ)
    (hX : ∀ z : Fin d,
      B z = (X : Matrix (Fin D) (Fin D) ℂ) * A z *
        (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ u : Fin e,
      linearMarkedTensor f B u =
        (X : Matrix (Fin D) (Fin D) ℂ) * linearMarkedTensor f A u *
          (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  intro u
  simp only [linearMarkedTensor]
  simp_rw [hX]
  calc
    ∑ z, f u z • ((X : Matrix (Fin D) (Fin D) ℂ) * A z *
        (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
        (X : Matrix (Fin D) (Fin D) ℂ) * (∑ z, f u z • A z) *
          (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      simp
    _ = _ := rfl

/-- A common virtual similarity leaves a closed chain with one linear marked
letter unchanged.

This is the gauge-invariant contraction used when the literal block gauge of
the horizontal canonical form is removed in arXiv:1606.00608,
Proposition 4.13, lines 1909--1919. -/
theorem trace_linearMarkedTensor_mul_evalWord_gauge {A B : MPSTensor d D}
    (f : Fin e → Fin d → ℂ) (X : GL (Fin D) ℂ)
    (hX : ∀ z : Fin d,
      B z = (X : Matrix (Fin D) (Fin D) ℂ) * A z *
        (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (u : Fin e) (w : List (Fin d)) :
    Matrix.trace (linearMarkedTensor f B u * evalWord B w) =
      Matrix.trace (linearMarkedTensor f A u * evalWord A w) := by
  rw [linearMarkedTensor_gauge f X hX u, evalWord_gauge X hX]
  rw [show
      ((X : Matrix (Fin D) (Fin D) ℂ) * linearMarkedTensor f A u *
          (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
        ((X : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
        (X : Matrix (Fin D) (Fin D) ℂ) *
          (linearMarkedTensor f A u * evalWord A w) *
          (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) by
    simp [Matrix.mul_assoc]]
  exact trace_conj_eq X _

end MPSTensor

namespace MPOTensor.IsHorizontalCF

variable {d e D : ℕ}

/-- Closed chains with one marked letter separate two physical-letter marks
for a tensor in normalized BNT-refined horizontal form.

For coefficient families `f` and `g`, suppose that replacing the first
physical letter by `sum_z f u z M^z` or by `sum_z g u z M^z` gives equal
closed chains for every marked index, tail word, and tail length.  Then the
two marked tensors are equal.

The proof uses only marks in the span of the physical letters.  Arbitrary
bond-space marks would give a false statement because closed chains cannot
detect off-diagonal matrices between repeated sectors.

This is the physical-insertion scope of Lemma L in arXiv:1606.00608,
Appendix C.3, lines 1835--1858, under the stronger `IsHorizontalCF` hypothesis.
It does not provide the retained-coordinate separation from literal CPSV
canonical form needed by Proposition 4.13; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`. -/
theorem linearMarkedTensor_eq_of_trace_agree
    (M : MPOTensor d D) (hHorizontal : M.IsHorizontalCF)
    (f g : Fin e → Fin (d * d) → ℂ)
    (hTrace : ∀ (L : ℕ) (u : Fin e) (w : Fin L → Fin (d * d)),
      Matrix.trace
          (MPSTensor.linearMarkedTensor f M.toMPSTensor u *
            MPSTensor.evalWord M.toMPSTensor (List.ofFn w)) =
        Matrix.trace
          (MPSTensor.linearMarkedTensor g M.toMPSTensor u *
            MPSTensor.evalWord M.toMPSTensor (List.ofFn w))) :
    MPSTensor.linearMarkedTensor f M.toMPSTensor =
      MPSTensor.linearMarkedTensor g M.toMPSTensor := by
  classical
  obtain ⟨S, hCF, hTotal, Xcopy, hX⟩ := hHorizontal
  subst D
  let X := MPSTensor.globalGaugeOfBlocks Xcopy
  have hX' : ∀ z : Fin (d * d), M.toMPSTensor z =
      (X : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor z *
        (((X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    intro z
    simpa using hX z
  have hRepresentative : ∀ j : Fin S.basisCount,
      MPSTensor.linearMarkedTensor f (S.basis j) =
        MPSTensor.linearMarkedTensor g (S.basis j) := by
    apply hCF.markedTensor_basis_eq_of_trace_agree
    intro L u w
    rw [← S.linearMarkedTensor_toTensor_eq_markedTensor f,
      ← S.linearMarkedTensor_toTensor_eq_markedTensor g]
    have hf := MPSTensor.trace_linearMarkedTensor_mul_evalWord_gauge
      f X hX' u (List.ofFn w)
    have hg := MPSTensor.trace_linearMarkedTensor_mul_evalWord_gauge
      g X hX' u (List.ofFn w)
    exact hf.symm.trans ((hTrace L u w).trans hg)
  have hSector : MPSTensor.linearMarkedTensor f S.toTensor =
      MPSTensor.linearMarkedTensor g S.toTensor := by
    rw [S.linearMarkedTensor_toTensor_eq_markedTensor,
      S.linearMarkedTensor_toTensor_eq_markedTensor]
    congr 1
    funext j
    exact hRepresentative j
  funext u
  rw [MPSTensor.linearMarkedTensor_gauge f X hX' u,
    MPSTensor.linearMarkedTensor_gauge g X hX' u, hSector]

end MPOTensor.IsHorizontalCF
