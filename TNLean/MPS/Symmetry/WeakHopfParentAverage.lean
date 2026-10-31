/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.WeakHopfRepresentation
import TNLean.MPS.Symmetry.BoundaryProjectionAverage

/-!
# The weak-Hopf average of the canonical parent term

Garre-Rubio, Lootens and Molnár symmetrize the canonical parent term of an
MPS under an MPO representation of a C*-weak Hopf algebra by
\[
  E(P)=\sum\rho(\Omega_{(1)})\,P\,\rho(T(\Omega_{(2)})),
\]
where \(\rho\) is the represented coproduct, \(\Omega\) the canonical
integral, and \(T\) the linear map of arXiv:2204.05940v1. They assert that
the average of the support projection \(P\) is Hermitian, has trace
\(\operatorname{tr}(\rho(1)P)\), and is again the projection onto the MPS
support; the key identity is
\(\sum\Delta(\Omega_{(1)})\Delta(T(\Omega_{(2)}))=\Delta(1)\).

Here the average is defined from the comultiplication of the integral, with
no choice of Sweedler decomposition, at every positive chain length `n`.
The weak-Hopf data supply the three ingredients of the boundary average:
adjoint closure of the boundary range, a boundary realizing the unit at one
site, and the normalized boundary family obtained from \(\Delta(\Omega)\).
For an MPS compatible with the MPO in the sense of GLM23 `eq:compatible`,
this gives
\[
  E_n(P_n)=P_n,\qquad E_n(I)=Q_n,\qquad E_n(I-P_n)=Q_n-P_n,
\]
with \(Q_n=\rho_n(1)\). The literal average of the parent term \(I-P_n\) is
therefore \(Q_n-P_n\), while the ambient complement \(I-E_n(P_n)\) is the
original parent term \(I-P_n\); the latter is nonzero when \(d^n>D^2\).

**Scope restriction (one-site injectivity):** the unit-support step uses an
MPS that is injective at one site, where the unital physical representation
gives \(\rho_1(1)=I\). This matches the two-site canonical parent term of
GLM23 Appendix B. Blocked injectivity is covered by
`WeakHopfRepresentation.weakHopfAverage_starProjection_of_rep_eq_one`, which
instead assumes that the represented unit is the identity at the injectivity
length. See `docs/paper-gaps/glm23_wha_parent_completion.tex`.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:compatible`,
  lines 431--469; Section 5, lines 1276--1320; Appendix B, lines 2463--2466.
* Molnár et al., arXiv:2204.05940v1, Section 4 and Section 6.
-/

open scoped Matrix TensorProduct

noncomputable section

namespace MPOTensor.WeakHopfRepresentation

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H] [StarRing H] [StarModule ℂ H]
variable {d D Dₐ L n : ℕ} (W : WeakHopfRepresentation H d D)

/-- The averaging map of GLM23 Appendix B on `n` sites,
\(E_n(P)=\sum\rho_n(\Omega_{(1)})\,P\,\rho_n(T(\Omega_{(2)}))\),
defined from \(\Delta(\Omega)\) itself. Source: arXiv:2203.12563v3,
lines 2463--2466. -/
def weakHopfAverage (n : ℕ)
    (P : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d))) :
    Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d)) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ
      (fun x y ↦ Matrix.toEuclideanLin (W.rep n x) * P *
        Matrix.toEuclideanLin (W.rep n (W.pullThrough y)))
      (fun x x' y ↦ by simp only [map_add, add_mul])
      (fun c x y ↦ by simp only [map_smul, smul_mul_assoc])
      (fun x y y' ↦ by simp only [map_add, mul_add])
      (fun c x y ↦ by simp only [map_smul, mul_smul_comm]))
    (Coalgebra.comul W.integral)

/-- Any Sweedler representation of \(\Delta(\Omega)\) computes the average. -/
theorem weakHopfAverage_eq_sum {ι : Type*} (𝓡 : Coalgebra.Repr ℂ W.integral ι)
    (P : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d))) :
    W.weakHopfAverage n P = ∑ i ∈ 𝓡.index,
      Matrix.toEuclideanLin (W.rep n (𝓡.left i)) * P *
        Matrix.toEuclideanLin (W.rep n (W.pullThrough (𝓡.right i))) := by
  rw [weakHopfAverage, ← 𝓡.eq, map_sum]
  rfl

/-- The average of the identity is the represented unit,
\(E_n(I)=\rho_n(1)=Q_n\), as stated in GLM23 Appendix B. -/
theorem weakHopfAverage_one (hn : 0 < n) :
    W.weakHopfAverage n 1 = Matrix.toEuclideanLin (W.rep n 1) := by
  let 𝓡 := Coalgebra.Repr.arbitrary ℂ W.integral
  rw [W.weakHopfAverage_eq_sum 𝓡, ← W.sum_rep_mul_rep_pullThrough 𝓡 hn, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_one]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rfl

/-- The average is additive in the averaged operator. -/
theorem weakHopfAverage_sub (P P' : Module.End ℂ (EuclideanSpace ℂ (Fin n → Fin d))) :
    W.weakHopfAverage n (P - P') = W.weakHopfAverage n P - W.weakHopfAverage n P' := by
  let 𝓡 := Coalgebra.Repr.arbitrary ℂ W.integral
  simp only [W.weakHopfAverage_eq_sum 𝓡, ← Finset.sum_sub_distrib, mul_sub, sub_mul]

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

/-- The weak-Hopf average fixes the MPS support projection, provided the
represented unit is the identity at an injectivity length `L`.

Adjoint closure of the boundary range and the normalized boundary family
are derived from the weak-Hopf data; this is the projection claim of GLM23
Appendix B, lines 2463--2466, for an MPS compatible with the MPO as in
`eq:compatible`. -/
theorem weakHopfAverage_starProjection_of_rep_eq_one {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) (hU : W.rep L 1 = 1) (hn : 0 < n) :
    W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  let 𝓡 := Coalgebra.Repr.arbitrary ℂ W.integral
  let X : 𝓡.index → Matrix (Fin D) (Fin D) ℂ := fun i ↦ W.boundary (𝓡.left i)
  let Y : 𝓡.index → Matrix (Fin D) (Fin D) ℂ :=
    fun i ↦ W.boundary (W.pullThrough (𝓡.right i))
  have hstar : ∀ Z : Matrix (Fin D) (Fin D) ℂ, ∃ Z' : Matrix (Fin D) (Fin D) ℂ,
      (mpoWithBoundary W.tensor Z n)ᴴ = mpoWithBoundary W.tensor Z' n := by
    intro Z
    obtain ⟨Z', hZ'⟩ := W.exists_conjTranspose_mpoWithBoundary_eq Z
    exact ⟨Z', hZ' n⟩
  have hXY : ∑ i, mpoWithBoundary W.tensor (X i) n * mpoWithBoundary W.tensor (Y i) n =
      mpoWithBoundary W.tensor (W.boundary 1) n := by
    simp only [X, Y, mpoWithBoundary_boundary]
    rw [Finset.sum_coe_sort 𝓡.index
      (fun i ↦ W.rep n (𝓡.left i) * W.rep n (W.pullThrough (𝓡.right i))),
      W.sum_rep_mul_rep_pullThrough 𝓡 hn]
  have hU' : mpoWithBoundary W.tensor (W.boundary 1) L = 1 := by
    rw [mpoWithBoundary_boundary, hU]
  have key := h.sum_mpoWithBoundary_groundSpaceES_starProjection hInj hL hU' hn hstar X Y hXY
  simp only [X, Y, mpoWithBoundary_boundary] at key
  rw [W.weakHopfAverage_eq_sum 𝓡, ← Finset.sum_coe_sort]
  exact key

/-- The weak-Hopf average fixes the MPS support projection of a one-site
injective MPS compatible with the MPO: \(E_n(P_n)=P_n\) at every positive
length. The unit at one site is the identity because the physical
representation is unital.

This is the projection claim of GLM23 Appendix B, lines 2463--2466; the
consequences Hermiticity and \(\operatorname{tr}E_n(P_n)=
\operatorname{tr}(Q_nP_n)\) follow below. -/
theorem weakHopfAverage_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsInjective A) (hn : 0 < n) :
    W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap :=
  W.weakHopfAverage_starProjection_of_rep_eq_one h
    (Kraus.isNBlkInjective_one_of_isInjective hInj) Nat.one_pos W.rep_one_length_one hn

/-- The represented unit fixes the MPS support: \(Q_nP_n=P_n\). -/
theorem toEuclideanLin_rep_one_comp_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsInjective A) (hn : 0 < n) :
    Matrix.toEuclideanLin (W.rep n 1) ∘ₗ
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  have hU : mpoWithBoundary W.tensor (W.boundary 1) 1 = 1 := by
    rw [mpoWithBoundary_boundary, W.rep_one_length_one]
  simpa only [mpoWithBoundary_boundary] using
    h.toEuclideanLin_comp_groundSpaceES_starProjection_of_one_site hInj hU hn

/-- The averaged support projection is Hermitian and has trace
\(\operatorname{tr}(Q_nP_n)\), as asserted in GLM23 Appendix B,
lines 2463--2466. -/
theorem isSymmetricProjection_weakHopfAverage_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsInjective A) (hn : 0 < n) :
    (W.weakHopfAverage n
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap).IsSymmetricProjection ∧
      LinearMap.trace ℂ _ (W.weakHopfAverage n
          (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) =
        LinearMap.trace ℂ _ (Matrix.toEuclideanLin (W.rep n 1) ∘ₗ
          (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) := by
  rw [W.weakHopfAverage_starProjection h hInj hn,
    W.toEuclideanLin_rep_one_comp_starProjection h hInj hn]
  exact ⟨Submodule.isSymmetricProjection_starProjection _, rfl⟩

/-- The literal average of the canonical parent term is
\(E_n(I-P_n)=Q_n-P_n\), which may vanish. Source: arXiv:2203.12563v3,
lines 2463--2466; the distinction from the ambient complement is recorded
in `docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem weakHopfAverage_parentInteractionES {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsInjective A) (hn : 0 < n) :
    W.weakHopfAverage n (MPSTensor.parentInteractionES A n) =
      Matrix.toEuclideanLin (W.rep n 1) -
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  rw [MPSTensor.parentInteractionES, Submodule.starProjection_orthogonal']
  change W.weakHopfAverage n
      (1 - (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) = _
  rw [W.weakHopfAverage_sub, W.weakHopfAverage_one hn,
    W.weakHopfAverage_starProjection h hInj hn]

/-- The ambient complement of the averaged support is the canonical parent
term: \(I-E_n(P_n)=I-P_n\). This is the parent term chosen in GLM23
Appendix B, lines 2463--2466. -/
theorem one_sub_weakHopfAverage_starProjection {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsInjective A) (hn : 0 < n) :
    1 - W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap =
      MPSTensor.parentInteractionES A n := by
  rw [W.weakHopfAverage_starProjection h hInj hn, MPSTensor.parentInteractionES,
    Submodule.starProjection_orthogonal']
  rfl

/-- The symmetrized parent term \(I-E_n(P_n)\) is nonzero when
\(d^n>D^2\), the nonvanishing claim of GLM23 Appendix B, lines 2453--2466,
for the ambient complement. -/
theorem one_sub_weakHopfAverage_starProjection_ne_zero {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsInjective A) (hn : 0 < n)
    (hDim : d ^ n > Dₐ ^ 2) :
    1 - W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap ≠ 0 := by
  rw [W.one_sub_weakHopfAverage_starProjection h hInj hn]
  exact MPSTensor.parentInteractionES_ne_zero A n hDim

/-- The symmetrized parent term commutes with every boundary operator of the
representation, at every positive length. -/
theorem commute_one_sub_weakHopfAverage_mpoWithBoundary {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible W.tensor A) (hInj : Kraus.IsInjective A) (hn : 0 < n)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Commute (1 - W.weakHopfAverage n (MPSTensor.groundSpaceES A n).starProjection.toLinearMap)
      (Matrix.toEuclideanLin (mpoWithBoundary W.tensor X n)) := by
  rw [W.one_sub_weakHopfAverage_starProjection h hInj hn]
  apply h.parentInteractionES_commute_mpoWithBoundary hn ?_ X
  intro Z
  obtain ⟨Z', hZ'⟩ := W.exists_conjTranspose_mpoWithBoundary_eq Z
  exact ⟨Z', hZ' n⟩

end MPOTensor.WeakHopfRepresentation
