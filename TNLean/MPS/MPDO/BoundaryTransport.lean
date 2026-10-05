/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ActionTensor
import TNLean.MPS.MPDO.Boundary

/-!
# Arbitrary boundaries and exact local decompositions

For arbitrary boundary matrices, stacking operators or acting on a state stacks
those boundaries by a Kronecker product. An exact local decomposition
\(B^i=\sum_c W_c A_c^i V_c\), with \(V_cW_b=\delta_{cb}1\), then transports
an arbitrary boundary \(X\) to the boundaries \(V_c X W_c\), independently of
the positive chain length.

These are the boundary calculations in Garre-Rubio--Lootens--Molnár,
arXiv:2203.12563v3, equations `algcond`, `fusiontensors`, `eq:compatible`,
`fusiontensors2`, and Appendix A. The hypotheses below are exact letter
identities. A reduction with a nilpotent remainder, or equality of periodic
traces, does not provide them.

The word decomposition is asserted only for nonempty words. Its empty-word
extension needs the additional identity \(\sum_c W_c V_c=1\); biorthogonality
alone does not give this identity on the ambient bond space.

## Main statements

* `MPOTensor.mpoWithBoundary_mulTensor`: arbitrary-boundary operator multiplication.
* `MPOTensor.mpvWithBoundary_actTensor`: arbitrary-boundary operator action.
* `MPSTensor.IsBiorthogonalDecomposition.mpvWithBoundary`: length-independent transport.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, source lines 321--391,
  431--490, and Appendix A, lines 2305 onwards.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D₁ D₂ : ℕ}

/-- The boundary of a stacked operator or an operator acting on a state, in the
bond coordinates of `mulTensor` and `actTensor`.
Source: GLM23, arXiv:2203.12563v3, `algcond` and `eq:compatible`. -/
noncomputable def productBoundary (X : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Y : Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) ℂ :=
  (X ⊗ₖ Y).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Product boundaries made from matrix units are matrix units in the stacked
bond coordinates. -/
@[simp] theorem productBoundary_single (i j : Fin D₁) (k l : Fin D₂) (a b : ℂ) :
    productBoundary (Matrix.single i j a) (Matrix.single k l b) =
      Matrix.single (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) (a * b) := by
  simp [productBoundary, Matrix.single_kronecker_single, Matrix.submatrix_single_equiv]

/-- Product boundaries separate matrices on the stacked bond space. This is
the nondegenerate trace-pairing step used in GLM23 Appendix A, `decompopen`. -/
theorem eq_iff_trace_productBoundary {F G : Matrix (Fin (D₁ * D₂))
    (Fin (D₁ * D₂)) ℂ} :
    F = G ↔ ∀ (X : Matrix (Fin D₁) (Fin D₁) ℂ)
      (Y : Matrix (Fin D₂) (Fin D₂) ℂ),
      Matrix.trace (productBoundary X Y * F) =
        Matrix.trace (productBoundary X Y * G) := by
  constructor
  · rintro rfl X Y
    rfl
  · intro h
    ext i j
    obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
    simpa [Matrix.trace_single_mul] using
      h (Matrix.single j₁ i₁ 1) (Matrix.single j₂ i₂ 1)

/-- Stacking arbitrary-boundary MPOs multiplies their operators. This holds
also at length zero and requires no commutation of either boundary with the
letters. Source: GLM23, arXiv:2203.12563v3, `algcond`, lines 321--330. -/
theorem mpoWithBoundary_mulTensor (M : MPOTensor d D₁) (N : MPOTensor d D₂)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) (Y : Matrix (Fin D₂) (Fin D₂) ℂ) (L : ℕ) :
    mpoWithBoundary (mulTensor M N) (productBoundary X Y) L =
      mpoWithBoundary M X L * mpoWithBoundary N Y L := by
  ext σ τ
  rw [Matrix.mul_apply]
  simp only [mpoWithBoundary, productBoundary]
  rw [evalWord_mulTensor, Matrix.submatrix_mul_equiv,
    Matrix.trace_submatrix_equiv, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

/-- Acting with an arbitrary-boundary MPO on an arbitrary-boundary MPS stacks
their boundaries. Source: GLM23, arXiv:2203.12563v3, `eq:compatible`,
lines 431--469. -/
theorem mpvWithBoundary_actTensor (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) (Y : Matrix (Fin D₂) (Fin D₂) ℂ)
    {L : ℕ} (σ : Fin L → Fin d) :
    MPSTensor.mpvWithBoundary (actTensor T A) (productBoundary X Y) σ =
      ∑ τ : Fin L → Fin d,
        mpoWithBoundary T X L σ τ * MPSTensor.mpvWithBoundary A Y τ := by
  simp only [MPSTensor.mpvWithBoundary, mpoWithBoundary, productBoundary]
  rw [evalWord_actTensor, Matrix.submatrix_mul_equiv,
    Matrix.trace_submatrix_equiv, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

/-- The arbitrary-boundary action formula as a matrix-vector equality.
Source: GLM23, arXiv:2203.12563v3, `eq:compatible`. -/
theorem mpoWithBoundary_mulVec_mpvWithBoundary (T : MPOTensor d D₁)
    (A : MPSTensor d D₂) (X : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Y : Matrix (Fin D₂) (Fin D₂) ℂ) (L : ℕ) :
    mpoWithBoundary T X L *ᵥ MPSTensor.mpvWithBoundary A Y =
      MPSTensor.mpvWithBoundary (actTensor T A) (productBoundary X Y) := by
  funext σ
  rw [mpvWithBoundary_actTensor]
  rfl

end MPOTensor

namespace MPSTensor

variable {ι : Type*} [Fintype ι] {d D : ℕ} {δ : ι → ℕ}

/-- An exact decomposition of the letters into blocks with biorthogonal
analysis and synthesis matrices. The index may include both a block label
and its multiplicity index. There is no ambient completeness assumption.

Source: GLM23, arXiv:2203.12563v3, `fusiontensors`, `eq:orthoW`,
`fusiontensors2`, and `eq:orthoV`, lines 364--391 and 462--490. -/
structure IsBiorthogonalDecomposition (B : MPSTensor d D)
    (A : ∀ c : ι, MPSTensor d (δ c))
    (V : ∀ c : ι, Matrix (Fin (δ c)) (Fin D) ℂ)
    (W : ∀ c : ι, Matrix (Fin D) (Fin (δ c)) ℂ) : Prop where
  /-- Analysis is a left inverse on each summand.
  Source: GLM23, `eq:orthoW` and `eq:orthoV`. -/
  retract : ∀ c : ι, V c * W c = 1
  /-- Analysis annihilates the other summands.
  Source: GLM23, `eq:orthoW` and `eq:orthoV`. -/
  orthogonal : ∀ c b : ι, c ≠ b → V c * W b = 0
  /-- Exact reconstruction of a single letter.
  Source: GLM23, `fusiontensors` and `fusiontensors2`. -/
  letter : ∀ i : Fin d, B i = ∑ c : ι, W c * A c i * V c

namespace IsBiorthogonalDecomposition

variable {B : MPSTensor d D} {A : ∀ c : ι, MPSTensor d (δ c)}
  {V : ∀ c : ι, Matrix (Fin (δ c)) (Fin D) ℂ}
  {W : ∀ c : ι, Matrix (Fin D) (Fin (δ c)) ℂ}
  (h : IsBiorthogonalDecomposition B A V W)

include h

/-- Biorthogonality cancels unequal intermediate summands in a product. -/
theorem sum_mul_sum (F G : ∀ c : ι, Matrix (Fin (δ c)) (Fin (δ c)) ℂ) :
    (∑ c : ι, W c * F c * V c) * (∑ c : ι, W c * G c * V c) =
      ∑ c : ι, W c * (F c * G c) * V c := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_eq_single c]
  · calc
      (W c * F c * V c) * (W c * G c * V c) =
          W c * F c * (V c * W c) * G c * V c := by simp [Matrix.mul_assoc]
      _ = W c * (F c * G c) * V c := by rw [h.retract]; simp [Matrix.mul_assoc]
  · intro b _ hbc
    calc
      (W c * F c * V c) * (W b * G b * V b) =
          W c * F c * (V c * W b) * G b * V b := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [h.orthogonal c b (Ne.symm hbc)]; simp
  · simp

/-- Exact local reconstruction extends to every nonempty word, without a
nilpotency threshold. Source: GLM23, arXiv:2203.12563v3, Appendix A,
`decompopen`, together with `eq:orthoW` or `eq:orthoV`. -/
theorem evalWord (w : List (Fin d)) (hw : w ≠ []) :
    Kraus.evalWord B w = ∑ c : ι, W c * Kraus.evalWord (A c) w * V c := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons i w ih =>
    cases w with
    | nil => simpa using h.letter i
    | cons j w =>
      rw [Kraus.evalWord_cons, h.letter i, ih (by simp), h.sum_mul_sum]
      rfl

/-- Empty-word transport requires the synthesis-analysis sum to be the
identity on the ambient bond space. -/
theorem evalWord_of_complete (hcomplete : ∑ c : ι, W c * V c = 1)
    (w : List (Fin d)) :
    Kraus.evalWord B w = ∑ c : ι, W c * Kraus.evalWord (A c) w * V c := by
  by_cases hw : w = []
  · subst w
    simpa using hcomplete.symm
  · exact h.evalWord w hw

/-- Cyclicity of trace transports the arbitrary boundary to each block.
The transported boundaries \(V_c X W_c\) do not depend on the word length.
Source: GLM23, arXiv:2203.12563v3, Appendix A, lines 2307--2315. -/
theorem trace_mul_evalWord (X : Matrix (Fin D) (Fin D) ℂ)
    (w : List (Fin d)) (hw : w ≠ []) :
    Matrix.trace (X * Kraus.evalWord B w) =
      ∑ c : ι, Matrix.trace ((V c * X * W c) * Kraus.evalWord (A c) w) := by
  rw [h.evalWord w hw, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  calc
    Matrix.trace (X * (W c * Kraus.evalWord (A c) w * V c)) =
        Matrix.trace ((X * W c * Kraus.evalWord (A c) w) * V c) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (V c * (X * W c * Kraus.evalWord (A c) w)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((V c * X * W c) * Kraus.evalWord (A c) w) := by
      simp only [Matrix.mul_assoc]

/-- Exact local decomposition transports every boundary at every positive
length. Source: GLM23, arXiv:2203.12563v3, `eq:compatible` and Appendix A. -/
theorem mpvWithBoundary (X : Matrix (Fin D) (Fin D) ℂ) {L : ℕ} (hL : 0 < L)
    (σ : Fin L → Fin d) :
    MPSTensor.mpvWithBoundary B X σ =
      ∑ c : ι, MPSTensor.mpvWithBoundary (A c) (V c * X * W c) σ := by
  exact h.trace_mul_evalWord X (List.ofFn σ)
    (by rw [Ne, List.ofFn_eq_nil_iff]; omega)

end IsBiorthogonalDecomposition

end MPSTensor
