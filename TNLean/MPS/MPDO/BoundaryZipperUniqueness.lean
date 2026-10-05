/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundarySourceDecomposition
import TNLean.MPS.Symmetry.MPOSymmetry.ZipperUniqueness

/-!
# Multiplicities and zipper uniqueness for exact boundary decompositions

An exact biorthogonal decomposition gives the existing zipper decomposition
with exactly the same rectangular matrices. Its trace counts the copies of
each target block. A simultaneous positive word span therefore makes those
multiplicities unique, including when the ambient support is proper.

The existing zipper uniqueness theorem then compares decompositions with
the same multiplicities by invertible multiplicity gauges on the letter
support. No unitary gauge or ambient completeness is inferred.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Appendix A and
  the fusion and action gauge freedoms at lines 415--424 and 595--602.
* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 164--166 and 181--200.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBiorthogonalDecomposition

variable {ι : Type*} [Fintype ι] {d DB : ℕ} {D N : ι → ℕ}
  {B : MPSTensor d DB} {A : ∀ c, MPSTensor d (D c)}
  {V : ∀ c, Fin (N c) → Matrix (Fin (D c)) (Fin DB) ℂ}
  {W : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (D c)) ℂ}

/-- The exact boundary decomposition is a zipper decomposition, retaining
both independently chosen maps. Source: GLM23 `fusiontensors`, `eq:orthoW`,
`fusiontensors2`, and `eq:orthoV`. -/
def toZipperDecomposition
    (h : IsBiorthogonalDecomposition B
      (fun q : (c : ι) × Fin (N c) ↦ A q.1)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2)) :
    ZipperDecomposition B A N where
  V := V
  W := W
  V_mul_W_self c μ := h.retract ⟨c, μ⟩
  V_mul_W_of_ne c μ e ν hne := h.orthogonal ⟨c, μ⟩ ⟨e, ν⟩ hne
  decomp i := by simpa only [Fintype.sum_sigma] using h.letter i

/-- The trace of a nonempty word counts each target block with its
multiplicity. Source: GLM23 Appendix A, `decompopen` and biorthogonality. -/
theorem trace_evalWord_eq_sum_multiplicity
    (h : IsBiorthogonalDecomposition B
      (fun q : (c : ι) × Fin (N c) ↦ A q.1)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))
    (w : List (Fin d)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord B w) =
      ∑ c, (N c : ℂ) * Matrix.trace (Kraus.evalWord (A c) w) := by
  have ht := h.trace_mul_evalWord 1 w hw
  simpa only [Matrix.one_mul, Matrix.mul_one, h.retract, Fintype.sum_sigma,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using ht

/-- Positive-dimensional target blocks with one common positive word span
have uniquely determined multiplicities in any exact biorthogonal
decomposition of the same tensor. Source: the multiplicity interpretation
of GLM23 Appendix A, with the derived simultaneous block inverse. -/
theorem multiplicity_eq_of_wordTupleSpanTop
    {g : ℕ} {dim N M : Fin g → ℕ} {A : ∀ c, MPSTensor d (dim c)}
    {VN : ∀ c, Fin (N c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {WN : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    {VM : ∀ c, Fin (M c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {WM : ∀ c, Fin (M c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    (hN : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (N c) ↦ A q.1)
      (fun q ↦ VN q.1 q.2) (fun q ↦ WN q.1 q.2))
    (hM : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (M c) ↦ A q.1)
      (fun q ↦ VM q.1 q.2) (fun q ↦ WM q.1 q.2))
    (hD : ∀ c, 0 < dim c) {L : ℕ} (hL : 0 < L)
    (hSpan : WordTupleSpanTop A L) : N = M := by
  have hzero := block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan
    (fun c ↦ ((N c : ℂ) - (M c : ℂ)) • (1 : Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (fun w ↦ by
      have hw : List.ofFn w ≠ [] := by rw [Ne, List.ofFn_eq_nil_iff]; omega
      have he := (hN.trace_evalWord_eq_sum_multiplicity (List.ofFn w) hw).symm.trans
        (hM.trace_evalWord_eq_sum_multiplicity (List.ofFn w) hw)
      simpa [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul,
        sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr he)
  funext c
  have he := congrArg (fun X ↦ X ⟨0, hD c⟩ ⟨0, hD c⟩) (hzero c)
  have he' : (N c : ℂ) = (M c : ℂ) := by
    apply sub_eq_zero.mp
    simpa using he
  exact_mod_cast he'

/-- The source's separated injective block assumptions already determine
the multiplicities; a simultaneous word span is derived internally.
Source: GLM23 block assumptions, lines 314--323, and Appendix A. -/
theorem multiplicity_eq_of_isInjective
    {g : ℕ} {dim N M : Fin g → ℕ} {A : ∀ c, MPSTensor d (dim c)}
    {VN : ∀ c, Fin (N c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {WN : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    {VM : ∀ c, Fin (M c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {WM : ∀ c, Fin (M c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    (hN : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (N c) ↦ A q.1)
      (fun q ↦ VN q.1 q.2) (fun q ↦ WN q.1 q.2))
    (hM : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (M c) ↦ A q.1)
      (fun q ↦ VM q.1 q.2) (fun q ↦ WM q.1 q.2))
    (hInj : ∀ c, Kraus.IsInjective (A c)) (hD : ∀ c, 0 < dim c)
    (hne : BlocksNotGaugePhaseEquiv A) : N = M := by
  obtain ⟨L, hL, hSpan⟩ := exists_positive_wordTupleSpanTop_of_isInjective hInj hD hne
  exact hN.multiplicity_eq_of_wordTupleSpanTop hM hD hL hSpan

end MPSTensor.IsBiorthogonalDecomposition

namespace MPSTensor

/-- A simultaneous word span separates rectangular intertwiners between
distinct target blocks. Source: GLM23 Appendix A, the block-separating inverse
in the proof of orthogonality. -/
theorem rectangularIntertwiner_eq_zero_of_wordTupleSpanTop
    {d g : ℕ} {dim : Fin g → ℕ} {A : ∀ c, MPSTensor d (dim c)}
    {L : ℕ} (hSpan : WordTupleSpanTop A L)
    (c e : Fin g) (hce : c ≠ e)
    (X : Matrix (Fin (dim c)) (Fin (dim e)) ℂ)
    (hX : ∀ i, A c i * X = X * A e i) : X = 0 := by
  classical
  have hall (M : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
      M c * X = X * M e := by
    have hM : M ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
      rw [hSpan]
      exact Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨w, rfl⟩ := hM
      exact Kraus.evalWord_intertwine (A c) (A e) X hX (List.ofFn w)
    | zero => simp
    | add M M' _ _ hM hM' =>
      simp only [Pi.add_apply, Matrix.add_mul, Matrix.mul_add, hM, hM']
    | smul z M _ hM =>
      simpa only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul] using
        congrArg (fun Y ↦ z • Y) hM
  simpa [hce, hce.symm] using hall (Pi.single c 1)

/-- Distinct positive-dimensional target blocks in a simultaneous word span
cannot be related by an invertible rectangular gauge. -/
theorem not_isGaugeRelated_of_wordTupleSpanTop
    {d g : ℕ} {dim : Fin g → ℕ} {A : ∀ c, MPSTensor d (dim c)}
    {L : ℕ} (hSpan : WordTupleSpanTop A L) (hD : ∀ c, 0 < dim c)
    (c e : Fin g) (hce : c ≠ e) : ¬ IsGaugeRelated (A c) (A e) := by
  rintro ⟨X, Y, hXY, _, hX⟩
  have hzero := rectangularIntertwiner_eq_zero_of_wordTupleSpanTop hSpan c e hce X hX
  have : NeZero (dim c) := ⟨(hD c).ne'⟩
  have hOne : (1 : Matrix (Fin (dim c)) (Fin (dim c)) ℂ) = 0 := by
    rw [← hXY, hzero, Matrix.zero_mul]
  exact one_ne_zero hOne

namespace IsBiorthogonalDecomposition

/-- Exact boundary decompositions with the same multiplicities differ by the
unique existing zipper gauge on the letter support. All block-separation
premises are derived from the source's injectivity and scalar-gauge exclusion.
Source: GLM23, fusion and action gauge freedoms at lines 415--424 and 595--602. -/
theorem exists_unique_multiplicityGauge_of_isInjective
    {d DB g : ℕ} {dim N : Fin g → ℕ} {B : MPSTensor d DB}
    {A : ∀ c, MPSTensor d (dim c)}
    {V V' : ∀ c, Fin (N c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {W W' : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    (h : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (N c) ↦ A q.1)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))
    (h' : IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (N c) ↦ A q.1)
      (fun q ↦ V' q.1 q.2) (fun q ↦ W' q.1 q.2))
    (hInj : ∀ c, Kraus.IsInjective (A c)) (hD : ∀ c, 0 < dim c)
    (hne : BlocksNotGaugePhaseEquiv A) :
    ∃! Y : ∀ c, GL (Fin (N c)) ℂ,
      (∀ c μ i, V' c μ * B i =
        ∑ ν, (↑(Y c) : Matrix (Fin (N c)) (Fin (N c)) ℂ) μ ν • (V c ν * B i)) ∧
      (∀ c κ i, B i * W' c κ =
        ∑ ν, (↑(Y c)⁻¹ : Matrix (Fin (N c)) (Fin (N c)) ℂ) ν κ • (B i * W c ν)) := by
  obtain ⟨L, _, hSpan⟩ := exists_positive_wordTupleSpanTop_of_isInjective hInj hD hne
  exact h.toZipperDecomposition.exists_unique_multiplicityGauge h'.toZipperDecomposition
    (fun c ↦ (hInj c).isNormal) hD (not_isGaugeRelated_of_wordTupleSpanTop hSpan hD)

end IsBiorthogonalDecomposition

end MPSTensor
