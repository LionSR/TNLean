/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import QICLean.Algebra.MatrixReindexUnitary
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Block

/-!
# A Schmidt space without a basis of unitary matrices

The Cartesian spin-one matrices give a six-dimensional bipartite reflection.
Its left operator space consists of scalar matrices plus complex skew-symmetric
matrices. The only unitary matrices in that space are scalar matrices. Thus a
recursive construction for arbitrary matrix product unitaries cannot require
that the Schmidt factors themselves form a basis of unitary matrices.

The mathematical argument is recorded in
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`.
-/

open scoped Matrix BigOperators

open Matrix

namespace MPUSchmidtObstruction

noncomputable section

/-- The Cartesian spin-one angular momentum matrices. -/
def spinOne : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]
  | 1 => !![0, 0, Complex.I; 0, 0, 0; -Complex.I, 0, 0]
  | 2 => !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]

/-- The spin-one/spin-half coupling, with Pauli rather than spin-half normalization. -/
def coupling : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  ∑ k : Fin 3, (spinOne k).kronecker (SpinCover.pauli k)

/-- The reflection with eigenvalues `1` and `-1` on the two total-spin sectors. -/
def reflection : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  (1 / 3 : ℂ) • (1 + (2 : ℂ) • coupling)

/-- The spin coupling is Hermitian. -/
theorem coupling_conjTranspose : couplingᴴ = coupling := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [coupling, spinOne, SpinCover.pauli, Matrix.conjTranspose_apply,
      Fin.sum_univ_three]

/-- The spin coupling satisfies its quadratic minimal-polynomial identity. -/
theorem coupling_sq : coupling * coupling = (2 : ℂ) • 1 - coupling := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [coupling, spinOne, SpinCover.pauli, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.kronecker_apply, Matrix.one_apply, Complex.I_mul_I]

/-- The bipartite reflection is unitary. -/
theorem reflection_mem_unitaryGroup :
    reflection ∈ Matrix.unitaryGroup (Fin 3 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hr : reflectionᴴ = reflection := by
    simp [reflection, coupling_conjTranspose]
  rw [hr]
  unfold reflection
  simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul, mul_one,
    coupling_sq]
  module

/-- A scalar matrix plus an arbitrary complex skew-symmetric three-dimensional matrix. -/
def scalarSkew (a : ℂ) (v : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![a, -v 2, v 1; v 2, a, -v 0; -v 1, v 0, a]
/-- The skew coefficient vector is an eigenvector of the scalar-plus-skew matrix. -/
theorem scalarSkew_mulVec (a : ℂ) (v : Fin 3 → ℂ) : scalarSkew a v *ᵥ v = a • v := by
  ext i
  fin_cases i <;> simp [scalarSkew, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
private theorem unitary_preserves_star_dotProduct {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X ∈ unitaryGroup n ℂ) (v : n → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (X *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hX, vecMul_one]
/-- A scalar-plus-skew-symmetric three-dimensional unitary has zero skew part. -/
theorem eq_zero_of_scalarSkew_mem_unitaryGroup (a : ℂ) (v : Fin 3 → ℂ)
    (h : scalarSkew a v ∈ unitaryGroup (Fin 3) ℂ) : v = 0 := by
  have hi := unitary_preserves_star_dotProduct (scalarSkew a v) h v
  rw [scalarSkew_mulVec] at hi
  simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hi
  have hic := congrArg Complex.re hi
  simp only [RCLike.star_def, dotProduct, Pi.star_apply, Fin.sum_univ_three,
    Fin.isValue, Complex.mul_re, Complex.conj_re, Complex.add_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add, Complex.add_im, Complex.mul_im] at hic
  have hrel : (Complex.normSq a - 1) *
      (Complex.normSq (v 0) + Complex.normSq (v 1) + Complex.normSq (v 2)) = 0 := by
    simp only [Complex.normSq_apply]
    nlinarith [hic]
  have hgram := Matrix.mem_unitaryGroup_iff'.mp h
  have h00 := congrArg Complex.re (congrFun (congrFun hgram 0) 0)
  have h11 := congrArg Complex.re (congrFun (congrFun hgram 1) 1)
  simp only [scalarSkew, Fin.isValue, star_eq_conjTranspose, Matrix.mul_apply,
    conjTranspose_apply, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
    RCLike.star_def, Fin.sum_univ_three, cons_val_one, cons_val, map_neg, mul_neg,
    neg_mul, neg_neg, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    sub_neg_eq_add, one_apply_eq, Complex.one_re] at h00 h11
  have h00' : Complex.normSq a + Complex.normSq (v 2) + Complex.normSq (v 1) = 1 := by
    simpa [Complex.normSq_apply] using h00
  have h11' : Complex.normSq (v 2) + Complex.normSq a + Complex.normSq (v 0) = 1 := by
    simpa [Complex.normSq_apply] using h11
  have hn0 := Complex.normSq_nonneg (v 0)
  have hn1 := Complex.normSq_nonneg (v 1)
  have hn2 := Complex.normSq_nonneg (v 2)
  have hs : Complex.normSq (v 0) + Complex.normSq (v 1) + Complex.normSq (v 2) = 0 := by
    rcases mul_eq_zero.mp hrel with ha | hs
    · have ha' := sub_eq_zero.mp ha
      linarith
    · exact hs
  have hv0 : Complex.normSq (v 0) = 0 := by linarith
  have hv1 : Complex.normSq (v 1) = 0 := by linarith
  have hv2 : Complex.normSq (v 2) = 0 := by linarith
  ext i
  apply Complex.normSq_eq_zero.mp
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hv2
/-- The linear parametrization of the scalar-plus-skew-symmetric operator space. -/
def scalarSkewLinearMap : (ℂ × (Fin 3 → ℂ)) →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun p := scalarSkew p.1 p.2
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarSkew] <;> ring
  map_smul' c p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarSkew]

/-- The left operator space of the spin-one/spin-half reflection. -/
def leftOperatorSpace : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ) := scalarSkewLinearMap.range

/-- Every unitary matrix in the left operator space is scalar. -/
theorem eq_smul_one_of_mem_leftOperatorSpace_of_unitary (X : Matrix (Fin 3) (Fin 3) ℂ)
    (hX : X ∈ leftOperatorSpace)
    (hu : X ∈ unitaryGroup (Fin 3) ℂ) : ∃ a : ℂ, X = a • 1 := by
  obtain ⟨⟨a, v⟩, h⟩ := hX
  change scalarSkew a v = X at h
  have hv := eq_zero_of_scalarSkew_mem_unitaryGroup a v (h ▸ hu)
  refine ⟨a, ?_⟩
  rw [← h, hv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarSkew]

/-- The first Cartesian spin matrix belongs to the left operator space. -/
theorem spinOne_zero_mem_leftOperatorSpace : spinOne 0 ∈ leftOperatorSpace := by
  refine ⟨⟨0, ![Complex.I, 0, 0]⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarSkewLinearMap, scalarSkew, spinOne]

/-- The left operator space is not spanned by its unitary matrices. -/
theorem leftOperatorSpace_not_spanned_by_unitaries :
    Submodule.span ℂ {X | X ∈ leftOperatorSpace ∧ X ∈ unitaryGroup (Fin 3) ℂ} ≠
      leftOperatorSpace := by
  intro heq
  have hle : Submodule.span ℂ {X | X ∈ leftOperatorSpace ∧ X ∈ unitaryGroup (Fin 3) ℂ} ≤
      Submodule.span ℂ {(1 : Matrix (Fin 3) (Fin 3) ℂ)} := by
    apply Submodule.span_le.mpr
    intro X hX
    obtain ⟨a, rfl⟩ := eq_smul_one_of_mem_leftOperatorSpace_of_unitary X hX.1 hX.2
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  have hspin := hle (heq.symm ▸ spinOne_zero_mem_leftOperatorSpace)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspin
  have h12 := congrFun (congrFun ha 1) 2
  norm_num [Matrix.one_apply, spinOne] at h12

/-- The four-dimensional operator-space parametrization obtained by adjoining an
identity sector to the reflection. Its active scalar is one third of its added scalar. -/
def paddedScalarSkew (a : ℂ) (v : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![a / 3, -v 2, v 1, 0; v 2, a / 3, -v 0, 0;
    -v 1, v 0, a / 3, 0; 0, 0, 0, a]

/-- No matrix in the padded scalar-plus-skew operator space is unitary. -/
theorem paddedScalarSkew_not_mem_unitaryGroup (a : ℂ) (v : Fin 3 → ℂ) :
    paddedScalarSkew a v ∉ unitaryGroup (Fin 4) ℂ := by
  intro h
  have hg := mem_unitaryGroup_iff'.mp h
  have ht : scalarSkew (a / 3) v ∈ unitaryGroup (Fin 3) ℂ := by
    rw [mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    have hij := congrFun (congrFun hg i.castSucc) j.castSucc
    fin_cases i <;> fin_cases j <;>
      simpa [paddedScalarSkew, scalarSkew, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_four] using hij
  have hv := eq_zero_of_scalarSkew_mem_unitaryGroup (a / 3) v ht
  have h00 := congrArg Complex.re (congrFun (congrFun hg 0) 0)
  have h33 := congrArg Complex.re (congrFun (congrFun hg 3) 3)
  simp only [paddedScalarSkew, hv, Fin.isValue, Pi.zero_apply, neg_zero,
    star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one, RCLike.star_def, Fin.sum_univ_four, map_div₀,
    cons_val_one, map_zero, mul_zero, add_zero, cons_val, Complex.mul_re,
    Complex.div_ofNat_re, Complex.div_ofNat_im, one_apply_eq, Complex.one_re,
    zero_add, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add] at h00 h33
  change (star a / star (3 : ℂ)).re * (a.re / 3) -
    (star a / star (3 : ℂ)).im * (a.im / 3) = 1 at h00
  norm_num [Complex.star_def] at h00
  nlinarith

/-- The linear parametrization of the left operator space of the qubit embedding. -/
def paddedScalarSkewLinearMap :
    (ℂ × (Fin 3 → ℂ)) →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun p := paddedScalarSkew p.1 p.2
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [paddedScalarSkew] <;> ring
  map_smul' c p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [paddedScalarSkew] <;> ring

/-- The left operator space obtained after adjoining the identity sector. -/
def qubitLeftOperatorSpace : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  paddedScalarSkewLinearMap.range

/-- The left operator space of the qubit embedding contains no unitary matrix. -/
theorem not_mem_unitaryGroup_of_mem_qubitLeftOperatorSpace
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X ∈ qubitLeftOperatorSpace) :
    X ∉ unitaryGroup (Fin 4) ℂ := by
  obtain ⟨⟨a, v⟩, rfl⟩ := hX
  exact paddedScalarSkew_not_mem_unitaryGroup a v

/-- The Cartesian spin-one matrices with a zero fourth row and column. -/
def paddedSpinOne (k : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  paddedScalarSkew 0 (fun j => if j = k then Complex.I else 0)

/-- The three-qubit reflection obtained by adjoining an identity sector. -/
def qubitReflection : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ :=
  (paddedScalarSkew 1 0).kronecker 1 + (2 / 3 : ℂ) •
    ∑ k : Fin 3, (paddedSpinOne k).kronecker (SpinCover.pauli k)

/-- The embedded three-qubit reflection is unitary. -/
theorem qubitReflection_mem_unitaryGroup :
    qubitReflection ∈ unitaryGroup (Fin 4 × Fin 2) ℂ := by
  let f : ((Fin 3 × Fin 2) ⊕ Fin 2) → Fin 4 × Fin 2 :=
    Sum.elim (fun p => (p.1.castSucc, p.2)) (fun j => (3, j))
  have hf : Function.Bijective f := by
    dsimp only [f]
    decide +kernel
  let e := Equiv.ofBijective f hf
  have hd : fromBlocks reflection 0 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈
      unitaryGroup ((Fin 3 × Fin 2) ⊕ Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, fromBlocks_conjTranspose,
      fromBlocks_multiply]
    have hr : reflection * reflectionᴴ = 1 := by
      simpa only [star_eq_conjTranspose] using
        mem_unitaryGroup_iff.mp reflection_mem_unitaryGroup
    simp [hr, ← Matrix.fromBlocks_one]
  have hm : reindex e.symm e.symm qubitReflection =
      fromBlocks reflection 0 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext a b
    rcases a with ⟨i, j⟩ | j <;> rcases b with ⟨k, l⟩ | l
    · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp [qubitReflection, paddedSpinOne, paddedScalarSkew, reflection, coupling,
          spinOne, SpinCover.pauli, e, f, Matrix.reindex_apply, Matrix.fromBlocks,
          Equiv.ofBijective, Fin.castSucc, Fin.sum_univ_three] <;> ring
    · fin_cases i <;> fin_cases j <;> fin_cases l <;>
        simp [qubitReflection, paddedSpinOne, paddedScalarSkew, e, f,
          Matrix.reindex_apply, Matrix.fromBlocks, Equiv.ofBijective, Fin.castSucc,
          SpinCover.pauli, Fin.sum_univ_three]
    · fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp [qubitReflection, paddedSpinOne, paddedScalarSkew, e, f,
          Matrix.reindex_apply, Matrix.fromBlocks, Equiv.ofBijective, Fin.castSucc,
          SpinCover.pauli, Fin.sum_univ_three]
    · fin_cases j <;> fin_cases l <;>
        simp [qubitReflection, paddedSpinOne, paddedScalarSkew, e, f,
          Matrix.reindex_apply, Matrix.fromBlocks, Equiv.ofBijective, Fin.castSucc,
          SpinCover.pauli, Fin.sum_univ_three]
  have hu : reindex e.symm e.symm qubitReflection ∈ unitaryGroup _ ℂ := hm.symm ▸ hd
  have hu' := reindex_mem_unitaryGroup e _ hu
  simpa using hu'

end

end MPUSchmidtObstruction
