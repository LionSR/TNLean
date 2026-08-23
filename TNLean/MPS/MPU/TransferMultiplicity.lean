/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.ShiftedTracePowerSpectrum
import QICLean.Channel.TransferMatrix
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.SharedInfra.Scaling
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Canonical Blocks and Transfer Multiplicity

This file proves the algebraic multiplicity step in arXiv:1703.09188,
Proposition `prop:normal-tensor`, lines 349--354. For literal CPSV canonical-form
data, the shifted transfer-trace identities force exactly one canonical block.

Each normal block supplies an unweighted fixed vector. Its weighted block has
eigenvalue `weight * star weight`; after embedding the corresponding diagonal
corner into the ambient bond space, the shifted nonzero-spectrum theorem forces
this eigenvalue to be one. The resulting ambient fixed vectors are linearly
independent. Applying the all-positive trace-power characteristic-polynomial
theorem to the square of the transfer matrix bounds their number by one.

No positivity, normality, diagonalizability, full-support, or first-moment
hypothesis is imposed on the ambient tensor.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188,
  Proposition `prop:normal-tensor`, lines 349--354
* [Cirac--Perez-Garcia--Schuch--Verstraete 2016] arXiv:1606.00608,
  Section 2.3, lines 214--263
-/

open scoped Matrix BigOperators
open Polynomial

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- The inclusion of a retained canonical block into the ambient bond space. -/
noncomputable def ambientBlockInclusion (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    Matrix (Fin D) (Fin (data.dim k)) ℂ :=
  data.ambient_coisometryᴴ * blockInclusion data.dim k

/-- A retained block inclusion into the ambient bond space is an isometry. -/
theorem ambientBlockInclusion_conjTranspose_mul_self
    (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    (data.ambientBlockInclusion k)ᴴ * data.ambientBlockInclusion k = 1 := by
  rw [ambientBlockInclusion, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc data.ambient_coisometry data.ambient_coisometryᴴ,
    data.coisometric, Matrix.one_mul, blockInclusion_conjTranspose_mul_self]

/-- Ambient inclusions of distinct retained blocks have orthogonal ranges. -/
private theorem ambientBlockInclusion_conjTranspose_mul_eq_zero
    (data : CPSVCanonicalFormData A) {k l : Fin data.r} (hkl : k ≠ l) :
    (data.ambientBlockInclusion k)ᴴ * data.ambientBlockInclusion l = 0 := by
  rw [ambientBlockInclusion, ambientBlockInclusion, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc data.ambient_coisometry data.ambient_coisometryᴴ,
    data.coisometric, Matrix.one_mul,
    blockInclusion_conjTranspose_mul_eq_zero data.dim hkl]

/-- The CPSV reconstruction intertwines an ambient block inclusion with the
corresponding weighted canonical block. -/
theorem mul_ambientBlockInclusion
    (data : CPSVCanonicalFormData A) (k : Fin data.r) (i : Fin d) :
    A i * data.ambientBlockInclusion k =
      data.ambientBlockInclusion k * (data.weights k • data.blocks k i) := by
  rw [data.reconstruct i, ambientBlockInclusion]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc data.ambient_coisometry data.ambient_coisometryᴴ,
    data.coisometric, Matrix.one_mul, toTensorFromBlocks_mul_blockInclusion]

/-- Compressing a matrix supported in one ambient block corner recovers that matrix. -/
private theorem ambientBlockCompression_self
    (data : CPSVCanonicalFormData A) (k : Fin data.r)
    (X : Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ) :
    (data.ambientBlockInclusion k)ᴴ *
        (data.ambientBlockInclusion k * X * (data.ambientBlockInclusion k)ᴴ) *
      data.ambientBlockInclusion k = X := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (data.ambientBlockInclusion k)ᴴ,
    data.ambientBlockInclusion_conjTranspose_mul_self, Matrix.one_mul]
  rw [Matrix.mul_one]

/-- Compressing a matrix supported in a different ambient block corner gives zero. -/
private theorem ambientBlockCompression_eq_zero_of_ne
    (data : CPSVCanonicalFormData A) {k l : Fin data.r} (hkl : k ≠ l)
    (X : Matrix (Fin (data.dim l)) (Fin (data.dim l)) ℂ) :
    (data.ambientBlockInclusion k)ᴴ *
        (data.ambientBlockInclusion l * X * (data.ambientBlockInclusion l)ᴴ) *
      data.ambientBlockInclusion k = 0 := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (data.ambientBlockInclusion k)ᴴ,
    data.ambientBlockInclusion_conjTranspose_mul_eq_zero hkl,
    Matrix.zero_mul]

/-- Nonzero matrices placed in the distinct ambient canonical-block corners are
linearly independent. -/
private theorem linearIndependent_ambientBlockCorners
    (data : CPSVCanonicalFormData A)
    (X : (k : Fin data.r) → Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ)
    (hX : ∀ k, X k ≠ 0) :
    LinearIndependent ℂ (fun k : Fin data.r =>
      data.ambientBlockInclusion k * X k * (data.ambientBlockInclusion k)ᴴ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum k
  have hcompressed := congrArg
    (fun Z : Matrix (Fin D) (Fin D) ℂ =>
      (data.ambientBlockInclusion k)ᴴ * Z * data.ambientBlockInclusion k) hsum
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_zero, Matrix.zero_mul] at hcompressed
  have hterm : ∀ l : Fin data.r,
      (data.ambientBlockInclusion k)ᴴ *
          (data.ambientBlockInclusion l * X l * (data.ambientBlockInclusion l)ᴴ) *
        data.ambientBlockInclusion k = if l = k then X k else 0 := by
    intro l
    by_cases hlk : l = k
    · subst l
      rw [ite_eq_left rfl, data.ambientBlockCompression_self]
    · rw [ite_eq_right hlk]
      exact data.ambientBlockCompression_eq_zero_of_ne (fun h => hlk h.symm) (X l)
  simp_rw [hterm] at hcompressed
  have hck : c k • X k = 0 := by
    calc
      c k • X k = ∑ l, c l • if l = k then X k else 0 := by simp
      _ = 0 := hcompressed
  exact (smul_eq_zero.mp hck).resolve_right (hX k)

/-- A normal MPS block has a nonzero fixed vector for its transfer map. -/
private theorem exists_nonzero_transferMap_fixedVector_of_normal
    {n : ℕ} {B : MPSTensor d n} (hB : IsNormalTensor B) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X ≠ 0 ∧ Kraus.transferMap B X = X := by
  have hone : (1 : ℂ) ∈ peripheralEigenvalues (Kraus.transferMap B) := by
    rw [hB.primitive_transfer]
    simp
  obtain ⟨X, hX⟩ := hone.1.exists_hasEigenvector
  exact ⟨X, hX.2, by simpa using hX.apply_eq_smul⟩

/-- A chosen nonzero transfer fixed vector for one retained normal block. -/
private noncomputable def blockFixedVector (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ :=
  Classical.choose (exists_nonzero_transferMap_fixedVector_of_normal (data.blocks_normal k))

/-- The chosen normal-block fixed vector is nonzero. -/
private theorem blockFixedVector_ne (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    data.blockFixedVector k ≠ 0 :=
  (Classical.choose_spec
    (exists_nonzero_transferMap_fixedVector_of_normal (data.blocks_normal k))).1

/-- The chosen normal-block vector is fixed by the unweighted block transfer map. -/
private theorem transferMap_blockFixedVector (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    Kraus.transferMap (data.blocks k) (data.blockFixedVector k) = data.blockFixedVector k :=
  (Classical.choose_spec
    (exists_nonzero_transferMap_fixedVector_of_normal (data.blocks_normal k))).2

/-- The transfer eigenvalue contributed by a weighted block. -/
noncomputable def transferEigenvalue
    (data : CPSVCanonicalFormData A) (k : Fin data.r) : ℂ :=
  data.weights k * starRingEnd ℂ (data.weights k)

/-- The weighted block acts on its unweighted fixed vector with eigenvalue
`weight * star weight`. -/
private theorem transferMap_weightedBlock_blockFixedVector
    (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    Kraus.transferMap (fun i => data.weights k • data.blocks k i)
        (data.blockFixedVector k) =
      data.transferEigenvalue k • data.blockFixedVector k := by
  rw [transferMap_smul, data.transferMap_blockFixedVector]
  simp [transferEigenvalue]

/-- The ambient matrix obtained by transporting one block fixed vector. -/
private noncomputable def ambientFixedVector
    (data : CPSVCanonicalFormData A) (k : Fin data.r) : Matrix (Fin D) (Fin D) ℂ :=
  data.ambientBlockInclusion k * data.blockFixedVector k *
    (data.ambientBlockInclusion k)ᴴ

/-- A block's transported ambient vector is nonzero. -/
private theorem ambientFixedVector_ne
    (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    data.ambientFixedVector k ≠ 0 := by
  intro hzero
  apply data.blockFixedVector_ne k
  calc
    data.blockFixedVector k =
        (data.ambientBlockInclusion k)ᴴ * data.ambientFixedVector k *
          data.ambientBlockInclusion k :=
      (data.ambientBlockCompression_self k (data.blockFixedVector k)).symm
    _ = 0 := by rw [hzero]; simp

/-- Before spectral normalization, the transported ambient vector has the weighted
block eigenvalue `weight * star weight`. -/
private theorem transferMap_ambientFixedVector
    (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    Kraus.transferMap A (data.ambientFixedVector k) =
      data.transferEigenvalue k • data.ambientFixedVector k := by
  rw [ambientFixedVector, transferMap_conj_of_intertwine A
    (fun i => data.weights k • data.blocks k i)
    (data.ambientBlockInclusion k) (data.mul_ambientBlockInclusion k)
    (data.blockFixedVector k)]
  rw [data.transferMap_weightedBlock_blockFixedVector k]
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- A block's weighted transfer eigenvalue is nonzero. -/
private theorem transferEigenvalue_ne
    (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    data.transferEigenvalue k ≠ 0 := by
  simp [transferEigenvalue, data.weights_ne_zero k]

/-- Shifted ambient transfer traces normalize every weighted-block eigenvalue to one. -/
theorem transferEigenvalue_eq_one
    (data : CPSVCanonicalFormData A)
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1)
    (k : Fin data.r) :
    data.transferEigenvalue k = 1 := by
  have hEig : Module.End.HasEigenvalue (Kraus.transferMap A) (data.transferEigenvalue k) :=
    hasEigenvalue_of_eigenvector_eq _ _ (data.ambientFixedVector k)
      (data.transferMap_ambientFixedVector k) (data.ambientFixedVector_ne k)
  have hEigMatrix : Module.End.HasEigenvalue
      (transferMatrix (Kraus.transferMap A)).toLin' (data.transferEigenvalue k) :=
    (transferMatrix_hasEigenvalue_iff (Kraus.transferMap A) _).mp hEig
  have hspecLin : data.transferEigenvalue k ∈
      spectrum ℂ (transferMatrix (Kraus.transferMap A)).toLin' :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp hEigMatrix
  have hspec : data.transferEigenvalue k ∈
      spectrum ℂ (transferMatrix (Kraus.transferMap A)) := by
    simpa using hspecLin
  exact Matrix.eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
    (transferMatrix (Kraus.transferMap A)) htrace hspec (data.transferEigenvalue_ne k)

/-- Under shifted ambient transfer traces, each transported block vector
is fixed by the ambient transfer map. -/
private theorem transferMap_ambientFixedVector_eq_self
    (data : CPSVCanonicalFormData A)
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1)
    (k : Fin data.r) :
    Kraus.transferMap A (data.ambientFixedVector k) = data.ambientFixedVector k := by
  rw [data.transferMap_ambientFixedVector k, data.transferEigenvalue_eq_one htrace k,
    one_smul]

/-- The shifted trace hypothesis bounds the one-eigenspace of the squared
transfer matrix by one dimension. -/
private theorem finrank_eigenspace_one_transferMatrix_sq_le_one
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1) :
    Module.finrank ℂ
      (Module.End.eigenspace ((transferMatrix (Kraus.transferMap A) ^ 2).toLin') (1 : ℂ)) ≤ 1 := by
  let M := transferMatrix (Kraus.transferMap A)
  have hpow2 :=
    Matrix.forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt
      M htrace 2 (by omega)
  have hchar : (M ^ 2).charpoly =
      X ^ (Fintype.card (Fin D × Fin D) - 1) * (X - 1) :=
    Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one
      (M ^ 2) hpow2
  calc
    Module.finrank ℂ (Module.End.eigenspace ((M ^ 2).toLin') (1 : ℂ)) ≤
        ((M ^ 2).toLin').charpoly.rootMultiplicity 1 :=
      LinearMap.finrank_eigenspace_le _ _
    _ = 1 := by
      rw [Matrix.charpoly_toLin', hchar]
      rw [Polynomial.rootMultiplicity_mul]
      · rw [Polynomial.rootMultiplicity_eq_zero]
        · simpa using
            (Polynomial.rootMultiplicity_X_sub_C_self (R := ℂ) (x := (1 : ℂ)))
        · simp [Polynomial.IsRoot]
      · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
          (Polynomial.X_sub_C_ne_zero 1)

/-- The canonical blocks give linearly independent ambient transfer fixed vectors. -/
private theorem linearIndependent_ambientFixedVector
    (data : CPSVCanonicalFormData A) :
    LinearIndependent ℂ data.ambientFixedVector := by
  change LinearIndependent ℂ (fun k : Fin data.r =>
    data.ambientBlockInclusion k * data.blockFixedVector k *
      (data.ambientBlockInclusion k)ᴴ)
  exact data.linearIndependent_ambientBlockCorners
    (fun k : Fin data.r => data.blockFixedVector k)
    (fun k => data.blockFixedVector_ne k)

/-- Shifted transfer traces force exactly one CPSV canonical block.

This is the algebraic-multiplicity step in arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 349--354. No full-support, positivity,
normality, diagonalizability, or first-moment hypothesis is required for the
ambient tensor. -/
theorem r_eq_one_of_shifted_transfer_trace
    (data : CPSVCanonicalFormData A)
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1) :
    data.r = 1 := by
  classical
  have hr_pos : 0 < data.r := by
    by_contra hempty
    have hr0 : data.r = 0 := by omega
    have hsum : (∑ k : Fin data.r, data.dim k) = 0 := by
      have : IsEmpty (Fin data.r) := by
        rw [hr0]
        infer_instance
      exact Fintype.sum_empty _
    have hAzero : A = 0 := by
      funext i
      rw [data.reconstruct i]
      have : IsEmpty (Fin (∑ k : Fin data.r, data.dim k)) := by
        rw [hsum]
        infer_instance
      ext x y
      simp [Matrix.mul_apply]
    have htwo := htrace 2 (by omega)
    rw [hAzero] at htwo
    have htransferZero :
        transferMatrix (Kraus.transferMap (0 : MPSTensor d D)) = 0 := by
      ext ⟨a, b⟩ ⟨c, e⟩
      simp [transferMatrix, Kraus.transferMap_apply]
    rw [htransferZero] at htwo
    simp at htwo
  let M := transferMatrix (Kraus.transferMap A)
  let f : Module.End ℂ (Fin D × Fin D → ℂ) := (M ^ 2).toLin'
  let v : Fin data.r → f.eigenspace (1 : ℂ) := fun k =>
    ⟨(data.ambientFixedVector k).vec, by
      rw [Module.End.mem_eigenspace_iff]
      change (M ^ 2).toLin' (data.ambientFixedVector k).vec =
        (1 : ℂ) • (data.ambientFixedVector k).vec
      rw [Matrix.toLin'_apply]
      change transferMatrix (Kraus.transferMap A) ^ 2 *ᵥ (data.ambientFixedVector k).vec = _
      rw [← transferMatrix_pow, transferMatrix_mulVec_eq]
      have hfix := data.transferMap_ambientFixedVector_eq_self htrace k
      have hpow : ((Kraus.transferMap A) ^ 2) (data.ambientFixedVector k) =
          data.ambientFixedVector k := by
        change Kraus.transferMap A (Kraus.transferMap A (data.ambientFixedVector k)) =
          data.ambientFixedVector k
        rw [hfix, hfix]
      rw [hpow, one_smul]⟩
  have hLIvec : LinearIndependent ℂ
      (fun k : Fin data.r => (data.ambientFixedVector k).vec) := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum k
    apply Fintype.linearIndependent_iff.mp
      data.linearIndependent_ambientFixedVector c _ k
    exact Matrix.vec_inj.mp (by
      funext x
      have hx := congrFun hsum x
      simpa only [Matrix.vec, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] using hx)
  have hLIv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum k
    apply Fintype.linearIndependent_iff.mp hLIvec c _ k
    have hcoe := congrArg
      (fun z : f.eigenspace (1 : ℂ) => (z : Fin D × Fin D → ℂ)) hsum
    simpa [v] using hcoe
  have hcard_le_finrank : Fintype.card (Fin data.r) ≤ Module.finrank ℂ (f.eigenspace 1) :=
    hLIv.fintype_card_le_finrank
  have hfinrank_le : Module.finrank ℂ (f.eigenspace 1) ≤ 1 := by
    simpa [f, M] using finrank_eigenspace_one_transferMatrix_sq_le_one
      (A := A) htrace
  rw [Fintype.card_fin] at hcard_le_finrank
  omega

end CPSVCanonicalFormData

end MPSTensor
