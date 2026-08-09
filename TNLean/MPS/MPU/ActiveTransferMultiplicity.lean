/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ShiftedTracePowerSpectrum
import TNLean.Channel.TransferMatrix
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.SharedInfra.Scaling
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Active Canonical Blocks and Transfer Multiplicity

This file proves the algebraic multiplicity step in arXiv:1703.09188,
Proposition `prop:normal-tensor`, lines 349--354. For literal CPSV canonical-form
data, the shifted transfer-trace identities force exactly one nonzero-weight
canonical block.

Each normal block supplies an unweighted fixed vector. Its weighted block has
eigenvalue `weight * star weight`; after embedding the corresponding diagonal
corner into the ambient bond space, the shifted nonzero-spectrum theorem forces
this eigenvalue to be one. The resulting ambient fixed vectors are linearly
independent. Applying the all-positive trace-power characteristic-polynomial
theorem to the square of the transfer matrix bounds their number by one.

No positivity, normality, diagonalizability, full-active-support, or first-moment
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
private noncomputable def ambientBlockInclusion (data : CPSVCanonicalFormData A) (k : Fin data.r) :
    Matrix (Fin D) (Fin (data.dim k)) ℂ :=
  data.ambient_coisometryᴴ * blockInclusion data.dim k

/-- A retained block inclusion into the ambient bond space is an isometry. -/
private theorem ambientBlockInclusion_conjTranspose_mul_self
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
private theorem mul_ambientBlockInclusion
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
    (X : (k : data.Active) → Matrix (Fin (data.dim k.1)) (Fin (data.dim k.1)) ℂ)
    (hX : ∀ k, X k ≠ 0) :
    LinearIndependent ℂ (fun k : data.Active =>
      data.ambientBlockInclusion k.1 * X k * (data.ambientBlockInclusion k.1)ᴴ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum k
  have hcompressed := congrArg
    (fun Z : Matrix (Fin D) (Fin D) ℂ =>
      (data.ambientBlockInclusion k.1)ᴴ * Z * data.ambientBlockInclusion k.1) hsum
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_zero, Matrix.zero_mul] at hcompressed
  have hterm : ∀ l : data.Active,
      (data.ambientBlockInclusion k.1)ᴴ *
          (data.ambientBlockInclusion l.1 * X l * (data.ambientBlockInclusion l.1)ᴴ) *
        data.ambientBlockInclusion k.1 = if l = k then X k else 0 := by
    intro l
    by_cases hlk : l = k
    · subst l
      rw [if_pos rfl, data.ambientBlockCompression_self]
    · rw [if_neg hlk]
      exact data.ambientBlockCompression_eq_zero_of_ne
        (k := k.1) (l := l.1) (fun h => hlk (Subtype.ext h.symm)) (X l)
  simp_rw [hterm] at hcompressed
  have hck : c k • X k = 0 := by
    calc
      c k • X k = ∑ l, c l • if l = k then X k else 0 := by simp
      _ = 0 := hcompressed
  exact (smul_eq_zero.mp hck).resolve_right (hX k)

/-- A normal MPS block has a nonzero fixed vector for its transfer map. -/
private theorem exists_nonzero_transferMap_fixedVector_of_normal
    {n : ℕ} {B : MPSTensor d n} (hB : IsNormalTensor B) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X ≠ 0 ∧ transferMap B X = X := by
  have hone : (1 : ℂ) ∈ peripheralEigenvalues (transferMap B) := by
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
    transferMap (data.blocks k) (data.blockFixedVector k) = data.blockFixedVector k :=
  (Classical.choose_spec
    (exists_nonzero_transferMap_fixedVector_of_normal (data.blocks_normal k))).2

/-- The transfer eigenvalue contributed by a weighted active block. -/
private noncomputable def activeTransferEigenvalue
    (data : CPSVCanonicalFormData A) (k : data.Active) : ℂ :=
  data.weights k.1 * starRingEnd ℂ (data.weights k.1)

/-- The weighted active block acts on its unweighted fixed vector with eigenvalue
`weight * star weight`. -/
private theorem transferMap_weightedBlock_blockFixedVector
    (data : CPSVCanonicalFormData A) (k : data.Active) :
    transferMap (fun i => data.weights k.1 • data.blocks k.1 i)
        (data.blockFixedVector k.1) =
      data.activeTransferEigenvalue k • data.blockFixedVector k.1 := by
  rw [transferMap_smul, data.transferMap_blockFixedVector]
  simp [activeTransferEigenvalue]

/-- The ambient matrix obtained by transporting one active block fixed vector. -/
private noncomputable def ambientActiveVector
    (data : CPSVCanonicalFormData A) (k : data.Active) : Matrix (Fin D) (Fin D) ℂ :=
  data.ambientBlockInclusion k.1 * data.blockFixedVector k.1 *
    (data.ambientBlockInclusion k.1)ᴴ

/-- An active block's transported ambient vector is nonzero. -/
private theorem ambientActiveVector_ne
    (data : CPSVCanonicalFormData A) (k : data.Active) :
    data.ambientActiveVector k ≠ 0 := by
  intro hzero
  apply data.blockFixedVector_ne k.1
  calc
    data.blockFixedVector k.1 =
        (data.ambientBlockInclusion k.1)ᴴ * data.ambientActiveVector k *
          data.ambientBlockInclusion k.1 :=
      (data.ambientBlockCompression_self k.1 (data.blockFixedVector k.1)).symm
    _ = 0 := by rw [hzero]; simp

/-- Before spectral normalization, the transported ambient vector has the weighted
block eigenvalue `weight * star weight`. -/
private theorem transferMap_ambientActiveVector
    (data : CPSVCanonicalFormData A) (k : data.Active) :
    transferMap A (data.ambientActiveVector k) =
      data.activeTransferEigenvalue k • data.ambientActiveVector k := by
  rw [ambientActiveVector, transferMap_conj_of_intertwine A
    (fun i => data.weights k.1 • data.blocks k.1 i)
    (data.ambientBlockInclusion k.1) (data.mul_ambientBlockInclusion k.1)
    (data.blockFixedVector k.1)]
  rw [data.transferMap_weightedBlock_blockFixedVector k]
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- An active block's weighted transfer eigenvalue is nonzero. -/
private theorem activeTransferEigenvalue_ne
    (data : CPSVCanonicalFormData A) (k : data.Active) :
    data.activeTransferEigenvalue k ≠ 0 := by
  simp [activeTransferEigenvalue, k.2]

/-- Shifted ambient transfer traces normalize every active weighted-block
eigenvalue to one. -/
private theorem activeTransferEigenvalue_eq_one
    (data : CPSVCanonicalFormData A)
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (transferMap A) ^ N) = 1)
    (k : data.Active) :
    data.activeTransferEigenvalue k = 1 := by
  have hEig : Module.End.HasEigenvalue (transferMap A) (data.activeTransferEigenvalue k) :=
    hasEigenvalue_of_eigenvector_eq _ _ (data.ambientActiveVector k)
      (data.transferMap_ambientActiveVector k) (data.ambientActiveVector_ne k)
  have hEigMatrix : Module.End.HasEigenvalue
      (transferMatrix (transferMap A)).toLin' (data.activeTransferEigenvalue k) :=
    (transferMatrix_hasEigenvalue_iff (transferMap A) _).mp hEig
  have hspecLin : data.activeTransferEigenvalue k ∈
      spectrum ℂ (transferMatrix (transferMap A)).toLin' :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp hEigMatrix
  have hspec : data.activeTransferEigenvalue k ∈
      spectrum ℂ (transferMatrix (transferMap A)) := by
    simpa using hspecLin
  exact Matrix.eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
    (transferMatrix (transferMap A)) htrace hspec (data.activeTransferEigenvalue_ne k)

/-- Under shifted ambient transfer traces, each transported active-block vector
is fixed by the ambient transfer map. -/
private theorem transferMap_ambientActiveVector_eq_self
    (data : CPSVCanonicalFormData A)
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (transferMap A) ^ N) = 1)
    (k : data.Active) :
    transferMap A (data.ambientActiveVector k) = data.ambientActiveVector k := by
  rw [data.transferMap_ambientActiveVector k, data.activeTransferEigenvalue_eq_one htrace k,
    one_smul]

/-- The shifted trace hypothesis bounds the one-eigenspace of the squared
transfer matrix by one dimension. -/
private theorem finrank_eigenspace_one_transferMatrix_sq_le_one
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (transferMap A) ^ N) = 1) :
    Module.finrank ℂ
      (Module.End.eigenspace ((transferMatrix (transferMap A) ^ 2).toLin') (1 : ℂ)) ≤ 1 := by
  let M := transferMatrix (transferMap A)
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

/-- The active canonical blocks give linearly independent ambient transfer fixed
vectors. -/
private theorem linearIndependent_ambientActiveVector
    (data : CPSVCanonicalFormData A) :
    LinearIndependent ℂ data.ambientActiveVector := by
  change LinearIndependent ℂ (fun k : data.Active =>
    data.ambientBlockInclusion k.1 * data.blockFixedVector k.1 *
      (data.ambientBlockInclusion k.1)ᴴ)
  exact data.linearIndependent_ambientBlockCorners
    (fun k : data.Active => data.blockFixedVector k.1)
    (fun k => data.blockFixedVector_ne k.1)

/-- Shifted transfer traces force exactly one active CPSV canonical block.

This is the algebraic-multiplicity step in arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 349--354. No full-active-support, positivity,
normality, diagonalizability, or first-moment hypothesis is required for the
ambient tensor. -/
theorem card_active_eq_one_of_shifted_transfer_trace
    (data : CPSVCanonicalFormData A)
    (htrace : ∀ N, 1 < N →
      Matrix.trace (transferMatrix (transferMap A) ^ N) = 1) :
    Fintype.card data.Active = 1 := by
  classical
  have hactive : Nonempty data.Active := by
    by_contra hempty
    haveI : IsEmpty data.Active := not_nonempty_iff.mp hempty
    have hweight : ∀ k : Fin data.r, data.weights k = 0 := by
      intro k
      by_contra hk
      exact isEmptyElim (⟨k, hk⟩ : data.Active)
    have hAzero : A = 0 := by
      funext i
      rw [data.reconstruct i]
      have hassembly : toTensorFromBlocks data.weights data.blocks i = 0 := by
        unfold toTensorFromBlocks
        simp only [hweight, zero_smul]
        change Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
          (Matrix.blockDiagonal' (0 : ∀ k : Fin data.r,
            Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ)) = 0
        rw [Matrix.blockDiagonal'_zero]
        simp
      rw [hassembly]
      simp
    have htwo := htrace 2 (by omega)
    rw [hAzero] at htwo
    have htransferZero :
        transferMatrix (transferMap (0 : MPSTensor d D)) = 0 := by
      ext ⟨a, b⟩ ⟨c, e⟩
      simp [transferMatrix, transferMap_apply]
    rw [htransferZero] at htwo
    simp at htwo
  let M := transferMatrix (transferMap A)
  let f : Module.End ℂ (Fin D × Fin D → ℂ) := (M ^ 2).toLin'
  let v : data.Active → f.eigenspace (1 : ℂ) := fun k =>
    ⟨(data.ambientActiveVector k).vec, by
      rw [Module.End.mem_eigenspace_iff]
      change (M ^ 2).toLin' (data.ambientActiveVector k).vec =
        (1 : ℂ) • (data.ambientActiveVector k).vec
      rw [Matrix.toLin'_apply]
      change transferMatrix (transferMap A) ^ 2 *ᵥ (data.ambientActiveVector k).vec = _
      rw [← transferMatrix_pow, transferMatrix_mulVec_eq]
      have hfix := data.transferMap_ambientActiveVector_eq_self htrace k
      have hpow : ((transferMap A) ^ 2) (data.ambientActiveVector k) =
          data.ambientActiveVector k := by
        change transferMap A (transferMap A (data.ambientActiveVector k)) =
          data.ambientActiveVector k
        rw [hfix, hfix]
      rw [hpow, one_smul]⟩
  let vecLM : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D × Fin D → ℂ) := {
    toFun := Matrix.vec
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hvecKer : LinearMap.ker vecLM = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro X hX
    exact Matrix.vec_inj.mp hX
  have hLIvec : LinearIndependent ℂ
      (fun k : data.Active => (data.ambientActiveVector k).vec) := by
    simpa [vecLM, Function.comp_def] using
      data.linearIndependent_ambientActiveVector.map' vecLM hvecKer
  have hLIv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum k
    apply Fintype.linearIndependent_iff.mp hLIvec c _ k
    have hcoe := congrArg
      (fun z : f.eigenspace (1 : ℂ) => (z : Fin D × Fin D → ℂ)) hsum
    simpa [v] using hcoe
  have hcard_le_finrank : Fintype.card data.Active ≤ Module.finrank ℂ (f.eigenspace 1) :=
    hLIv.fintype_card_le_finrank
  have hfinrank_le : Module.finrank ℂ (f.eigenspace 1) ≤ 1 := by
    simpa [f, M] using finrank_eigenspace_one_transferMatrix_sq_le_one
      (A := A) htrace
  have hcard_pos : 0 < Fintype.card data.Active := Fintype.card_pos_iff.mpr hactive
  omega

end CPSVCanonicalFormData

end MPSTensor
