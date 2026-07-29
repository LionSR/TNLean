/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ListProduct
import TNLean.Channel.SingleKrausPositivity
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport

/-!
# Sitewise physical matrices on periodic MPOs

A one-site matrix `V` acts on a chain by its sitewise tensor power.  Acting on
both physical legs of a periodic MPO is the same as changing the physical
basis of every local MPO matrix before closing the virtual trace.

This is finite-dimensional tensor-product algebra.  The construction is used
below with the BNT physical-sector projections of arXiv:1606.00608,
Appendix C.2, equations `generateMPDO` and `sigmaNKj`.
-/

open scoped Matrix BigOperators Kronecker

namespace Matrix

/-- Reindexing the input and output bases commutes with a single-Kraus
conjugation. -/
theorem reindex_singleKrausMap
    {α α' β β' : Type*} [Fintype α] [Fintype α']
    [Fintype β] [Fintype β']
    (eα : α ≃ α') (eβ : β ≃ β')
    (V : Matrix β α ℂ) (X : Matrix α α ℂ) :
    reindex eβ eβ (singleKrausMap V X) =
      singleKrausMap (reindex eβ eα V) (reindex eα eα X) := by
  simp only [singleKrausMap_apply]
  change reindexLinearEquiv ℂ ℂ eβ eβ (V * X * Vᴴ) = _
  rw [← reindexLinearEquiv_mul ℂ ℂ eβ eα eβ,
    ← reindexLinearEquiv_mul ℂ ℂ eβ eα eα]
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.conjTranspose_reindex]

end Matrix

namespace MPOTensor

variable {d D e f : ℕ}

open PhysicalSectorFactorization

/-- The sitewise tensor power of a one-site physical matrix, indexed by
physical configurations rather than by nested tensor products. -/
noncomputable def sitewisePhysicalMatrix
    (V : Matrix (Fin e) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin N → Fin e) (Fin N → Fin d) ℂ :=
  fun s t ↦ ∏ n : Fin N, V (s n) (t n)

/-- Sitewise tensor powers preserve rectangular matrix multiplication. -/
theorem sitewisePhysicalMatrix_mul
    (V : Matrix (Fin e) (Fin d) ℂ)
    (W : Matrix (Fin d) (Fin f) ℂ) (N : ℕ) :
    sitewisePhysicalMatrix V N * sitewisePhysicalMatrix W N =
      sitewisePhysicalMatrix (V * W) N := by
  classical
  ext s t
  simp only [Matrix.mul_apply, sitewisePhysicalMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin d)))
    (fun n a ↦ V (s n) a * W a (t n))]

/-- Conjugate transpose commutes with the sitewise tensor power. -/
theorem sitewisePhysicalMatrix_conjTranspose
    (V : Matrix (Fin e) (Fin d) ℂ) (N : ℕ) :
    (sitewisePhysicalMatrix V N)ᴴ = sitewisePhysicalMatrix Vᴴ N := by
  ext s t
  simp [Matrix.conjTranspose_apply, sitewisePhysicalMatrix, star_prod]

/-- The sitewise tensor power of a one-site isometry is an isometry. -/
theorem sitewisePhysicalMatrix_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1) (N : ℕ) :
    (sitewisePhysicalMatrix V N)ᴴ * sitewisePhysicalMatrix V N = 1 := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    sitewisePhysicalMatrix]
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin e)))
    (fun n a ↦ star (V a (x n)) * V a (y n))]
  have hentry : ∀ n : Fin N,
      (∑ a : Fin e, star (V a (x n)) * V a (y n)) =
        if x n = y n then 1 else 0 := by
    intro n
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using congrFun (congrFun hV (x n)) (y n)
  simp_rw [hentry]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

/-- The product of a sitewise tensor power with its conjugate transpose is the
sitewise tensor power of the corresponding one-site product. -/
theorem sitewisePhysicalMatrix_mul_conjTranspose
    (V : Matrix (Fin d) (Fin e) ℂ) (N : ℕ) :
    sitewisePhysicalMatrix V N * (sitewisePhysicalMatrix V N)ᴴ =
      sitewisePhysicalMatrix (V * Vᴴ) N := by
  classical
  ext s t
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    sitewisePhysicalMatrix, star_prod]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin e)))
    (fun n a ↦ V (s n) a * star (V (t n) a))]

/-- On two sites, the configuration-indexed tensor power is the Kronecker square. -/
theorem reindex_sitewisePhysicalMatrix_two
    (V : Matrix (Fin e) (Fin d) ℂ) :
    Matrix.reindex (_root_.finTwoArrowEquiv (Fin e))
        (_root_.finTwoArrowEquiv (Fin d))
        (sitewisePhysicalMatrix V 2) = V ⊗ₖ V := by
  ext ⟨i, j⟩ ⟨a, b⟩
  simp [Matrix.reindex_apply, sitewisePhysicalMatrix,
    Matrix.kroneckerMap_apply, _root_.finTwoArrowEquiv]

/-- The sitewise tensor power of the identity matrix is the identity matrix. -/
@[simp] theorem sitewisePhysicalMatrix_one (d N : ℕ) :
    sitewisePhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ) N = 1 := by
  classical
  ext x y
  simp only [sitewisePhysicalMatrix, Matrix.one_apply]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

private def braKetFunctionsEquiv {i a b : Type*} :
    ((i → b) × (i → a)) ≃ (i → a × b) :=
  (Equiv.prodComm _ _).trans
    (Equiv.arrowProdEquivProdArrow i (fun _ ↦ a) (fun _ ↦ b)).symm

/-- Word evaluation after a physical basis change, expanded over the original
ket and bra configurations. -/
theorem evalWord_changePhysicalBasis_ofFn
    (V : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D) {N : ℕ}
    (s t : Fin N → Fin e) :
    evalWord (changePhysicalBasis V M) (List.ofFn s) (List.ofFn t) =
      ∑ x : Fin N → Fin d × Fin d,
        (∏ i : Fin N, V (s i) (x i).1 * star (V (t i) (x i).2)) •
          evalWord M
            (List.ofFn fun i : Fin N ↦ (x i).1)
            (List.ofFn fun i : Fin N ↦ (x i).2) := by
  rw [evalWord_ofFn]
  simp_rw [changePhysicalBasis_apply_eq_sum]
  rw [List.prod_ofFn_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [List.prod_ofFn_smul, evalWord_ofFn]

/-- Acting on every site by `V` sends the MPO of `M` to the MPO obtained by
changing every local physical matrix by `V`.

This is the configuration-index form of
\((V^{\otimes N})\rho^{(N)}(M)(V^{\otimes N})^\dagger\).
-/
theorem singleKrausMap_sitewisePhysicalMatrix_mpo
    (V : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D) (N : ℕ) :
    singleKrausMap (sitewisePhysicalMatrix V N) (mpo M N) =
      mpo (changePhysicalBasis V M) N := by
  ext s t
  simp only [singleKrausMap_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, sitewisePhysicalMatrix, mpo_apply,
    mpoMatrixEntry, evalWord_changePhysicalBasis_ofFn, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, star_prod]
  have hexpand :
      (∑ q : Fin N → Fin d,
        (∑ p : Fin N → Fin d,
          (∏ i : Fin N, V (s i) (p i)) *
            Matrix.trace (evalWord M (List.ofFn p) (List.ofFn q))) *
          (∏ i : Fin N, star (V (t i) (q i)))) =
        ∑ q : Fin N → Fin d, ∑ p : Fin N → Fin d,
          ((∏ i : Fin N, V (s i) (p i)) *
            Matrix.trace (evalWord M (List.ofFn p) (List.ofFn q))) *
          (∏ i : Fin N, star (V (t i) (q i))) := by
    apply Finset.sum_congr rfl
    intro q _
    simpa only using Finset.sum_mul Finset.univ
      (fun p : Fin N → Fin d ↦
        (∏ i : Fin N, V (s i) (p i)) *
          Matrix.trace (evalWord M (List.ofFn p) (List.ofFn q)))
      (∏ i : Fin N, star (V (t i) (q i)))
  rw [hexpand]
  have h := Fintype.sum_equiv
    (braKetFunctionsEquiv (i := Fin N) (a := Fin d) (b := Fin d))
    (fun p : (Fin N → Fin d) × (Fin N → Fin d) ↦
      (∏ i : Fin N, V (s i) (p.2 i)) *
        Matrix.trace (evalWord M (List.ofFn p.2) (List.ofFn p.1)) *
        (∏ i : Fin N, star (V (t i) (p.1 i))))
    (fun x : Fin N → Fin d × Fin d ↦
      (∏ i : Fin N, V (s i) (x i).1 * star (V (t i) (x i).2)) *
        Matrix.trace (evalWord M
          (List.ofFn fun i : Fin N ↦ (x i).1)
          (List.ofFn fun i : Fin N ↦ (x i).2)))
    (fun p ↦ by
      dsimp
      change
        (∏ i : Fin N, V (s i) (p.2 i)) *
              Matrix.trace (evalWord M (List.ofFn p.2) (List.ofFn p.1)) *
            (∏ i : Fin N, star (V (t i) (p.1 i))) =
          (∏ i : Fin N,
            V (s i) (p.2 i) * star (V (t i) (p.1 i))) *
            Matrix.trace (evalWord M (List.ofFn p.2) (List.ofFn p.1))
      have hprod :
          (∏ i : Fin N,
            V (s i) (p.2 i) * star (V (t i) (p.1 i))) =
            (∏ i : Fin N, V (s i) (p.2 i)) *
              (∏ i : Fin N, star (V (t i) (p.1 i))) := by
        exact Finset.prod_mul_distrib
      rw [hprod]
      ring)
  rw [Fintype.sum_prod_type] at h
  exact h

/-- If an MPO is positive after an isometric physical inclusion, then it was
already positive before inclusion. -/
theorem isMPDO_of_changePhysicalBasis_isMPDO_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (hM : IsMPDO (changePhysicalBasis V M)) :
    IsMPDO M := by
  intro N hN
  apply Matrix.posSemidef_of_singleKraus_isometry
    (sitewisePhysicalMatrix V N) (sitewisePhysicalMatrix_isometry V hV N)
  rw [singleKrausMap_sitewisePhysicalMatrix_mpo]
  exact hM N hN

/-- The sitewise tensor power of a Hermitian one-site matrix is Hermitian. -/
theorem sitewisePhysicalMatrix_isHermitian
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) (N : ℕ) :
    (sitewisePhysicalMatrix P N).IsHermitian := by
  ext s t
  simp only [Matrix.conjTranspose_apply, sitewisePhysicalMatrix, star_prod]
  apply Finset.prod_congr rfl
  intro n _
  exact hP.apply (s n) (t n)

end MPOTensor
