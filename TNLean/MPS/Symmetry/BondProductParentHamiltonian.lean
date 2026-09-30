/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondInterpolation
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding
import TNLean.Algebra.CommutingProjectionProduct

/-!
# Parent Hamiltonian of independent bonds

Regroup the virtual legs of a finite chain into independent two-leg bonds.
For a unit bond vector `η`, the local energy on each bond is
`1 - |η⟩⟨η|`. The resulting terms commute, and their sum has a spectral
gap of at least one, independently of the number of bonds. This is the
parent-Hamiltonian calculation used in Schuch--Pérez-García--Cirac,
arXiv:1010.3732, Sections II.D.2 and II.F.2.

The theorem concerns the regrouped bond Hilbert space. Identifying it with
the original physical chain and transporting symmetry are separate steps.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {q N : ℕ}

/-- The rank-one projection onto a normalized bond vector.
Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
def bondVectorProjection (η : Fin q → ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.vecMulVec η (star η)

/-- The complement of the bond-vector line is the local parent term.
Source: arXiv:1010.3732, Section II.D.2. -/
def bondPenalty (η : Fin q → ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  1 - bondVectorProjection η

/-- A unit bond vector determines an orthogonal rank-one projection.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem bondVectorProjection_isStarProjection (η : Fin q → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1) :
    IsStarProjection (bondVectorProjection η) := by
  classical
  have hnorm : (∑ x : Fin q, star (η x) * η x) = 1 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hη
    simpa [Complex.normSq_eq_conj_mul_self, Complex.star_def] using h
  rw [isStarProjection_iff']
  constructor
  · ext i j
    simp only [Matrix.mul_apply, bondVectorProjection, Matrix.vecMulVec_apply]
    calc
      (∑ x : Fin q, (η i * star (η x)) * (η x * star (η j))) =
          η i * (∑ x : Fin q, star (η x) * η x) * star (η j) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = η i * star (η j) := by rw [hnorm]; ring
  · ext i j
    simp [bondVectorProjection, Matrix.vecMulVec_apply, star_mul]

/-- The local parent term is an orthogonal projection.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem bondPenalty_isStarProjection (η : Fin q → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1) :
    IsStarProjection (bondPenalty η) :=
  (bondVectorProjection_isStarProjection η hη).one_sub

/-- One independent-bond penalty, embedded at position `i` in the regrouped
finite chain. Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
noncomputable def bondPenaltyAt (η : Fin q → ℂ) (hN : 1 ≤ N) (i : Fin N) :
    MPOTensor.ChainOperator q N :=
  MPOTensor.embedLocalOperator 1 N hN i
    (MPOTensor.oneSiteOperator (bondPenalty η))

/-- Sum of the independent-bond penalties on a finite chain.
Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
noncomputable def bondProductParentHamiltonian
    (η : Fin q → ℂ) (hN : 1 ≤ N) : MPOTensor.ChainOperator q N :=
  ∑ i : Fin N, bondPenaltyAt η hN i

private theorem oneSiteOperator_isStarProjection
    (A : Matrix (Fin q) (Fin q) ℂ) (hA : IsStarProjection A) :
    IsStarProjection (MPOTensor.oneSiteOperator A) := by
  let e : (Fin 1 → Fin q) ≃ Fin q := Equiv.funUnique (Fin 1) (Fin q)
  have he : MPOTensor.oneSiteOperator A =
      (Matrix.reindexAlgEquiv ℂ ℂ e).symm A := by
    ext x y
    rfl
  rw [he, isStarProjection_iff']
  rw [isStarProjection_iff'] at hA
  constructor
  · rw [← map_mul, hA.1]
  · ext x y
    exact congrArg (fun M : Matrix (Fin q) (Fin q) ℂ => M (e x) (e y)) hA.2

/-- Every embedded independent-bond penalty is an orthogonal projection.
Source: arXiv:1010.3732, Section II.D.2. -/
theorem bondPenaltyAt_isStarProjection (η : Fin q → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) (i : Fin N) :
    IsStarProjection (bondPenaltyAt η hN i) :=
  MPOTensor.embedLocalOperator_isStarProjection 1 N hN i
    (oneSiteOperator_isStarProjection (bondPenalty η) (bondPenalty_isStarProjection η hη))

/-- Independent-bond parent terms commute.
Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem bondPenaltyAt_commute (η : Fin q → ℂ) (hN : 1 ≤ N)
    (i j : Fin N) :
    Commute (bondPenaltyAt η hN i) (bondPenaltyAt η hN j) :=
  MPOTensor.embedLocalOperator_one_commute hN (bondPenalty η) i j

/-- The product of identical bond vectors, in independent-bond coordinates.
Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
def bondProductVector (η : Fin q → ℂ) (N : ℕ) :
    (Fin N → Fin q) → ℂ :=
  fun σ => ∏ i : Fin N, η (σ i)

/-- The product bond vector as an element of the finite-chain Hilbert space.
Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
def bondProductState (η : Fin q → ℂ) (N : ℕ) :
    EuclideanSpace ℂ (Fin N → Fin q) :=
  WithLp.toLp 2 (bondProductVector η N)

private theorem sitewise_bondVectorProjection_eq_productVectorProjection
    (η : Fin q → ℂ) (N : ℕ) :
    MPOTensor.sitewiseMatrixFamily
      (fun _ : Fin N => bondVectorProjection η) =
        Matrix.vecMulVec (bondProductVector η N) (star (bondProductVector η N)) := by
  ext σ τ
  simp only [MPOTensor.sitewiseMatrixFamily, bondVectorProjection,
    Matrix.vecMulVec_apply, bondProductVector, Pi.star_apply]
  rw [Finset.prod_mul_distrib]
  simp

/-- The product of local bond-line projections is the rank-one projection
onto the product bond vector. Source: arXiv:1010.3732,
Sections II.D.2 and II.F.2. -/
theorem bondProductVectorProjection_eq_localProduct
    (η : Fin q → ℂ) (hN : 1 ≤ N) :
    (Finset.univ : Finset (Fin N)).noncommProd
      (fun i => MPOTensor.embedLocalOperator 1 N hN i
        (MPOTensor.oneSiteOperator (bondVectorProjection η)))
      (by
        intro i _ j _ _
        exact MPOTensor.embedLocalOperator_one_commute hN
          (bondVectorProjection η) i j) =
        Matrix.vecMulVec (bondProductVector η N) (star (bondProductVector η N)) := by
  rw [MPOTensor.prod_embedLocalOperator_one_eq_sitewiseMatrixFamily,
    sitewise_bondVectorProjection_eq_productVectorProjection]

/-- Matrix coordinates for operators on the independent-bond Hilbert space. -/
noncomputable def bondMatrixEquiv (q N : ℕ) :=
  LinearMap.toMatrixOrthonormal
    (EuclideanSpace.basisFun (Fin N → Fin q) ℂ)

/-- The inverse of the matrix-coordinate equivalence acts by matrix
multiplication on Euclidean vectors. -/
theorem bondMatrixEquiv_symm_eq_toEuclideanLin
    (A : MPOTensor.ChainOperator q N) :
    (bondMatrixEquiv q N).symm A = Matrix.toEuclideanLin A := by
  rfl

/-- The local bond penalty acting on the Hilbert space of all bond
configurations. Source: arXiv:1010.3732, Section II.D.2. -/
noncomputable def bondPenaltyAtLin (η : Fin q → ℂ) (hN : 1 ≤ N)
    (i : Fin N) :
    EuclideanSpace ℂ (Fin N → Fin q) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin N → Fin q) :=
  (bondMatrixEquiv q N).symm (bondPenaltyAt η hN i)

/-- The independent-bond parent Hamiltonian as a linear operator on the
finite-chain Hilbert space. Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
noncomputable def bondProductParentHamiltonianLin
    (η : Fin q → ℂ) (hN : 1 ≤ N) :
    EuclideanSpace ℂ (Fin N → Fin q) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin N → Fin q) :=
  (bondMatrixEquiv q N).symm (bondProductParentHamiltonian η hN)

private theorem bondPenaltyAtLin_isSymmetricProjection
    (η : Fin q → ℂ) (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) (i : Fin N) :
    (bondPenaltyAtLin η hN i).IsSymmetricProjection := by
  exact LinearMap.isStarProjection_iff_isSymmetricProjection.mp
    ((bondPenaltyAt_isStarProjection η hη hN i).map
      (bondMatrixEquiv q N).symm)

private theorem bondPenaltyAtLin_commute (η : Fin q → ℂ)
    (hN : 1 ≤ N) (i j : Fin N) :
    Commute (bondPenaltyAtLin η hN i) (bondPenaltyAtLin η hN j) :=
  (bondPenaltyAt_commute η hN i j).map (bondMatrixEquiv q N).symm

private theorem listProd_ofFn_eq_noncommProd
    {M : Type*} [Monoid M] {N : ℕ} (f : Fin N → M)
    (hcomm : ∀ i j, Commute (f i) (f j)) :
    (List.ofFn f).prod =
      (Finset.univ : Finset (Fin N)).noncommProd f
        (fun i _ j _ _ => hcomm i j) := by
  classical
  let l : List (Fin N) := List.ofFn id
  have hl : l.Nodup := List.nodup_ofFn.mpr (fun _ _ h => h)
  have he : l.toFinset = Finset.univ := by
    ext i
    simp [l]
  have h := Finset.noncommProd_toFinset l f
    (fun i _ j _ _ => hcomm i j) hl
  simpa [he, l, List.map_ofFn] using h.symm

/-- The parent Hamiltonian on `N` independent bonds has the uniform
quadratic-form gap `H² ≥ H`. In particular, every nonzero excited eigenvalue
is at least one. Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem bondProductParentHamiltonian_gap_one
    (η : Fin q → ℂ) (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) (v : EuclideanSpace ℂ (Fin N → Fin q)) :
    (⟪bondProductParentHamiltonianLin η hN v, v⟫_ℂ).re ≤
      (⟪bondProductParentHamiltonianLin η hN v,
        bondProductParentHamiltonianLin η hN v⟫_ℂ).re := by
  have hsum : bondProductParentHamiltonianLin η hN =
      ∑ i : Fin N, bondPenaltyAtLin η hN i := by
    simp [bondProductParentHamiltonianLin, bondProductParentHamiltonian,
      bondPenaltyAtLin, map_sum]
  rw [hsum]
  have h := ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum
    (γ := 1) (by norm_num)
    (fun i : Fin N => bondPenaltyAtLin η hN i)
    (bondPenaltyAtLin_isSymmetricProjection η hη hN)
    (fun _ _ => (0 : ℝ))
    (by intro i; simp)
    (by
      intro i j hj w
      have hc := bondPenaltyAtLin_commute η hN i j
      have hpos := LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
        (bondPenaltyAtLin_isSymmetricProjection η hη hN i)
        (bondPenaltyAtLin_isSymmetricProjection η hη hN j)
        (fun x => congrArg (fun T => T x) hc.eq) w
      simpa using hpos) v
  simpa only [one_mul] using h

/-- The ground space is the range of the product of the commuting local
bond-line projections. This identifies the joint local kernel with the
kernel of the parent Hamiltonian. Source: arXiv:1010.3732,
Sections II.D.2 and II.F.2. -/
theorem bondProductParentHamiltonian_groundSpace
    (η : Fin q → ℂ) (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) :
    LinearMap.range
      ((List.ofFn fun i : Fin N =>
        (1 : EuclideanSpace ℂ (Fin N → Fin q) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin N → Fin q)) - bondPenaltyAtLin η hN i).prod) =
      LinearMap.ker (bondProductParentHamiltonianLin η hN) := by
  have hsum : bondProductParentHamiltonianLin η hN =
      ∑ i : Fin N, bondPenaltyAtLin η hN i := by
    simp [bondProductParentHamiltonianLin, bondProductParentHamiltonian,
      bondPenaltyAtLin, map_sum]
  rw [hsum]
  exact LinearMap.range_listProd_one_sub_eq_ker_sum
    (fun i : Fin N => bondPenaltyAtLin η hN i)
    (bondPenaltyAtLin_isSymmetricProjection η hη hN)
    (bondPenaltyAtLin_commute η hN)

/-- The ground projection is the rank-one projection onto the product
bond vector. Source: arXiv:1010.3732, Sections II.D.2 and II.F.2. -/
theorem bondProductParentHamiltonian_groundProjector
    (η : Fin q → ℂ) (hN : 1 ≤ N) :
    (List.ofFn fun i : Fin N =>
      (1 : EuclideanSpace ℂ (Fin N → Fin q) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin N → Fin q)) - bondPenaltyAtLin η hN i).prod =
      (InnerProductSpace.rankOne ℂ
        (bondProductState η N) (bondProductState η N)).toLinearMap := by
  let e := bondMatrixEquiv q N
  let Q : Fin N → MPOTensor.ChainOperator q N := fun i =>
    MPOTensor.embedLocalOperator 1 N hN i
      (MPOTensor.oneSiteOperator (bondVectorProjection η))
  have hmat (i : Fin N) : 1 - bondPenaltyAt η hN i = Q i := by
    change 1 - (MPOTensor.embedLocalOperatorAlgHom 1 N hN i)
      (MPOTensor.oneSiteOperator (1 - bondVectorProjection η)) =
        (MPOTensor.embedLocalOperatorAlgHom 1 N hN i)
          (MPOTensor.oneSiteOperator (bondVectorProjection η))
    simp only [MPOTensor.oneSiteOperator_eq_reindexAlgEquiv_symm,
      map_sub, map_one]
    abel
  have hlin (i : Fin N) :
      (1 : EuclideanSpace ℂ (Fin N → Fin q) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin N → Fin q)) - bondPenaltyAtLin η hN i =
          e.symm (Q i) := by
    change 1 - e.symm (bondPenaltyAt η hN i) = e.symm (Q i)
    rw [← map_one e.symm, ← map_sub, hmat]
  have hcomm : ∀ i j, Commute (Q i) (Q j) := fun i j =>
    MPOTensor.embedLocalOperator_one_commute hN (bondVectorProjection η) i j
  have hprod : (List.ofFn Q).prod =
      Matrix.vecMulVec (bondProductVector η N) (star (bondProductVector η N)) := by
    rw [listProd_ofFn_eq_noncommProd Q hcomm]
    exact bondProductVectorProjection_eq_localProduct η hN
  calc
    _ = (List.ofFn fun i : Fin N => e.symm (Q i)).prod := by
          simp_rw [hlin]
    _ = e.symm ((List.ofFn Q).prod) := by
          rw [map_list_prod, List.map_ofFn]
          rfl
    _ = Matrix.toEuclideanLin
          (Matrix.vecMulVec (bondProductVector η N)
            (star (bondProductVector η N))) := by
          rw [hprod]
          exact bondMatrixEquiv_symm_eq_toEuclideanLin _
    _ = (InnerProductSpace.rankOne ℂ
          (bondProductState η N) (bondProductState η N)).toLinearMap := by
          have h := InnerProductSpace.symm_toEuclideanLin_rankOne
            (bondProductState η N) (bondProductState η N)
          simpa [bondProductState] using
            (congrArg (Matrix.toEuclideanLin) h).symm

/-- A unit bond vector has a nonzero product state on every nonempty
finite chain. Source: arXiv:1010.3732, Section II.D.2. -/
theorem bondProductState_ne_zero
    (η : Fin q → ℂ) (hη : ∑ x, Complex.normSq (η x) = 1)
    (N : ℕ) : bondProductState η N ≠ 0 := by
  classical
  have hsome : ∃ a : Fin q, η a ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ x : Fin q, Complex.normSq (η x)) = 0 := by
      simp [h]
    linarith
  obtain ⟨a, ha⟩ := hsome
  intro hzero
  have heval := congrArg
    (fun v : EuclideanSpace ℂ (Fin N → Fin q) => v (fun _ => a)) hzero
  have hp : (∏ _i : Fin N, η a) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (by intro i hi; exact ha)
  apply hp
  simpa [bondProductState, bondProductVector, PiLp.toLp_apply] using heval

/-- The normalized independent-bond parent Hamiltonian has exactly the
product bond state as its ground line. Source: arXiv:1010.3732,
Sections II.D.2 and II.F.2. -/
theorem bondProductParentHamiltonian_groundSpace_eq_span
    (η : Fin q → ℂ) (hη : ∑ x, Complex.normSq (η x) = 1)
    (hN : 1 ≤ N) :
    LinearMap.ker (bondProductParentHamiltonianLin η hN) =
      Submodule.span ℂ {bondProductState η N} := by
  rw [← bondProductParentHamiltonian_groundSpace η hη hN,
    bondProductParentHamiltonian_groundProjector]
  rw [InnerProductSpace.toLinearMap_rankOne]
  apply LinearMap.range_smulRight_apply
  intro hzero
  have hval := LinearMap.congr_fun hzero (bondProductState η N)
  have hi : ⟪bondProductState η N, bondProductState η N⟫_ℂ = 0 := by
    simpa using hval
  exact bondProductState_ne_zero η hη N (inner_self_eq_zero.mp hi)

/-- The normalized interpolating two-leg bond in one-index coordinates.
Source: arXiv:1010.3732, Section II.F.2, equation `eq:sym:omega-gamma`. -/
noncomputable def normalizedBondInterpolationVector
    (D₀ D₁ : ℕ) (γ : ℝ) : Fin ((D₀ + D₁) * (D₀ + D₁)) → ℂ :=
  fun x => normalizedBondInterpolationMatrix D₀ D₁ γ
    (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2

/-- The interpolating bond has unit norm in the one-index coordinates.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedBondInterpolationVector_sum_normSq
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    (∑ x, Complex.normSq (normalizedBondInterpolationVector D₀ D₁ γ x)) = 1 := by
  classical
  rw [← Equiv.sum_comp finProdFinEquiv]
  simpa [normalizedBondInterpolationVector, Fintype.sum_prod_type] using
    normalizedBondInterpolationMatrix_sum_normSq h₀ h₁ γ

/-- Uniform gap of the commuting parent Hamiltonian for the normalized
interpolating bonds. The Hilbert space here is the regrouped product of
independent bonds. Source: arXiv:1010.3732, Section II.F.2. -/
theorem normalizedBondInterpolation_parent_gap_one
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ)
    {N : ℕ} (hN : 1 ≤ N)
    (v : EuclideanSpace ℂ
      (Fin N → Fin ((D₀ + D₁) * (D₀ + D₁)))) :
    (⟪bondProductParentHamiltonianLin
      (normalizedBondInterpolationVector D₀ D₁ γ) hN v, v⟫_ℂ).re ≤
      (⟪bondProductParentHamiltonianLin
        (normalizedBondInterpolationVector D₀ D₁ γ) hN v,
        bondProductParentHamiltonianLin
          (normalizedBondInterpolationVector D₀ D₁ γ) hN v⟫_ℂ).re :=
  bondProductParentHamiltonian_gap_one _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) hN v

/-- The normalized interpolating bond has the product bond state as its
unique ground line in independent-bond coordinates. Source:
arXiv:1010.3732, Section II.F.2. -/
theorem normalizedBondInterpolation_parent_groundSpace_eq_span
    {D₀ D₁ : ℕ} (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    LinearMap.ker (bondProductParentHamiltonianLin
      (normalizedBondInterpolationVector D₀ D₁ γ) hN) =
      Submodule.span ℂ
        {bondProductState (normalizedBondInterpolationVector D₀ D₁ γ) N} :=
  bondProductParentHamiltonian_groundSpace_eq_span _
    (normalizedBondInterpolationVector_sum_normSq h₀ h₁ γ) hN

end MPSTensor
