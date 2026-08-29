/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryEntries
import TNLean.MPS.MPDO.NonCartesianActiveSectorCandidate

/-!
# Rigidity of the non-Cartesian sector tensor

The simple spectra of two physical slices force both tensor factors in every
physical-sector decomposition of the candidate to be one-dimensional.

This construction concerns arXiv:1606.00608, Appendix C.2,
Proposition `prop2to3`, lines 1740--1782.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

noncomputable section

namespace MPOTensor.NonCartesianActiveSectorCandidate

/-! ### Constraints on an arbitrary physical-sector factorization -/

/-- The `(0,0)` virtual slice is a nonzero scalar matrix. -/
lemma physicalSlice_zero_zero :
    physicalSlice tensor 0 0 = (1 / 4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physicalSlice, tensor, sectorMatrix, leftPairing, rightPairing]

/-- The `(1,0)` virtual slice has four distinct diagonal entries. -/
lemma physicalSlice_one_zero :
    physicalSlice tensor 1 0 =
      Matrix.diagonal ![(1 / 4 : ℂ), 1 / 2, -7 / 4, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physicalSlice, tensor, sectorMatrix, leftPairing, rightPairing] <;>
    ring

/-- The `(0,1)` virtual slice has four distinct diagonal entries. -/
lemma physicalSlice_zero_one :
    physicalSlice tensor 0 1 =
      Matrix.diagonal ![(-3 / 100 : ℂ), -1 / 100, 1 / 100, 3 / 100] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physicalSlice, tensor, sectorMatrix, leftPairing, rightPairing]

/-- In every factorization of the candidate, the zero--zero factors have
scalar Kronecker product `(1/4) I`. -/
lemma zero_zero_block_of_factorization
    (F : PhysicalSectorFactorization tensor) (k : Fin F.sectorCount) :
    Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (F.leftTensor k 0)
        (F.rightTensor k 0) =
      (1 / 4 : ℂ) •
        (1 : Matrix (Fin (F.leftDim k) × Fin (F.rightDim k))
          (Fin (F.leftDim k) × Fin (F.rightDim k)) ℂ) := by
  have hU := F.physicalIsometry_mul_conjTranspose
  have hfac := F.factorization 0 0
  rw [physicalSlice_zero_zero, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU] at hfac
  ext x y
  have hentry := congrFun (congrFun hfac ⟨k, x⟩) ⟨k, y⟩
  by_cases hxy : x = y
  · subst y
    simpa [Matrix.reindex_apply, Matrix.blockDiagonal'_apply_eq] using hentry.symm
  · have hpre : F.sectorEquiv.symm ⟨k, x⟩ ≠ F.sectorEquiv.symm ⟨k, y⟩ := by
      intro h
      exact hxy (eq_of_heq (Sigma.mk.inj_iff.mp (F.sectorEquiv.symm.injective h)).2)
    simpa [Matrix.reindex_apply, Matrix.blockDiagonal'_apply_eq, hxy, hpre]
      using hentry.symm

/-- The two factors of a nonzero scalar Kronecker product are themselves
nonzero scalar matrices. -/
lemma zero_factors_scalar
    (F : PhysicalSectorFactorization tensor) (k : Fin F.sectorCount) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧
      F.leftTensor k 0 = a • 1 ∧ F.rightTensor k 0 = b • 1 ∧
      a * b = 1 / 4 := by
  let x₀ : Fin (F.leftDim k) := ⟨0, F.leftDim_pos k⟩
  let y₀ : Fin (F.rightDim k) := ⟨0, F.rightDim_pos k⟩
  let a := F.leftTensor k 0 x₀ x₀
  let b := F.rightTensor k 0 y₀ y₀
  have hblock := zero_zero_block_of_factorization F k
  have hab : a * b = 1 / 4 := by
    have h := congrFun (congrFun hblock (x₀, y₀)) (x₀, y₀)
    simpa [a, b, Matrix.kroneckerMap_apply] using h
  have ha : a ≠ 0 := fun ha ↦ by
    rw [ha, zero_mul] at hab
    norm_num at hab
  have hb : b ≠ 0 := fun hb ↦ by
    rw [hb, mul_zero] at hab
    norm_num at hab
  refine ⟨a, b, ha, hb, ?_, ?_, hab⟩
  · ext x x'
    have h := congrFun (congrFun hblock (x, y₀)) (x', y₀)
    by_cases hxx : x = x'
    · subst x'
      apply mul_right_cancel₀ hb
      simpa [a, b, Matrix.kroneckerMap_apply, hab] using h
    · have hzero : F.leftTensor k 0 x x' * b = 0 := by
        simpa [b, Matrix.kroneckerMap_apply, hxx] using h
      simpa [hxx] using (mul_eq_zero.mp hzero).resolve_right hb
  · ext y y'
    have h := congrFun (congrFun hblock (x₀, y)) (x₀, y')
    by_cases hyy : y = y'
    · subst y'
      apply mul_left_cancel₀ ha
      simpa [a, b, Matrix.kroneckerMap_apply, hab] using h
    · have hzero : a * F.rightTensor k 0 y y' = 0 := by
        simpa [a, Matrix.kroneckerMap_apply, hyy] using h
      simpa [hyy] using (mul_eq_zero.mp hzero).resolve_left ha

/-- The compression of a matrix in sector coordinates to one sector. -/
def sectorBlock (F : PhysicalSectorFactorization tensor)
    (M : Matrix (Σ k, F.SectorIndex k) (Σ k, F.SectorIndex k) ℂ)
    (k : Fin F.sectorCount) : Matrix (F.SectorIndex k) (F.SectorIndex k) ℂ :=
  M.submatrix (fun x ↦ ⟨k, x⟩) (fun x ↦ ⟨k, x⟩)

/-- After scaling its eigenvalues to `1,2,-7,4`, the left observable acts
trivially on the right coordinate of every sector. -/
lemma left_observable_block
    (F : PhysicalSectorFactorization tensor) (k : Fin F.sectorCount) :
    ∃ X : Matrix (Fin (F.leftDim k)) (Fin (F.leftDim k)) ℂ,
      sectorBlock F ((4 : ℂ) • F.transformedPhysicalSlice 1 0) k =
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) X 1 := by
  obtain ⟨a, b, ha, hb, hleft, hright, hab⟩ := zero_factors_scalar F k
  refine ⟨(4 : ℂ) • b • F.leftTensor k 1, ?_⟩
  ext x y
  simp only [sectorBlock, Matrix.submatrix_apply, Matrix.smul_apply]
  rw [F.transformedPhysicalSlice_eq, Matrix.blockDiagonal'_apply_eq]
  simp only [Matrix.kroneckerMap_apply]
  rw [hright]
  simp only [Matrix.smul_apply]
  ring

/-- After scaling its eigenvalues to `-3,-1,1,3`, the right observable acts
trivially on the left coordinate of every sector. -/
lemma right_observable_block
    (F : PhysicalSectorFactorization tensor) (k : Fin F.sectorCount) :
    ∃ X : Matrix (Fin (F.rightDim k)) (Fin (F.rightDim k)) ℂ,
      sectorBlock F ((100 : ℂ) • F.transformedPhysicalSlice 0 1) k =
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) 1 X := by
  obtain ⟨a, b, ha, hb, hleft, hright, hab⟩ := zero_factors_scalar F k
  refine ⟨(100 : ℂ) • a • F.rightTensor k 1, ?_⟩
  ext x y
  simp only [sectorBlock, Matrix.submatrix_apply, Matrix.smul_apply]
  rw [F.transformedPhysicalSlice_eq, Matrix.blockDiagonal'_apply_eq]
  simp only [Matrix.kroneckerMap_apply]
  rw [hleft]
  simp only [Matrix.smul_apply]
  ring

/-- The cubic Lagrange factor associated with three excluded eigenvalues. -/
def cubicProjection {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (u v w denominator : ℂ) : Matrix n n ℂ :=
  denominator⁻¹ •
    ((M - u • 1) * (M - v • 1) * (M - w • 1))

/-- A cubic Lagrange factor of a diagonal matrix is computed pointwise. -/
lemma cubicProjection_diagonal {n : Type} [Fintype n] [DecidableEq n]
    (f : n → ℂ) (u v w denominator : ℂ) :
    cubicProjection (Matrix.diagonal f) u v w denominator =
      Matrix.diagonal (fun i ↦
        denominator⁻¹ * ((f i - u) * (f i - v) * (f i - w))) := by
  have hsub (z : ℂ) :
      Matrix.diagonal f - z • 1 = Matrix.diagonal (fun i ↦ f i - z) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [cubicProjection, hsub, hsub, hsub,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Cubic Lagrange factors commute with unitary conjugation. -/
lemma cubicProjection_conjugate {n : Type} [Fintype n] [DecidableEq n]
    (U M : Matrix n n ℂ) (u v w denominator : ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    cubicProjection (U * M * Uᴴ) u v w denominator =
      U * cubicProjection M u v w denominator * Uᴴ := by
  have hfactor (z : ℂ) :
      U * M * Uᴴ - z • 1 = U * (M - z • 1) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp [Matrix.mul_assoc, hright]
  rw [cubicProjection, cubicProjection]
  rw [hfactor, hfactor, hfactor]
  have hproduct :
      (U * (M - u • 1) * Uᴴ) * (U * (M - v • 1) * Uᴴ) *
          (U * (M - w • 1) * Uᴴ) =
        U * ((M - u • 1) * (M - v • 1) * (M - w • 1)) * Uᴴ := by
    calc
      _ = U * (M - u • 1) * (Uᴴ * U) * (M - v • 1) *
          (Uᴴ * U) * (M - w • 1) * Uᴴ := by noncomm_ring
      _ = _ := by rw [hleft]; simp only [mul_one]; noncomm_ring
  rw [hproduct]
  simp

/-- Reindexing both matrix coordinates commutes with cubic Lagrange factors. -/
lemma cubicProjection_reindex {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) (M : Matrix m m ℂ)
    (u v w denominator : ℂ) :
    cubicProjection (Matrix.reindex e e M) u v w denominator =
      Matrix.reindex e e (cubicProjection M u v w denominator) := by
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  change cubicProjection (E M) u v w denominator =
    E (cubicProjection M u v w denominator)
  simp only [cubicProjection, map_smul, map_mul, map_sub, map_one]

/-- First excluded eigenvalue for the four left spectral projectors. -/
def leftExcluded₁ : Fin 4 → ℂ := ![2, 1, 1, 1]

/-- Second excluded eigenvalue for the four left spectral projectors. -/
def leftExcluded₂ : Fin 4 → ℂ := ![-7, -7, 2, 2]

/-- Third excluded eigenvalue for the four left spectral projectors. -/
def leftExcluded₃ : Fin 4 → ℂ := ![4, 4, 4, -7]

/-- Vandermonde denominators for the four left spectral projectors. -/
def leftDenominator : Fin 4 → ℂ := ![24, -18, -792, 66]

/-- The four cubic spectral projectors for an operator with ordered spectrum
`1,2,-7,4`. -/
def leftSpectralProjection {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (p : Fin 4) : Matrix n n ℂ :=
  cubicProjection M (leftExcluded₁ p) (leftExcluded₂ p)
    (leftExcluded₃ p) (leftDenominator p)

/-- On the untransformed left observable, the cubic projectors are the four
coordinate projections. -/
lemma leftSpectralProjection_base (p : Fin 4) :
    leftSpectralProjection ((4 : ℂ) • physicalSlice tensor 1 0) p =
      Matrix.diagonal (fun i ↦ if i = p then (1 : ℂ) else 0) := by
  rw [physicalSlice_one_zero]
  have hscale :
      (4 : ℂ) • Matrix.diagonal ![(1 / 4 : ℂ), 1 / 2, -7 / 4, 1] =
        Matrix.diagonal (fun i ↦
          4 * ![(1 / 4 : ℂ), 1 / 2, -7 / 4, 1] i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hscale]
  rw [leftSpectralProjection, cubicProjection_diagonal]
  ext i j
  fin_cases p <;> fin_cases i <;> fin_cases j <;>
    norm_num [leftExcluded₁, leftExcluded₂, leftExcluded₃,
      leftDenominator]

/-- The rank-one physical projection corresponding to the `p`-th left
eigenvalue, written in sector coordinates. -/
def transformedCoordinateProjection (F : PhysicalSectorFactorization tensor)
    (p : Fin 4) :
    Matrix (Σ k, F.SectorIndex k) (Σ k, F.SectorIndex k) ℂ :=
  Matrix.reindex F.sectorEquiv F.sectorEquiv
    (F.physicalIsometry *
      Matrix.diagonal (fun i ↦ if i = p then (1 : ℂ) else 0) *
        F.physicalIsometryᴴ)

/-- The cubic projectors of the transformed left observable are precisely
the transformed coordinate projections. -/
lemma leftSpectralProjection_transformed
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    leftSpectralProjection ((4 : ℂ) • F.transformedPhysicalSlice 1 0) p =
      transformedCoordinateProjection F p := by
  have hobs :
      (4 : ℂ) • F.transformedPhysicalSlice 1 0 =
        Matrix.reindex F.sectorEquiv F.sectorEquiv
          (F.physicalIsometry * ((4 : ℂ) • physicalSlice tensor 1 0) *
            F.physicalIsometryᴴ) := by
    have hin :
        F.physicalIsometry * ((4 : ℂ) • physicalSlice tensor 1 0) *
            F.physicalIsometryᴴ =
          (4 : ℂ) • (F.physicalIsometry * physicalSlice tensor 1 0 *
            F.physicalIsometryᴴ) := by
      simp
    rw [hin]
    ext i j
    rfl
  rw [hobs]
  rw [leftSpectralProjection, cubicProjection_reindex]
  rw [cubicProjection_conjugate _ _ _ _ _ _
    F.physicalIsometry_isometry F.physicalIsometry_mul_conjTranspose]
  rw [← leftSpectralProjection, leftSpectralProjection_base]
  rfl

/-- Entries of a transformed coordinate projection are outer products of one
column of the physical isometry. -/
lemma transformedCoordinateProjection_apply
    (F : PhysicalSectorFactorization tensor) (p : Fin 4)
    (x y : Σ k, F.SectorIndex k) :
    transformedCoordinateProjection F p x y =
      F.physicalIsometry (F.sectorEquiv.symm x) p *
        star (F.physicalIsometry (F.sectorEquiv.symm y) p) := by
  have hmul :
      F.physicalIsometry *
          Matrix.diagonal (fun i ↦ if i = p then (1 : ℂ) else 0) =
        Matrix.of fun i j ↦
          F.physicalIsometry i j * if j = p then (1 : ℂ) else 0 := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [transformedCoordinateProjection, hmul]
  simp [Matrix.reindex_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Every two-by-two minor of a transformed coordinate projection vanishes. -/
lemma transformedCoordinateProjection_minor_zero
    (F : PhysicalSectorFactorization tensor) (p : Fin 4)
    (x₁ x₂ y₁ y₂ : Σ k, F.SectorIndex k) :
    transformedCoordinateProjection F p x₁ y₁ *
        transformedCoordinateProjection F p x₂ y₂ =
      transformedCoordinateProjection F p x₁ y₂ *
        transformedCoordinateProjection F p x₂ y₁ := by
  rw [transformedCoordinateProjection_apply,
    transformedCoordinateProjection_apply,
    transformedCoordinateProjection_apply,
    transformedCoordinateProjection_apply]
  ring

/-- A chosen left-coordinate matrix for each block of an arbitrary
factorization. -/
noncomputable def leftBlockFactor (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) :
    Matrix (Fin (F.leftDim k)) (Fin (F.leftDim k)) ℂ :=
  Classical.choose (left_observable_block F k)

/-- The chosen left-coordinate matrix realizes its observable block. -/
lemma leftBlockFactor_spec (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) :
    sectorBlock F ((4 : ℂ) • F.transformedPhysicalSlice 1 0) k =
      Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (leftBlockFactor F k)
        (1 : Matrix (Fin (F.rightDim k)) (Fin (F.rightDim k)) ℂ) :=
  Classical.choose_spec (left_observable_block F k)

/-- The transformed left observable is the direct sum of its chosen
left-coordinate matrices tensored with right identities. -/
lemma left_observable_eq_blockDiagonal
    (F : PhysicalSectorFactorization tensor) :
    (4 : ℂ) • F.transformedPhysicalSlice 1 0 =
      Matrix.blockDiagonal' fun k ↦
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (leftBlockFactor F k)
          (1 : Matrix (Fin (F.rightDim k)) (Fin (F.rightDim k)) ℂ) := by
  ext q r
  obtain ⟨k, x⟩ := q
  obtain ⟨h, y⟩ := r
  by_cases hkh : k = h
  · subst h
    have hentry := congrFun (congrFun (leftBlockFactor_spec F k) x) y
    simpa [sectorBlock] using hentry
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    simp [F.transformedPhysicalSlice_eq,
      Matrix.blockDiagonal'_apply_ne _ _ _ hkh]

/-- Cubic Lagrange factors are computed independently on the blocks of a
dependent direct sum. -/
lemma cubicProjection_blockDiagonal {o : Type} [Fintype o] [DecidableEq o]
    {n : o → Type} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (M : (k : o) → Matrix (n k) (n k) ℂ) (u v w denominator : ℂ) :
    cubicProjection (Matrix.blockDiagonal' M) u v w denominator =
      Matrix.blockDiagonal' fun k ↦ cubicProjection (M k) u v w denominator := by
  rw [cubicProjection]
  rw [← Matrix.blockDiagonal'_one]
  rw [← Matrix.blockDiagonal'_smul, ← Matrix.blockDiagonal'_smul,
    ← Matrix.blockDiagonal'_smul]
  rw [← Matrix.blockDiagonal'_sub, ← Matrix.blockDiagonal'_sub,
    ← Matrix.blockDiagonal'_sub]
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  rw [← Matrix.blockDiagonal'_smul]
  rfl

/-- A cubic Lagrange factor of `X ⊗ I` again acts trivially on the second
coordinate. -/
lemma cubicProjection_kronecker_one {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m m ℂ)
    (u v w denominator : ℂ) :
    cubicProjection
        (Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) X
          (1 : Matrix n n ℂ)) u v w denominator =
      Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
        (cubicProjection X u v w denominator) (1 : Matrix n n ℂ) := by
  have hfactor (z : ℂ) :
      Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) X (1 : Matrix n n ℂ) -
          z • 1 =
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (X - z • 1)
          (1 : Matrix n n ℂ) := by
    ext x y
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
      simp [Matrix.kroneckerMap_apply, h₁, h₂]
  rw [cubicProjection, cubicProjection, hfactor, hfactor, hfactor]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  rw [← Matrix.smul_kronecker]

/-- Each transformed coordinate projection acts trivially on the right
coordinate within every sector. -/
lemma transformedCoordinateProjection_eq_blockDiagonal_left
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    transformedCoordinateProjection F p =
      Matrix.blockDiagonal' fun k ↦
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
          (leftSpectralProjection (leftBlockFactor F k) p)
          (1 : Matrix (Fin (F.rightDim k)) (Fin (F.rightDim k)) ℂ) := by
  rw [← leftSpectralProjection_transformed]
  rw [left_observable_eq_blockDiagonal]
  rw [leftSpectralProjection, cubicProjection_blockDiagonal]
  congr 1
  funext k
  exact cubicProjection_kronecker_one _ _ _ _ _

/-- Pairwise simplicity of the left observable forces every right factor in
an arbitrary physical-sector factorization to be one-dimensional. -/
lemma rightDim_eq_one (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) : F.rightDim k = 1 := by
  by_contra hne
  have hpos := F.rightDim_pos k
  have hdim : 1 < F.rightDim k := by omega
  let x₀ : Fin (F.leftDim k) := ⟨0, F.leftDim_pos k⟩
  let y₀ : Fin (F.rightDim k) := ⟨0, F.rightDim_pos k⟩
  let y₁ : Fin (F.rightDim k) := ⟨1, hdim⟩
  let q₀ : Σ h, F.SectorIndex h := ⟨k, (x₀, y₀)⟩
  let q₁ : Σ h, F.SectorIndex h := ⟨k, (x₀, y₁)⟩
  let i := F.sectorEquiv.symm q₀
  have hsum :
      ∑ p, F.physicalIsometry i p * star (F.physicalIsometry i p) = 1 := by
    simpa using Matrix.sum_mul_star_eq_ite_of_mul_conjTranspose_eq_one
      F.physicalIsometry F.physicalIsometry_mul_conjTranspose i i
  have hsum_ne :
      (∑ p, F.physicalIsometry i p * star (F.physicalIsometry i p)) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨p, hp_mem, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hpU : F.physicalIsometry i p ≠ 0 := by
    intro hzero
    apply hp
    simp [hzero]
  let P := transformedCoordinateProjection F p
  let Y := leftSpectralProjection (leftBlockFactor F k) p
  have hP := transformedCoordinateProjection_eq_blockDiagonal_left F p
  have hdiag₀ : P q₀ q₀ = Y x₀ x₀ := by
    have h := congrFun (congrFun hP q₀) q₀
    simpa [P, Y, q₀, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hdiag₁ : P q₁ q₁ = Y x₀ x₀ := by
    have h := congrFun (congrFun hP q₁) q₁
    simpa [P, Y, q₁, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hoff₀₁ : P q₀ q₁ = 0 := by
    have h := congrFun (congrFun hP q₀) q₁
    simpa [P, Y, q₀, q₁, y₀, y₁, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hoff₁₀ : P q₁ q₀ = 0 := by
    have h := congrFun (congrFun hP q₁) q₀
    simpa [P, Y, q₀, q₁, y₀, y₁, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hY : Y x₀ x₀ ≠ 0 := by
    rw [← hdiag₀]
    change transformedCoordinateProjection F p q₀ q₀ ≠ 0
    rw [transformedCoordinateProjection_apply]
    simpa [i] using mul_ne_zero hpU (star_ne_zero.mpr hpU)
  have hminor := transformedCoordinateProjection_minor_zero F p q₀ q₁ q₀ q₁
  change P q₀ q₀ * P q₁ q₁ = P q₀ q₁ * P q₁ q₀ at hminor
  rw [hdiag₀, hdiag₁, hoff₀₁, hoff₁₀, mul_zero] at hminor
  exact (mul_ne_zero hY hY) hminor

/-! ### The symmetric right-coordinate argument -/

/-- First excluded eigenvalue for the four right spectral projectors. -/
def rightExcluded₁ : Fin 4 → ℂ := ![-1, -3, -3, -3]

/-- Second excluded eigenvalue for the four right spectral projectors. -/
def rightExcluded₂ : Fin 4 → ℂ := ![1, 1, -1, -1]

/-- Third excluded eigenvalue for the four right spectral projectors. -/
def rightExcluded₃ : Fin 4 → ℂ := ![3, 3, 3, 1]

/-- Vandermonde denominators for the four right spectral projectors. -/
def rightDenominator : Fin 4 → ℂ := ![-48, 16, -16, 48]

/-- The four cubic spectral projectors for an operator with ordered spectrum
`-3,-1,1,3`. -/
def rightSpectralProjection {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (p : Fin 4) : Matrix n n ℂ :=
  cubicProjection M (rightExcluded₁ p) (rightExcluded₂ p)
    (rightExcluded₃ p) (rightDenominator p)

/-- On the untransformed right observable, the cubic projectors are the four
coordinate projections. -/
lemma rightSpectralProjection_base (p : Fin 4) :
    rightSpectralProjection ((100 : ℂ) • physicalSlice tensor 0 1) p =
      Matrix.diagonal (fun i ↦ if i = p then (1 : ℂ) else 0) := by
  rw [physicalSlice_zero_one]
  have hscale :
      (100 : ℂ) •
          Matrix.diagonal ![(-3 / 100 : ℂ), -1 / 100, 1 / 100, 3 / 100] =
        Matrix.diagonal (fun i ↦
          100 * ![(-3 / 100 : ℂ), -1 / 100, 1 / 100, 3 / 100] i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hscale]
  rw [rightSpectralProjection, cubicProjection_diagonal]
  ext i j
  fin_cases p <;> fin_cases i <;> fin_cases j <;>
    norm_num [rightExcluded₁, rightExcluded₂, rightExcluded₃,
      rightDenominator]

/-- The cubic projectors of the transformed right observable are precisely
the transformed coordinate projections. -/
lemma rightSpectralProjection_transformed
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    rightSpectralProjection ((100 : ℂ) • F.transformedPhysicalSlice 0 1) p =
      transformedCoordinateProjection F p := by
  have hobs :
      (100 : ℂ) • F.transformedPhysicalSlice 0 1 =
        Matrix.reindex F.sectorEquiv F.sectorEquiv
          (F.physicalIsometry * ((100 : ℂ) • physicalSlice tensor 0 1) *
            F.physicalIsometryᴴ) := by
    have hin :
        F.physicalIsometry * ((100 : ℂ) • physicalSlice tensor 0 1) *
            F.physicalIsometryᴴ =
          (100 : ℂ) • (F.physicalIsometry * physicalSlice tensor 0 1 *
            F.physicalIsometryᴴ) := by
      simp
    rw [hin]
    ext i j
    rfl
  rw [hobs]
  rw [rightSpectralProjection, cubicProjection_reindex]
  rw [cubicProjection_conjugate _ _ _ _ _ _
    F.physicalIsometry_isometry F.physicalIsometry_mul_conjTranspose]
  rw [← rightSpectralProjection, rightSpectralProjection_base]
  rfl

/-- A chosen right-coordinate matrix for each block of an arbitrary
factorization. -/
noncomputable def rightBlockFactor (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) :
    Matrix (Fin (F.rightDim k)) (Fin (F.rightDim k)) ℂ :=
  Classical.choose (right_observable_block F k)

/-- The chosen right-coordinate matrix realizes its observable block. -/
lemma rightBlockFactor_spec (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) :
    sectorBlock F ((100 : ℂ) • F.transformedPhysicalSlice 0 1) k =
      Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
        (1 : Matrix (Fin (F.leftDim k)) (Fin (F.leftDim k)) ℂ)
        (rightBlockFactor F k) :=
  Classical.choose_spec (right_observable_block F k)

/-- The transformed right observable is the direct sum of left identities
tensored with the chosen right-coordinate matrices. -/
lemma right_observable_eq_blockDiagonal
    (F : PhysicalSectorFactorization tensor) :
    (100 : ℂ) • F.transformedPhysicalSlice 0 1 =
      Matrix.blockDiagonal' fun k ↦
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
          (1 : Matrix (Fin (F.leftDim k)) (Fin (F.leftDim k)) ℂ)
          (rightBlockFactor F k) := by
  ext q r
  obtain ⟨k, x⟩ := q
  obtain ⟨h, y⟩ := r
  by_cases hkh : k = h
  · subst h
    have hentry := congrFun (congrFun (rightBlockFactor_spec F k) x) y
    simpa [sectorBlock] using hentry
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    simp [F.transformedPhysicalSlice_eq,
      Matrix.blockDiagonal'_apply_ne _ _ _ hkh]

/-- A cubic Lagrange factor of `I ⊗ X` again acts trivially on the first
coordinate. -/
lemma cubicProjection_one_kronecker {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix n n ℂ)
    (u v w denominator : ℂ) :
    cubicProjection
        (Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (1 : Matrix m m ℂ) X)
        u v w denominator =
      Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (1 : Matrix m m ℂ)
        (cubicProjection X u v w denominator) := by
  have hfactor (z : ℂ) :
      Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (1 : Matrix m m ℂ) X -
          z • 1 =
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y) (1 : Matrix m m ℂ)
          (X - z • 1) := by
    ext x y
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
      simp [Matrix.kroneckerMap_apply, h₁, h₂]
  rw [cubicProjection, cubicProjection, hfactor, hfactor, hfactor]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [← Matrix.kronecker_smul]

/-- Each transformed coordinate projection acts trivially on the left
coordinate within every sector. -/
lemma transformedCoordinateProjection_eq_blockDiagonal_right
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    transformedCoordinateProjection F p =
      Matrix.blockDiagonal' fun k ↦
        Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
          (1 : Matrix (Fin (F.leftDim k)) (Fin (F.leftDim k)) ℂ)
          (rightSpectralProjection (rightBlockFactor F k) p) := by
  rw [← rightSpectralProjection_transformed]
  rw [right_observable_eq_blockDiagonal]
  rw [rightSpectralProjection, cubicProjection_blockDiagonal]
  congr 1
  funext k
  exact cubicProjection_one_kronecker _ _ _ _ _

/-- Pairwise simplicity of the right observable forces every left factor in
an arbitrary physical-sector factorization to be one-dimensional. -/
lemma leftDim_eq_one (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) : F.leftDim k = 1 := by
  by_contra hne
  have hpos := F.leftDim_pos k
  have hdim : 1 < F.leftDim k := by omega
  let x₀ : Fin (F.leftDim k) := ⟨0, F.leftDim_pos k⟩
  let x₁ : Fin (F.leftDim k) := ⟨1, hdim⟩
  let y₀ : Fin (F.rightDim k) := ⟨0, F.rightDim_pos k⟩
  let q₀ : Σ h, F.SectorIndex h := ⟨k, (x₀, y₀)⟩
  let q₁ : Σ h, F.SectorIndex h := ⟨k, (x₁, y₀)⟩
  let i := F.sectorEquiv.symm q₀
  have hsum :
      ∑ p, F.physicalIsometry i p * star (F.physicalIsometry i p) = 1 := by
    simpa using Matrix.sum_mul_star_eq_ite_of_mul_conjTranspose_eq_one
      F.physicalIsometry F.physicalIsometry_mul_conjTranspose i i
  have hsum_ne :
      (∑ p, F.physicalIsometry i p * star (F.physicalIsometry i p)) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨p, hp_mem, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hpU : F.physicalIsometry i p ≠ 0 := by
    intro hzero
    apply hp
    simp [hzero]
  let P := transformedCoordinateProjection F p
  let Y := rightSpectralProjection (rightBlockFactor F k) p
  have hP := transformedCoordinateProjection_eq_blockDiagonal_right F p
  have hdiag₀ : P q₀ q₀ = Y y₀ y₀ := by
    have h := congrFun (congrFun hP q₀) q₀
    simpa [P, Y, q₀, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hdiag₁ : P q₁ q₁ = Y y₀ y₀ := by
    have h := congrFun (congrFun hP q₁) q₁
    simpa [P, Y, q₁, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hoff₀₁ : P q₀ q₁ = 0 := by
    have h := congrFun (congrFun hP q₀) q₁
    simpa [P, Y, q₀, q₁, x₀, x₁, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hoff₁₀ : P q₁ q₀ = 0 := by
    have h := congrFun (congrFun hP q₁) q₀
    simpa [P, Y, q₀, q₁, x₀, x₁, Matrix.blockDiagonal'_apply_eq,
      Matrix.kroneckerMap_apply] using h
  have hY : Y y₀ y₀ ≠ 0 := by
    rw [← hdiag₀]
    change transformedCoordinateProjection F p q₀ q₀ ≠ 0
    rw [transformedCoordinateProjection_apply]
    simpa [i] using mul_ne_zero hpU (star_ne_zero.mpr hpU)
  have hminor := transformedCoordinateProjection_minor_zero F p q₀ q₁ q₀ q₁
  change P q₀ q₀ * P q₁ q₁ = P q₀ q₁ * P q₁ q₀ at hminor
  rw [hdiag₀, hdiag₁, hoff₀₁, hoff₁₀, mul_zero] at hminor
  exact (mul_ne_zero hY hY) hminor

end MPOTensor.NonCartesianActiveSectorCandidate
