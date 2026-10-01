/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommonKernelGapInterpolation
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral gap along an ordered interpolation

A positive quadratic-form bound on the orthogonal complement of the kernel
bounds every nonzero eigenvalue of a positive matrix. Combined with the
common-kernel interpolation theorem, this gives a uniform spectral bound
along an ordered path of finite Hamiltonians.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

/-- The matrix eigenvector equation in Euclidean-space coordinates. -/
lemma IsHermitian.toEuclideanLin_eigenvectorBasis
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i) =
      (hM.eigenvalues i : ℂ) • (hM.eigenvectorBasis i) := by
  apply PiLp.ext
  intro j
  change (M *ᵥ (hM.eigenvectorBasis i).ofLp) j =
    (((hM.eigenvalues i : ℂ) • hM.eigenvectorBasis i).ofLp) j
  simpa using congrFun (hM.mulVec_eigenvectorBasis i) j

/-- A spectral gap above zero bounds the quadratic form on the orthogonal
complement of the kernel. -/
theorem orthogonal_quadratic_gap_of_spectrum_separated
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hHermitian : M.IsHermitian) {δ : ℝ}
    (hSpec : ∀ z ∈ spectrum ℂ M, z.re = 0 ∨ δ ≤ z.re) :
    ∀ x : EuclideanSpace ℂ n,
      x ∈ (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ →
      δ * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)).re := by
  classical
  let hM := hHermitian
  let b := hM.eigenvectorBasis
  let L := Matrix.toEuclideanLin M
  have hSym : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  intro x hx
  have hcoord (i : n) : b.repr (L x) i =
      (hM.eigenvalues i : ℂ) * b.repr x i := by
    calc
      b.repr (L x) i = ⟪b i, L x⟫_ℂ := b.repr_apply_apply (L x) i
      _ = ⟪L (b i), x⟫_ℂ := (hSym (b i) x).symm
      _ = (hM.eigenvalues i : ℂ) * b.repr x i := by
        rw [show L (b i) = (hM.eigenvalues i : ℂ) • b i from
          hM.toEuclideanLin_eigenvectorBasis i]
        rw [inner_smul_left (b i) x (hM.eigenvalues i : ℂ)]
        simp [b.repr_apply_apply]
  have hnorm : (∑ i, Complex.normSq (x i)) =
      ∑ i, Complex.normSq (b.repr x i) := by
    calc
      (∑ i, Complex.normSq (x i)) = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp_rw [Complex.normSq_eq_norm_sq]
      _ = ‖b.repr x‖ ^ 2 := by rw [b.repr.norm_map]
      _ = ∑ i, Complex.normSq (b.repr x i) := by
        rw [EuclideanSpace.norm_sq_eq]
        simp_rw [Complex.normSq_eq_norm_sq]
  have hform : (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)).re =
      ∑ i, hM.eigenvalues i * Complex.normSq (b.repr x i) := by
    have hc : ⟪x, L x⟫_ℂ =
        ∑ i, (hM.eigenvalues i : ℂ) *
          (Complex.normSq (b.repr x i) : ℂ) := by
      calc
        ⟪x, L x⟫_ℂ = ⟪b.repr x, b.repr (L x)⟫_ℂ :=
          (b.repr.inner_map_map x (L x)).symm
        _ = ∑ i, (hM.eigenvalues i : ℂ) *
            (Complex.normSq (b.repr x i) : ℂ) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct]
          simp_rw [dotProduct, hcoord]
          simp [mul_assoc, Complex.mul_conj]
    have hleft : (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)).re =
        (⟪x, L x⟫_ℂ).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)).re =
        ((M *ᵥ x.ofLp) ⬝ᵥ star x.ofLp).re
      rw [dotProduct_comm]
    rw [hleft, hc]
    simp
  have hbound (i : n) : δ * Complex.normSq (b.repr x i) ≤
      hM.eigenvalues i * Complex.normSq (b.repr x i) := by
    have hs : (hM.eigenvalues i : ℂ) ∈ spectrum ℂ M := by
      rw [hM.spectrum_eq_image_range]
      exact ⟨hM.eigenvalues i, ⟨i, rfl⟩, rfl⟩
    rcases hSpec _ hs with hzero | hδ
    · have hz : hM.eigenvalues i = 0 := by simpa using hzero
      have hb : b i ∈ LinearMap.ker L := by
        rw [LinearMap.mem_ker, hM.toEuclideanLin_eigenvectorBasis]
        simp [hz]
      have hinner := Submodule.inner_right_of_mem_orthogonal hb hx
      have hc0 : b.repr x i = 0 := by
        simpa [b.repr_apply_apply] using hinner
      simp [hc0]
    · have hδ' : δ ≤ hM.eigenvalues i := by simpa using hδ
      exact mul_le_mul_of_nonneg_right hδ' (Complex.normSq_nonneg _)
  rw [hnorm, hform, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => hbound i)

/-- A positive semidefinite matrix with a quadratic-form gap above its kernel
has no spectral values strictly between zero and the gap. -/
theorem spectrum_separated_of_orthogonal_quadratic_gap
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hPos : M.PosSemidef) {δ : ℝ}
    (hGap : ∀ x : EuclideanSpace ℂ n,
      x ∈ (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ →
      δ * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)).re) :
    ∀ z ∈ spectrum ℂ M, 0 ≤ z.re ∧ (z.re = 0 ∨ δ ≤ z.re) := by
  classical
  let hM := hPos.isHermitian
  have hSym : (Matrix.toEuclideanLin M).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  intro z hz
  rw [hM.spectrum_eq_image_range] at hz
  obtain ⟨r, ⟨i, rfl⟩, rfl⟩ := hz
  let v := hM.eigenvectorBasis i
  have hnorm : ‖v‖ = 1 := hM.eigenvectorBasis.orthonormal.norm_eq_one i
  have hlin : Matrix.toEuclideanLin M v = (hM.eigenvalues i : ℂ) • v :=
    hM.toEuclideanLin_eigenvectorBasis i
  have hnonneg : 0 ≤ hM.eigenvalues i := hPos.eigenvalues_nonneg i
  constructor
  · simp [hnonneg]
  · by_cases hzero : hM.eigenvalues i = 0
    · left
      simp [hzero]
    · right
      have hmem : v ∈ (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ := by
        rw [LinearMap.orthogonal_ker, hSym.adjoint_eq]
        refine ⟨(hM.eigenvalues i : ℂ)⁻¹ • v, ?_⟩
        rw [map_smul, hlin]
        have hzeroC : (hM.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast hzero
        change ((hM.eigenvalues i : ℂ)⁻¹ •
          ((hM.eigenvalues i : ℂ) • v)) = v
        rw [smul_smul, inv_mul_cancel₀ hzeroC, one_smul]
      have hsum : (∑ j, Complex.normSq (v j)) = 1 := by
        simp_rw [Complex.normSq_eq_norm_sq]
        rw [← EuclideanSpace.norm_sq_eq, hnorm]
        norm_num
      have hdot : star v.ofLp ⬝ᵥ v.ofLp = (1 : ℂ) := by
        calc
          star v.ofLp ⬝ᵥ v.ofLp = v.ofLp ⬝ᵥ star v.ofLp := dotProduct_comm _ _
          _ = ⟪v, v⟫_ℂ := (EuclideanSpace.inner_eq_star_dotProduct v v).symm
          _ = 1 := by rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num
      have hmulvec : M *ᵥ v.ofLp = (hM.eigenvalues i : ℂ) • v.ofLp := by
        funext j
        have hj := congrArg (fun w : EuclideanSpace ℂ n => w j) hlin
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hj
      have hval : (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)).re = hM.eigenvalues i := by
        rw [hmulvec, dotProduct_smul, hdot]
        simp
      have hg := hGap v hmem
      rw [hsum, mul_one, hval] at hg
      exact hg

/-- The ordered interpolation has the same zero eigenspace and a uniform
spectral lower bound away from it. The parameter need only be nonnegative. -/
theorem spectrum_gap_interpolation_of_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hAB : A ≤ B)
    (hker : ∀ x : n → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0)
    (δ t : ℝ) (ht : 0 ≤ t)
    (hgap : ∀ x : EuclideanSpace ℂ n,
      x ∈ (LinearMap.ker (Matrix.toEuclideanLin A))ᗮ →
      δ * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)).re) :
    let C := A + t • (B - A)
    (LinearMap.ker (Matrix.toEuclideanLin C) =
      LinearMap.ker (Matrix.toEuclideanLin A)) ∧
    ∀ z ∈ spectrum ℂ C, 0 ≤ z.re ∧ (z.re = 0 ∨ δ ≤ z.re) := by
  dsimp only
  obtain ⟨hC, hkerEq, hquad⟩ := gap_interpolation_of_le A B hA hAB hker δ t ht hgap
  exact ⟨hkerEq, spectrum_separated_of_orthogonal_quadratic_gap _ hC hquad⟩

/-- A nonzero common zero mode gives zero as an eigenvalue throughout the
ordered interpolation, in addition to the uniform spectral gap. -/
theorem spectrum_gap_interpolation_of_le_of_nontrivial_kernel
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hAB : A ≤ B)
    (hker : ∀ x : n → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0)
    (δ t : ℝ) (ht : 0 ≤ t)
    (hgap : ∀ x : EuclideanSpace ℂ n,
      x ∈ (LinearMap.ker (Matrix.toEuclideanLin A))ᗮ →
      δ * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)).re)
    (hzero : ∃ x : EuclideanSpace ℂ n,
      x ≠ 0 ∧ Matrix.toEuclideanLin A x = 0) :
    let C := A + t • (B - A)
    (0 : ℂ) ∈ spectrum ℂ C ∧
    ∀ z ∈ spectrum ℂ C, 0 ≤ z.re ∧ (z.re = 0 ∨ δ ≤ z.re) := by
  dsimp only
  obtain ⟨hkerEq, hspec⟩ :=
    spectrum_gap_interpolation_of_le A B hA hAB hker δ t ht hgap
  obtain ⟨x, hx, hxA⟩ := hzero
  have hxC : x ∈ LinearMap.ker (Matrix.toEuclideanLin (A + t • (B - A))) := by
    rw [hkerEq]
    exact LinearMap.mem_ker.mpr hxA
  constructor
  · rw [← Matrix.spectrum_toLpLin (p := 2)]
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
    rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
    intro hbot
    rw [hbot] at hxC
    exact hx (by simpa using hxC)
  · exact hspec

end Matrix
