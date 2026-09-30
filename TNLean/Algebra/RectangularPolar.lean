/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-!
# Polar factorization of an injective rectangular complex matrix

The physical map of a one-site injective MPS, with its virtual pair space
as domain, is an injective rectangular matrix. Its right polar factorization
is `P = W Q`, where `Wᴴ W = I` and `Q > 0`. The source uses a left polar
factor on the physical range. The two factors agree on that range through
`Q_left W = W Q`; an ambient left factor can be extended by the identity
on the orthogonal complement.

Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
equation `eq:1d-iso:polardec`. This algebraic factorization alone does not
establish a symmetric gapped path from an arbitrary endpoint.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

/-- A full-column-rank rectangular complex matrix factors into an
isometry and a positive-definite square matrix. The factorization is
the right-polar orientation of Schuch–Pérez-García–Cirac,
arXiv:1010.3732, equation `eq:1d-iso:polardec`. -/
theorem exists_isometric_posDef_factor
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m n ℂ) (hP : Function.Injective P.mulVec) :
    ∃ (Q : Matrix n n ℂ) (W : Matrix m n ℂ),
      Q = CFC.sqrt (Pᴴ * P) ∧ Q.PosDef ∧ Wᴴ * W = 1 ∧ P = W * Q := by
  let G := Pᴴ * P
  have hG : G.PosDef := Matrix.PosDef.conjTranspose_mul_self P hP
  let Q := CFC.sqrt G
  have hQpos : Q.PosDef :=
    Matrix.IsStrictlyPositive.posDef (hG.isStrictlyPositive.sqrt)
  have hQunit : IsUnit Q.det := hG.isUnit_det_cfc_sqrt
  have hQHerm : Qᴴ = Q := Matrix.conjTranspose_cfc_sqrt G
  have hQsq : Q * Q = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  let W : Matrix m n ℂ := P * Q⁻¹
  refine ⟨Q, W, rfl, hQpos, ?_, ?_⟩
  · change (P * Q⁻¹)ᴴ * (P * Q⁻¹) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hQHerm]
    calc
      (Q⁻¹ * Pᴴ) * (P * Q⁻¹) = Q⁻¹ * (Pᴴ * P) * Q⁻¹ := by
        simp [Matrix.mul_assoc]
      _ = Q⁻¹ * (Q * Q) * Q⁻¹ := by rw [hQsq]
      _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQunit]
        simp [Matrix.mul_nonsing_inv Q hQunit]
  · change P = (P * Q⁻¹) * Q
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQunit, Matrix.mul_one]

/-- The positive factor interpolates affinely between the identity and
the original positive factor, as in Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.D.2, equation following
`eq:1d-iso:polardec`. -/
noncomputable def polarInterpolant {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (γ : ℝ) : Matrix n n ℂ :=
  γ • Q + (1 - γ) • 1

/-- The affine positive factor stays strictly positive throughout the
unit interval. This gives an invertible local deformation before any
parent-Hamiltonian gap argument. -/
theorem polarInterpolant_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQ : Q.PosDef) {γ : ℝ}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    (polarInterpolant Q γ).PosDef := by
  have hδ : 0 ≤ 1 - γ := sub_nonneg.mpr hγ₁
  by_cases hzero : γ = 0
  · simp [polarInterpolant, hzero, Matrix.PosDef.one]
  · have hγpos : 0 < γ := lt_of_le_of_ne hγ₀ (Ne.symm hzero)
    exact (hQ.smul hγpos).add_posSemidef
      (Matrix.PosSemidef.one.smul hδ)

/-- An isometric factor followed by a strictly positive factor has full
column rank. In particular, the local polar path remains injective. -/
theorem isometric_mul_posDef_mulVec_injective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {W : Matrix m n ℂ} {Q : Matrix n n ℂ}
    (hW : Wᴴ * W = 1) (hQ : Q.PosDef) :
    Function.Injective (W * Q).mulVec := by
  have hWinj : Function.Injective W.mulVec := by
    intro x y hxy
    have hx : (Wᴴ * W).mulVec x = (Wᴴ * W).mulVec y := by
      simpa only [Matrix.mulVec_mulVec] using congrArg Wᴴ.mulVec hxy
    simpa only [hW, Matrix.one_mulVec] using hx
  have hQinj : Function.Injective Q.mulVec :=
    Matrix.mulVec_injective_of_isUnit hQ.isUnit
  intro x y hxy
  apply hQinj
  apply hWinj
  simpa only [Matrix.mulVec_mulVec] using hxy

@[simp]
theorem polarInterpolant_zero {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) : polarInterpolant Q 0 = 1 := by
  simp [polarInterpolant]

@[simp]
theorem polarInterpolant_one {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) : polarInterpolant Q 1 = Q := by
  simp [polarInterpolant]

/-- The local positive factor depends continuously on the deformation
parameter. -/
theorem continuous_polarInterpolant {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) : Continuous (polarInterpolant Q) := by
  apply continuous_matrix
  intro i j
  simp only [polarInterpolant, Matrix.add_apply, Matrix.smul_apply]
  fun_prop

/-- The polar deformation starts at the isometric factor and ends at the
original injective rectangular map. Positivity of its square factor holds
uniformly over the closed parameter interval; this assertion does not
include a many-body spectral gap. -/
theorem exists_polar_deformation_of_injective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m n ℂ) (hP : Function.Injective P.mulVec) :
    ∃ (Q : Matrix n n ℂ) (W : Matrix m n ℂ),
      Q.PosDef ∧ Wᴴ * W = 1 ∧
      P = W * polarInterpolant Q 1 ∧
      W = W * polarInterpolant Q 0 ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 → (polarInterpolant Q γ).PosDef) ∧
      Continuous (fun γ : ℝ => W * polarInterpolant Q γ) := by
  obtain ⟨Q, W, _, hQ, hW, hPfactor⟩ :=
    exists_isometric_posDef_factor P hP
  refine ⟨Q, W, hQ, hW, ?_, ?_, ?_, ?_⟩
  · simpa using hPfactor
  · simp
  · intro γ hγ₀ hγ₁
    exact polarInterpolant_posDef hQ hγ₀ hγ₁
  · exact (continuous_const : Continuous fun _ : ℝ => W).matrix_mul
      (continuous_polarInterpolant Q)

/-- The Gram matrix of an intertwining rectangular map commutes with the
unitary action on its domain. This is the first symmetry step in the polar
deformation of Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.D.2. -/
theorem gram_commute_of_unitary_intertwining
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Matrix m n ℂ} {U : Matrix m m ℂ} {R : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup m ℂ)
    (hR : R ∈ Matrix.unitaryGroup n ℂ)
    (h : U * P = P * R) : Commute (Pᴴ * P) R := by
  have hUstar : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
  have hRstar : R * Rᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hR
  have hconj : Pᴴ * Uᴴ = Rᴴ * Pᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose h
  have hG : Rᴴ * (Pᴴ * P) * R = Pᴴ * P := by
    calc
      Rᴴ * (Pᴴ * P) * R = (Rᴴ * Pᴴ) * (P * R) := by simp only [Matrix.mul_assoc]
      _ = (Pᴴ * Uᴴ) * (U * P) := by rw [hconj, h]
      _ = Pᴴ * P := by rw [← Matrix.mul_assoc, Matrix.mul_assoc Pᴴ, hUstar]; simp
  rw [commute_iff_eq]
  calc
    (Pᴴ * P) * R = (R * Rᴴ) * ((Pᴴ * P) * R) := by rw [hRstar, one_mul]
    _ = R * (Rᴴ * (Pᴴ * P) * R) := by simp only [Matrix.mul_assoc]
    _ = R * (Pᴴ * P) := by rw [hG]

/-- Taking the positive square root of the Gram matrix preserves its
commutation with the unitary virtual action. Source: arXiv:1010.3732,
Section II.D.2, polar deformation following `eq:1d-iso:polardec`. -/
theorem sqrt_gram_commute_of_unitary_intertwining
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Matrix m n ℂ} {U : Matrix m m ℂ} {R : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup m ℂ)
    (hR : R ∈ Matrix.unitaryGroup n ℂ)
    (h : U * P = P * R) : Commute (CFC.sqrt (Pᴴ * P)) R := by
  exact (gram_commute_of_unitary_intertwining hU hR h).cfcₙ_nnreal NNReal.sqrt

/-- A nonsingular matrix and its nonsingular inverse have the same
commutant. -/
theorem commute_nonsing_inv_left
    {n : Type*} [Fintype n] [DecidableEq n]
    {Q R : Matrix n n ℂ} (hQ : IsUnit Q.det) (h : Commute Q R) :
    Commute Q⁻¹ R := by
  rw [commute_iff_eq] at h ⊢
  calc
    Q⁻¹ * R = Q⁻¹ * (R * Q) * Q⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ, Matrix.mul_one]
    _ = Q⁻¹ * (Q * R) * Q⁻¹ := by rw [h]
    _ = R * Q⁻¹ := by
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ, one_mul]

/-- The affine interpolation of a commuting positive factor commutes with
the same virtual action. -/
theorem polarInterpolant_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    {Q R : Matrix n n ℂ} (h : Commute Q R) (γ : ℝ) :
    Commute (polarInterpolant Q γ) R := by
  rw [commute_iff_eq] at h ⊢
  simp only [polarInterpolant, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, h, one_mul, mul_one]

/-- The right-polar path respects a family of unitary physical and virtual
actions intertwining the original injective map. Source: Schuch–Pérez-García–
Cirac, arXiv:1010.3732, Section II.D.2, equation following
`eq:1d-iso:polardec`. This is a local matrix statement; a uniformly gapped
parent-Hamiltonian path requires a separate argument. -/
theorem exists_equivariant_polar_deformation_of_injective
    {ι : Type*}
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : Matrix m n ℂ) (hP : Function.Injective P.mulVec)
    (U : ι → Matrix m m ℂ) (R : ι → Matrix n n ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup m ℂ)
    (hR : ∀ g, R g ∈ Matrix.unitaryGroup n ℂ)
    (hintertwine : ∀ g, U g * P = P * R g) :
    ∃ (Q : Matrix n n ℂ) (W : Matrix m n ℂ),
      Q.PosDef ∧ Wᴴ * W = 1 ∧
      P = W * polarInterpolant Q 1 ∧
      W = W * polarInterpolant Q 0 ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 → (polarInterpolant Q γ).PosDef) ∧
      Continuous (fun γ : ℝ => W * polarInterpolant Q γ) ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
        Function.Injective (W * polarInterpolant Q γ).mulVec) ∧
      (∀ g γ, U g * (W * polarInterpolant Q γ) =
        (W * polarInterpolant Q γ) * R g) := by
  obtain ⟨Q, W, hQeq, hQ, hW, hPfactor⟩ :=
    exists_isometric_posDef_factor P hP
  refine ⟨Q, W, hQ, hW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hPfactor
  · simp
  · intro γ hγ₀ hγ₁
    exact polarInterpolant_posDef hQ hγ₀ hγ₁
  · exact (continuous_const : Continuous fun _ : ℝ => W).matrix_mul
      (continuous_polarInterpolant Q)
  · intro γ hγ₀ hγ₁
    exact isometric_mul_posDef_mulVec_injective hW
      (polarInterpolant_posDef hQ hγ₀ hγ₁)
  · intro g γ
    have hQc : Commute Q (R g) := by
      rw [hQeq]
      exact sqrt_gram_commute_of_unitary_intertwining (hU g) (hR g) (hintertwine g)
    have hQunit : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
    have hWdef : W = P * Q⁻¹ := by
      calc
        W = (W * Q) * Q⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQunit, Matrix.mul_one]
        _ = P * Q⁻¹ := by rw [← hPfactor]
    have hWintertwine : U g * W = W * R g := by
      rw [hWdef]
      calc
        U g * (P * Q⁻¹) = (U g * P) * Q⁻¹ := by rw [Matrix.mul_assoc]
        _ = (P * R g) * Q⁻¹ := by rw [hintertwine g]
        _ = P * (Q⁻¹ * R g) := by
          rw [Matrix.mul_assoc, ← (commute_nonsing_inv_left hQunit hQc).eq]
        _ = (P * Q⁻¹) * R g := by rw [Matrix.mul_assoc]
    calc
      U g * (W * polarInterpolant Q γ) = (U g * W) * polarInterpolant Q γ := by
        rw [Matrix.mul_assoc]
      _ = (W * R g) * polarInterpolant Q γ := by rw [hWintertwine]
      _ = W * (polarInterpolant Q γ * R g) := by
        rw [Matrix.mul_assoc, ← (polarInterpolant_commute hQc γ).eq]
      _ = (W * polarInterpolant Q γ) * R g := by rw [Matrix.mul_assoc]

/-- The right-polar path respects a pair of unitary physical and virtual
actions intertwining the original injective map. Source: Schuch–Pérez-García–
Cirac, arXiv:1010.3732, Section II.D.2, equation following
`eq:1d-iso:polardec`. This is a local matrix statement; a uniformly gapped
parent-Hamiltonian path requires a separate argument. -/
theorem exists_symmetric_polar_deformation_of_injective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : Matrix m n ℂ) (hP : Function.Injective P.mulVec)
    (U : Matrix m m ℂ) (R : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup m ℂ)
    (hR : R ∈ Matrix.unitaryGroup n ℂ)
    (hintertwine : U * P = P * R) :
    ∃ (Q : Matrix n n ℂ) (W : Matrix m n ℂ),
      Q.PosDef ∧ Wᴴ * W = 1 ∧
      P = W * polarInterpolant Q 1 ∧
      W = W * polarInterpolant Q 0 ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 → (polarInterpolant Q γ).PosDef) ∧
      Continuous (fun γ : ℝ => W * polarInterpolant Q γ) ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
        Function.Injective (W * polarInterpolant Q γ).mulVec) ∧
      (∀ γ : ℝ, U * (W * polarInterpolant Q γ) =
        (W * polarInterpolant Q γ) * R) := by
  simpa using exists_equivariant_polar_deformation_of_injective P hP
    (fun _ : Unit => U) (fun _ : Unit => R)
    (fun _ => hU) (fun _ => hR) (fun _ => hintertwine)

end Matrix
