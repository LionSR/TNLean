/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PeripheralSpectrum
import TNLean.Channel.PeripheralClosure
import TNLean.Channel.PeripheralClosureFixedPoint
import TNLean.Channel.PeriodicityRemoval
import TNLean.Channel.Schwarz
import TNLean.QPF.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclic decomposition of periodic irreducible channels

Following Wolf, *Quantum Channels & Operations*, Theorem 6.6.

The statements in this file are arranged in three layers:

1. a peripheral eigenvector of an irreducible unital Schwarz map can be normalized
   to a unitary;
2. a finite-order peripheral unitary admits a spectral decomposition into orthogonal
   projections that are cyclically permuted by the channel;
3. the `m`-th power of the channel restricts to primitive and irreducible dynamics
   on each cyclic sector.

At present this file is mainly an API scaffold: several proofs are intentionally
left as `sorry`. The main goal is to pin down the objects and theorem statements
needed by downstream periodicity-removal and blocked-canonical-form arguments.

To keep the statements algebraic, we use an abstract primitive root `γ` with
`IsPrimitiveRoot γ m` rather than the analytic expression
`Complex.exp (2 * π * Complex.I / m)`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

/-- The ambient matrix algebra `M_D(ℂ)`. -/
abbrev MatrixAlg (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- Linear endomorphisms of `M_D(ℂ)`. -/
abbrev MatrixEnd (D : ℕ) := MatrixAlg D →ₗ[ℂ] MatrixAlg D

/-- `T` preserves the corner algebra `P · M_D(ℂ) · P`. -/
def PreservesCorner {D : ℕ} (P : MatrixAlg D) (T : MatrixEnd D) : Prop :=
  ∀ X : MatrixAlg D, P * T (P * X * P) * P = T (P * X * P)

/-- The corner algebra `P · M_D(ℂ) · P`, viewed as a `ℂ`-submodule of the ambient matrix
algebra. -/
def cornerSubmodule {D : ℕ} (P : MatrixAlg D) : Submodule ℂ (MatrixAlg D) where
  carrier := {X | P * X * P = X}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    have hX' : P * X * P = X := by simpa using hX
    have hY' : P * Y * P = Y := by simpa using hY
    calc
      P * (X + Y) * P = P * X * P + P * Y * P := by
        simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      _ = X + Y := by simp [hX', hY']
  smul_mem' c X hX := by
    have hX' : P * X * P = X := by simpa using hX
    calc
      P * (c • X) * P = c • (P * X * P) := by
        rw [Matrix.mul_smul, smul_mul_assoc, Matrix.mul_assoc]
      _ = c • X := by simp [hX']

/-- Restriction of `T` to an invariant corner `P · M_D(ℂ) · P`. -/
def cornerRestriction {D : ℕ} (P : MatrixAlg D) (T : MatrixEnd D)
    (hInv : PreservesCorner P T) :
    cornerSubmodule P →ₗ[ℂ] cornerSubmodule P where
  toFun X := ⟨T X.1, by
    have hX : P * X.1 * P = X.1 := by
      exact X.2
    simpa [hX] using hInv X.1⟩
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    simp
  map_smul' c X := by
    apply Subtype.ext
    ext i j
    simp

/-- Ambient reformulation of irreducibility for the restriction of `T` to the corner
`P · M_D(ℂ) · P`. -/
def IsIrreducibleOnCorner {D : ℕ} (P : MatrixAlg D) (T : MatrixEnd D) : Prop :=
  ∀ Q : MatrixAlg D,
    IsOrthogonalProjection Q →
    Q * P = Q →
    P * Q = Q →
    PreservesCorner Q T →
    Q = 0 ∨ Q = P

namespace MPSTensor

private noncomputable def minEigenvalue {D : ℕ} [Nonempty (Fin D)]
    {H : MatrixAlg D} (hH : H.IsHermitian) : ℝ :=
  (Finset.univ.image hH.eigenvalues).min' (Finset.Nonempty.image Finset.univ_nonempty _)

private lemma minEigenvalue_le {D : ℕ} [Nonempty (Fin D)]
    {H : MatrixAlg D} (hH : H.IsHermitian) (i : Fin D) :
    minEigenvalue hH ≤ hH.eigenvalues i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private lemma diagonal_sub_smul_one {D : ℕ} (v : Fin D → ℝ) (c : ℝ) :
    Matrix.diagonal (fun j => (↑(v j) : ℂ)) - (↑c : ℂ) • (1 : MatrixAlg D) =
      Matrix.diagonal (fun j => (↑(v j - c) : ℂ)) := by
  ext i j
  simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  split <;> simp

private lemma hermitian_sub_scalar_spectral
    {D : ℕ} {H : MatrixAlg D} (hH : H.IsHermitian) (c : ℝ) :
    H - (↑c : ℂ) • 1 =
      (↑hH.eigenvectorUnitary : MatrixAlg D) *
      Matrix.diagonal (fun j => (↑(hH.eigenvalues j - c) : ℂ)) *
      (↑hH.eigenvectorUnitary : MatrixAlg D)ᴴ := by
  set U : MatrixAlg D := ↑hH.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := by
    simpa [U] using eig_mul_conj hH
  have h_cI : (↑c : ℂ) • (1 : MatrixAlg D) = U * ((↑c : ℂ) • 1) * Uᴴ := by
    calc
      (↑c : ℂ) • (1 : MatrixAlg D) = (↑c : ℂ) • (U * Uᴴ) := by rw [hUU]
      _ = U * ((↑c : ℂ) • 1) * Uᴴ := by
          rw [Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc]
  calc
    H - (↑c : ℂ) • 1
        = U * Matrix.diagonal (fun j => ↑(hH.eigenvalues j)) * Uᴴ -
            U * ((↑c : ℂ) • 1) * Uᴴ := by
              conv_lhs =>
                rw [spectral_decomp_eq hH]
                rw [h_cI]
    _ = U * (Matrix.diagonal (fun j => ↑(hH.eigenvalues j)) - (↑c : ℂ) • 1) * Uᴴ := by
          noncomm_ring
    _ = U * Matrix.diagonal (fun j => ↑(hH.eigenvalues j - c)) * Uᴴ := by
          congr 1
          congr 1
          exact diagonal_sub_smul_one hH.eigenvalues c

private theorem hermitian_fixed_eq_scalar_of_irreducible_unital
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    (H : MatrixAlg D) (hH : H.IsHermitian)
    (hfix : transferMap (d := r) (D := D) K H = H) :
    ∃ c : ℂ, H = c • 1 := by
  classical
  haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
  set c0 : ℝ := minEigenvalue hH
  set U : MatrixAlg D := (↑hH.eigenvectorUnitary : MatrixAlg D)
  have hU_unit : IsUnit U := by
    apply (Matrix.isUnit_iff_isUnit_det U).2
    simpa [U] using Matrix.UnitaryGroup.det_isUnit hH.eigenvectorUnitary
  have hshift_eq :
      H - (c0 : ℂ) • 1 =
        U * Matrix.diagonal (fun i : Fin D => (↑(hH.eigenvalues i - c0) : ℂ)) * Uᴴ := by
    simpa [U] using hermitian_sub_scalar_spectral hH c0
  have hshift_psd : (H - (c0 : ℂ) • 1).PosSemidef := by
    rw [hshift_eq]
    have hdiag_psd :
        (Matrix.diagonal (fun i : Fin D => (↑(hH.eigenvalues i - c0) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast sub_nonneg.mpr (minEigenvalue_le hH i)
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU_unit).2 hdiag_psd
  have hone_fix : transferMap (d := r) (D := D) K (1 : MatrixAlg D) = 1 := by
    simpa [MPSTensor.transferMap_apply, KadisonSchwarz.krausMap,
      KadisonSchwarz.IsUnitalKraus] using hUnital
  have hshift_fix :
      transferMap (d := r) (D := D) K (H - (c0 : ℂ) • 1) = H - (c0 : ℂ) • 1 := by
    calc
      transferMap (d := r) (D := D) K (H - (c0 : ℂ) • 1)
          = transferMap (d := r) (D := D) K H - (c0 : ℂ) • transferMap (d := r) (D := D) K 1 := by
              simpa using (transferMap (d := r) (D := D) K).map_sub H ((c0 : ℂ) • (1 : MatrixAlg D))
      _ = H - (c0 : ℂ) • 1 := by simp [hfix, hone_fix]
  have hone_psd : (1 : MatrixAlg D).PosSemidef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := K) hIrr
      (1 : MatrixAlg D) (H - (c0 : ℂ) • 1) hone_psd one_ne_zero hshift_psd hone_fix hshift_fix with
    ⟨d, hd⟩
  refine ⟨d + c0, ?_⟩
  calc
    H = (H - (c0 : ℂ) • 1) + (c0 : ℂ) • 1 := by abel
    _ = d • 1 + (c0 : ℂ) • 1 := by rw [hd]
    _ = (d + c0) • 1 := by simp [add_smul]

private theorem fixed_eq_scalar_of_irreducible_unital
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    (X : MatrixAlg D)
    (hfix : transferMap (d := r) (D := D) K X = X) :
    ∃ c : ℂ, X = c • 1 := by
  have hfix_map : Kraus.map K X = X := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hfix
  have hfix_star_map : Kraus.map K Xᴴ = Xᴴ := by
    calc
      Kraus.map K Xᴴ = (Kraus.map K X)ᴴ := by
        simpa using (Kraus.map_conjTranspose K X).symm
      _ = Xᴴ := by simp [hfix_map]
  have hfix_star : transferMap (d := r) (D := D) K Xᴴ = Xᴴ := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hfix_star_map
  have hHerm_fix : transferMap (d := r) (D := D) K (X + Xᴴ) = X + Xᴴ := by
    calc
      transferMap (d := r) (D := D) K (X + Xᴴ)
          = transferMap (d := r) (D := D) K X + transferMap (d := r) (D := D) K Xᴴ := by
              simpa using (transferMap (d := r) (D := D) K).map_add X Xᴴ
      _ = X + Xᴴ := by simp [hfix, hfix_star]
  have hSkew_fix :
      transferMap (d := r) (D := D) K (Complex.I • (X - Xᴴ)) = Complex.I • (X - Xᴴ) := by
    calc
      transferMap (d := r) (D := D) K (Complex.I • (X - Xᴴ))
          = Complex.I • transferMap (d := r) (D := D) K (X - Xᴴ) := by
              simp using (transferMap (d := r) (D := D) K).map_smul Complex.I (X - Xᴴ)
      _ = Complex.I • (transferMap (d := r) (D := D) K X - transferMap (d := r) (D := D) K Xᴴ) := by
              simpa using congrArg (fun M => Complex.I • M)
                ((transferMap (d := r) (D := D) K).map_sub X Xᴴ)
      _ = Complex.I • (X - Xᴴ) := by simp [hfix, hfix_star]
  have hHerm_herm : (X + Xᴴ).IsHermitian := by
    simp [Matrix.IsHermitian, add_comm]
  have hSkew_herm : (Complex.I • (X - Xᴴ)).IsHermitian := by
    simp [Matrix.IsHermitian, sub_eq_add_neg, add_comm]
  rcases hermitian_fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr (X + Xᴴ) hHerm_herm hHerm_fix with ⟨a, ha⟩
  rcases hermitian_fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr (Complex.I • (X - Xᴴ)) hSkew_herm hSkew_fix with ⟨b, hb⟩
  refine ⟨(1 / 2 : ℂ) * (a - Complex.I * b), ?_⟩
  have hrecon :
      (X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ)) = (2 : ℂ) • X := by
    calc
      (X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ)) = (X + Xᴴ) + (X - Xᴴ) := by
            simp [sub_eq_add_neg, smul_smul]
            abel
      _ = (2 : ℂ) • X := by
            ext i j
            simp [two_mul, sub_eq_add_neg, add_assoc, add_left_comm]
  calc
    X = (1 / 2 : ℂ) • ((2 : ℂ) • X) := by simp
    _ = (1 / 2 : ℂ) • ((X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ))) := by rw [← hrecon]
    _ = (1 / 2 : ℂ) • ((a • (1 : MatrixAlg D)) - Complex.I • (b • (1 : MatrixAlg D))) := by
          rw [ha, hb]
    _ = ((1 / 2 : ℂ) * (a - Complex.I * b)) • (1 : MatrixAlg D) := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [sub_eq_add_neg, mul_comm, mul_left_comm]
          · simp [hij]

section PeripheralUnitary

/-- A peripheral eigenvalue of an irreducible unital Schwarz transfer map admits a unitary
matrix eigenvector.

This is the unitary part of Wolf Theorem 6.6. The current formulation is stated for transfer
maps of Kraus families because the available Kadison--Schwarz / multiplicative-domain API is
implemented at that level. -/
theorem exists_peripheral_unitary_of_irreducible_schwarz
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    {γ : ℂ}
    (hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D) := by
  classical
  haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
  rcases hγ with ⟨hγ_eig, hγ_norm⟩
  rcases hγ_eig.exists_hasEigenvector with ⟨X, hX_eigvec⟩
  have hX_mem : X ∈ Module.End.eigenspace (transferMap (d := r) (D := D) K) γ :=
    (Module.End.hasEigenvector_iff.mp hX_eigvec).1
  have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX_eigvec).2
  have hEig_transfer : transferMap (d := r) (D := D) K X = γ • X :=
    (Module.End.mem_eigenspace_iff).1 hX_mem
  have hEig_map : Kraus.map K X = γ • X := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hEig_transfer
  have hUnital' : Kraus.IsUnital K := by
    simpa [Kraus.IsUnital, KadisonSchwarz.IsUnitalKraus] using hUnital
  have hKS_map :
      Kraus.map K (Xᴴ * X) = (Kraus.map K X)ᴴ * Kraus.map K X :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hUnital' hρ hρfix X γ hEig_map hγ_norm
  have hγ_star_mul : star γ * γ = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hγ_norm]
  have hγ_starRing_mul : (starRingEnd ℂ) γ * γ = 1 := by
    simpa [Complex.star_def] using hγ_star_mul
  have hXX_fix_map : Kraus.map K (Xᴴ * X) = Xᴴ * X := by
    calc
      Kraus.map K (Xᴴ * X) = (Kraus.map K X)ᴴ * Kraus.map K X := hKS_map
      _ = (γ • X)ᴴ * (γ • X) := by simp [hEig_map]
      _ = ((starRingEnd ℂ) γ * γ) • (Xᴴ * X) := by
            simp [conjTranspose_smul, smul_smul, mul_comm]
      _ = Xᴴ * X := by simp [hγ_starRing_mul]
  have hXX_fix : transferMap (d := r) (D := D) K (Xᴴ * X) = Xᴴ * X := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hXX_fix_map
  have hXX_psd : (Xᴴ * X).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self X
  have hXX_ne : Xᴴ * X ≠ 0 := by
    intro h
    apply hX_ne
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h
  have hone_psd : (1 : MatrixAlg D).PosSemidef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
  have hone_fix : transferMap (d := r) (D := D) K (1 : MatrixAlg D) = 1 := by
    simpa [MPSTensor.transferMap_apply, KadisonSchwarz.krausMap,
      KadisonSchwarz.IsUnitalKraus] using hUnital
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := K) hIrr
      (1 : MatrixAlg D) (Xᴴ * X) hone_psd one_ne_zero hXX_psd hone_fix hXX_fix with ⟨c, hXX_scalar⟩
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    apply hXX_ne
    simp [hXX_scalar, hc0]
  have hc_nonneg : 0 ≤ c := by
    have hscalar_psd : (c • (1 : MatrixAlg D)).PosSemidef := by
      simpa [hXX_scalar] using hXX_psd
    have hdiag_psd : (Matrix.diagonal (fun _ : Fin D => c)).PosSemidef := by
      simpa [Matrix.smul_one_eq_diagonal] using hscalar_psd
    have hdiag_nonneg := (Matrix.posSemidef_diagonal_iff).1 hdiag_psd
    exact hdiag_nonneg ⟨0, NeZero.pos D⟩
  have hc_eq_real : c = (c.re : ℂ) := by
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hc_nonneg).2.symm)
  have hcre_nonneg : 0 ≤ c.re := (Complex.nonneg_iff.mp hc_nonneg).1
  have hcre_ne0 : c.re ≠ 0 := by
    intro h0
    apply hc_ne0
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = 0 := by simp [h0]
  have hcre_pos : 0 < c.re := lt_of_le_of_ne hcre_nonneg (Ne.symm hcre_ne0)
  set a : ℂ := (Real.sqrt c.re : ℂ)
  have ha_ne0 : a ≠ 0 := by
    have hsqrt_ne : ((Real.sqrt c.re : ℂ)) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr hcre_pos
    simpa [a] using hsqrt_ne
  have hstar_a : star a = a := by
    simp [a]
  have hstar_a_inv : (starRingEnd ℂ) a⁻¹ = a⁻¹ := by
    rw [map_inv₀]
    simpa [Complex.star_def] using hstar_a
  have hstar_a_inv' : star a⁻¹ = a⁻¹ := by
    simpa [Complex.star_def] using hstar_a_inv
  have hc_eq_sq : c = a * a := by
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = (((Real.sqrt c.re) ^ 2 : ℝ) : ℂ) := by
            simp [Real.sq_sqrt hcre_nonneg]
      _ = a * a := by
            rw [pow_two]
            simp [a]
  refine ⟨⟨a⁻¹ • X, by
    rw [Matrix.mem_unitaryGroup_iff']
    calc
      (a⁻¹ • X)ᴴ * (a⁻¹ • X) = ((a⁻¹ * a⁻¹) * c) • (1 : MatrixAlg D) := by
            rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hXX_scalar, smul_smul,
              hstar_a_inv']
      _ = 1 := by
            have hscalar : ((a⁻¹ * a⁻¹) * c : ℂ) = 1 := by
              calc
                (a⁻¹ * a⁻¹) * c = (a⁻¹ * a⁻¹) * (a * a) := by rw [hc_eq_sq]
                _ = 1 := by field_simp [ha_ne0]
            simp [hscalar]⟩, ?_⟩
  calc
    transferMap (d := r) (D := D) K (a⁻¹ • X) = a⁻¹ • transferMap (d := r) (D := D) K X := by
          simp
    _ = a⁻¹ • (γ • X) := by rw [hEig_transfer]
    _ = γ • (a⁻¹ • X) := by simp [smul_smul, mul_comm]

/-- Powers of a peripheral unitary remain peripheral eigenvectors. -/
theorem map_powers_of_peripheral_unitary
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    {γ : ℂ}
    (hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K))
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hU : transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D)) :
    ∀ k : ℕ,
      transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
        γ ^ k • ((U : MatrixAlg D) ^ k) := by
  intro k
  have hγnorm : ‖γ‖ = 1 := hγ.2
  have hU_map : Kraus.map K (U : MatrixAlg D) = γ • (U : MatrixAlg D) := by
    simpa [Kraus.map, MPSTensor.transferMap_apply] using hU
  have hU_kraus : KadisonSchwarz.krausMap (d := r) (D := D) K (U : MatrixAlg D) =
      γ • (U : MatrixAlg D) := by
    simpa [KadisonSchwarz.krausMap, MPSTensor.transferMap_apply] using hU
  have hUnital' : Kraus.IsUnital K := by
    simpa [Kraus.IsUnital, KadisonSchwarz.IsUnitalKraus] using hUnital
  have hKS_map :
      Kraus.map K ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) =
        (Kraus.map K (U : MatrixAlg D))ᴴ * Kraus.map K (U : MatrixAlg D) :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hUnital' hρ hρfix (U : MatrixAlg D) γ hU_map hγnorm
  have hKS_kraus :
      KadisonSchwarz.krausMap (d := r) (D := D) K ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) =
        (KadisonSchwarz.krausMap (d := r) (D := D) K (U : MatrixAlg D))ᴴ *
          KadisonSchwarz.krausMap (d := r) (D := D) K (U : MatrixAlg D) := by
    simpa [Kraus.map, KadisonSchwarz.krausMap] using hKS_map
  have hpow_kraus :
      KadisonSchwarz.krausMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
        γ ^ k • ((U : MatrixAlg D) ^ k) :=
    KadisonSchwarz.krausMap_pow_of_ks_equality
      (K := K) hUnital (U : MatrixAlg D) γ hU_kraus hKS_kraus k
  simpa [KadisonSchwarz.krausMap, MPSTensor.transferMap_apply] using hpow_kraus

/-- A generator of the peripheral cycle can be normalized to have exact order `m`. -/
theorem exists_normalized_peripheral_unitary_of_irreducible_schwarz
    {r D m : ℕ} [NeZero D] [NeZero m]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D) ∧
      ((U : MatrixAlg D) ^ m = 1) := by
  classical
  haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
  obtain ⟨U, hU⟩ :=
    exists_peripheral_unitary_of_irreducible_schwarz
      (K := K) hUnital ρ hρ hρfix hIrr hγ
  have hPow :
      ∀ k : ℕ,
        transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
          γ ^ k • ((U : MatrixAlg D) ^ k) :=
    map_powers_of_peripheral_unitary
      (K := K) hUnital ρ hρ hρfix hγ U hU
  have hUm_fix :
      transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ m) = (U : MatrixAlg D) ^ m := by
    calc
      transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ m)
          = γ ^ m • ((U : MatrixAlg D) ^ m) := hPow m
      _ = (U : MatrixAlg D) ^ m := by simp [hγprim.pow_eq_one]
  rcases fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr ((U : MatrixAlg D) ^ m) hUm_fix with ⟨α, hUm_scalar⟩
  have hUm_unitary : (((U : MatrixAlg D) ^ m)ᴴ * ((U : MatrixAlg D) ^ m)) = 1 := by
    simpa using Matrix.UnitaryGroup.star_mul_self (U ^ m)
  have hα_unit_mul : α * (starRingEnd ℂ) α = 1 := by
    let i0 : Fin D := ⟨0, NeZero.pos D⟩
    have hscalar_mat : ((α • (1 : MatrixAlg D))ᴴ * (α • (1 : MatrixAlg D)) : MatrixAlg D) = 1 := by
      simpa [hUm_scalar] using hUm_unitary
    have hentry := congrFun (congrFun hscalar_mat i0) i0
    simpa using hentry
  have hα_unit : star α * α = 1 := by
    simpa [Complex.star_def, mul_comm] using hα_unit_mul
  have hα_sq : ‖α‖ ^ 2 = 1 := by
    have hnormSqC : (↑(Complex.normSq α) : ℂ) = 1 := by
      calc
        (↑(Complex.normSq α) : ℂ) = star α * α := by
          rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
        _ = 1 := hα_unit
    have hnormSq : Complex.normSq α = 1 := by
      exact_mod_cast hnormSqC
    simpa [Complex.normSq_eq_norm_sq] using hnormSq
  have hα_norm : ‖α‖ = 1 := by
    have hnonneg : 0 ≤ ‖α‖ := norm_nonneg α
    nlinarith
  set β : ℂ := α⁻¹ ^ (m⁻¹ : ℂ)
  have hβm : β ^ m = α⁻¹ := by
    simpa [β] using (Complex.cpow_nat_inv_pow (α⁻¹) (NeZero.ne m))
  have hβ_norm_pow : ‖β‖ ^ m = 1 := by
    calc
      ‖β‖ ^ m = ‖β ^ m‖ := by rw [norm_pow]
      _ = ‖α⁻¹‖ := by simp [hβm]
      _ = 1 := by simp [hα_norm]
  have hβ_norm : ‖β‖ = 1 := by
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg β) (NeZero.ne m)).1 hβ_norm_pow
  have hβ_unit : star β * β = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hβ_norm]
  have hβ_starRing_mul : (starRingEnd ℂ) β * β = 1 := by
    simpa [Complex.star_def] using hβ_unit
  have hU_star_mul : ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  refine ⟨⟨β • (U : MatrixAlg D), by
    rw [Matrix.mem_unitaryGroup_iff']
    calc
      (β • (U : MatrixAlg D))ᴴ * (β • (U : MatrixAlg D)) =
          ((starRingEnd ℂ) β * β) • ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) := by
            simp [conjTranspose_smul, smul_smul, mul_comm]
      _ = 1 := by rw [hβ_starRing_mul, hU_star_mul]; simp⟩, ?_, ?_⟩
  · calc
      transferMap (d := r) (D := D) K (β • (U : MatrixAlg D))
          = β • transferMap (d := r) (D := D) K (U : MatrixAlg D) := by simp
      _ = β • (γ • (U : MatrixAlg D)) := by rw [hU]
      _ = γ • (β • (U : MatrixAlg D)) := by simp [smul_smul, mul_comm]
  · calc
      (β • (U : MatrixAlg D)) ^ m = β ^ m • ((U : MatrixAlg D) ^ m) := by
            simpa using smul_pow β (U : MatrixAlg D) m
      _ = β ^ m • (α • (1 : MatrixAlg D)) := by rw [hUm_scalar]
      _ = ((β ^ m) * α) • (1 : MatrixAlg D) := by rw [smul_smul]
      _ = 1 := by
            have hα_ne0 : α ≠ 0 := by
              intro h0
              simp [h0] at hα_unit
            simp [hβm, hα_ne0]

end PeripheralUnitary

end MPSTensor

section CyclicProjections

variable {D m : ℕ} [NeZero m]

/-- Spectral projections of a finite-order peripheral unitary.

Here `γ` should be thought of as the canonical phase `exp(2π i / m)`, represented in Lean by
an abstract primitive root `hγprim : IsPrimitiveRoot γ m`. -/
theorem exists_cyclic_projections_of_peripheral_unitary
    (T : MatrixEnd D) {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hUm : ((U : MatrixAlg D) ^ m) = 1)
    (hPow : ∀ k : ℕ, T ((U : MatrixAlg D) ^ k) = γ ^ k • ((U : MatrixAlg D) ^ k)) :
    ∃ P : Fin m → MatrixAlg D,
      (∀ k : Fin m, IsOrthogonalProjection (P k)) ∧
      (∑ k : Fin m, P k = 1) ∧
      ((U : MatrixAlg D) = ∑ k : Fin m, γ ^ (k : ℕ) • P k) ∧
      (∀ k : Fin m, T (P (k + 1)) = P k) := by
  sorry

end CyclicProjections

namespace MPSTensor

/-- Packaged version of Wolf Theorem 6.6 for transfer maps of irreducible unital Schwarz
maps, assuming the peripheral spectrum is generated by a primitive `m`-th root `γ`. -/
theorem exists_cyclic_decomposition_of_irreducible_schwarz
    {r D m : ℕ} [NeZero D] [NeZero m]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (transferMap (d := r) (D := D) K))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues (transferMap (d := r) (D := D) K) =
      Set.range (fun j : Fin m => γ ^ (j : ℕ))) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      ∃ P : Fin m → MatrixAlg D,
        transferMap (d := r) (D := D) K (U : MatrixAlg D) = γ • (U : MatrixAlg D) ∧
        (∀ k : ℕ,
          transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
            γ ^ k • ((U : MatrixAlg D) ^ k)) ∧
        ((U : MatrixAlg D) ^ m = 1) ∧
        (∀ k : Fin m, IsOrthogonalProjection (P k)) ∧
        (∑ k : Fin m, P k = 1) ∧
        ((U : MatrixAlg D) = ∑ k : Fin m, γ ^ (k : ℕ) • P k) ∧
        (∀ k : Fin m, transferMap (d := r) (D := D) K (P (k + 1)) = P k) := by
  have hγ : γ ∈ peripheralEigenvalues (transferMap (d := r) (D := D) K) := by
    rw [hperiph]
    by_cases hm1 : m = 1
    · subst hm1
      simp [IsPrimitiveRoot.one_right_iff.mp hγprim]
    · have hm0 : m ≠ 0 := NeZero.ne m
      have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
      exact ⟨⟨1, hm_gt⟩, by simp⟩
  obtain ⟨U, hU, hUm⟩ :=
    exists_normalized_peripheral_unitary_of_irreducible_schwarz
      (K := K) hUnital ρ hρ hρfix hIrr hγprim hγ
  have hPow :
      ∀ k : ℕ,
        transferMap (d := r) (D := D) K ((U : MatrixAlg D) ^ k) =
          γ ^ k • ((U : MatrixAlg D) ^ k) :=
    map_powers_of_peripheral_unitary
      (K := K) hUnital ρ hρ hρfix hγ U hU
  obtain ⟨P, hPproj, hPsum, hUspec, hcyclic⟩ :=
    exists_cyclic_projections_of_peripheral_unitary
      (T := transferMap (d := r) (D := D) K) hγprim U hUm hPow
  exact ⟨U, P, hU, hPow, hUm, hPproj, hPsum, hUspec, hcyclic⟩

end MPSTensor

section PrimitivityOfSectors

variable {D m : ℕ} [NeZero m]

/-- The `m`-th power of the channel preserves each cyclic corner `P_k · M_D(ℂ) · P_k`.

The cyclic permutation of the projections alone is not enough for this conclusion for a general
linear map. We therefore assume the left- and right-multiplicative-domain identities on the
sector projections, which are the abstract consequences needed from the multiplicative-domain
argument in Wolf Theorem 6.6. -/
theorem preserves_corner_pow_of_cyclic_decomp
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (_hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)) :
    ∀ k : Fin m, PreservesCorner (P k) (T ^ m) := by
  let idx : Fin m → ℕ → Fin m := fun k n =>
    ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩
  have hidx_zero : ∀ k : Fin m, idx k 0 = k := by
    intro k
    ext
    simp [idx, Nat.mod_eq_of_lt k.is_lt]
  have hidx_succ : ∀ k : Fin m, ∀ n : ℕ, idx k (n + 1) = idx k n + 1 := by
    intro k n
    ext
    change ((k : ℕ) + (n + 1)) % m = ((((k : ℕ) + n) % m) + 1 % m) % m
    symm
    simp [Nat.add_assoc] using (Nat.add_mod ((k : ℕ) + n) 1 m)
  have hidx_full : ∀ k : Fin m, idx k m = k := by
    intro k
    ext
    change ((k : ℕ) + m) % m = k
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]
  have hstep :
      ∀ n : ℕ, ∀ k : Fin m, ∀ X : MatrixAlg D,
        (T ^ n) (P (idx k n) * X * P (idx k n)) = P k * ((T ^ n) X) * P k := by
    intro n
    induction n with
    | zero =>
        intro k X
        simp [hidx_zero k]
    | succ n ih =>
        intro k X
        calc
          (T ^ (n + 1)) (P (idx k (n + 1)) * X * P (idx k (n + 1)))
              = (T ^ n) (T (P (idx k (n + 1)) * X * P (idx k (n + 1)))) := by
                  simp [pow_succ]
          _ = (T ^ n) (T (P (idx k n + 1) * X * P (idx k n + 1))) := by
                  rw [hidx_succ k n]
          _ = (T ^ n) (P (idx k n) * T X * P (idx k n)) := by
                  congr 1
                  calc
                    T (P (idx k n + 1) * X * P (idx k n + 1))
                        = T (P (idx k n + 1) * X) * T (P (idx k n + 1)) := by
                            exact hMulRight (idx k n + 1) (P (idx k n + 1) * X)
                    _ = (T (P (idx k n + 1)) * T X) * T (P (idx k n + 1)) := by
                            rw [hMulLeft (idx k n + 1) X]
                    _ = P (idx k n) * T X * P (idx k n) := by
                            rw [hcyclic (idx k n)]
          _ = P k * ((T ^ n) (T X)) * P k := ih k (T X)
          _ = P k * ((T ^ (n + 1)) X) * P k := by
                  simp [pow_succ]
  intro k X
  have hmk := hstep m k X
  rw [hidx_full k] at hmk
  rw [hmk]
  calc
    P k * (P k * ((T ^ m) X) * P k) * P k
        = (P k * P k) * ((T ^ m) X) * (P k * P k) := by
            simp [Matrix.mul_assoc]
    _ = P k * ((T ^ m) X) * P k := by
            simp [Matrix.mul_assoc, (hPproj k).2]
/-- Wolf Theorem 6.6 corollary: the `m`-step dynamics on each cyclic sector is irreducible.

The key missing input is an orbit-sum lift from an invariant subprojection of the corner to a
`T`-invariant ambient projection. This packages the `R = ∑_j T^j(Q)` construction suggested by
Wolf's proof. -/
theorem isIrreducible_restriction_of_cyclic_decomp
    {T : MatrixEnd D}
    (hIrr : IsIrreducibleMap T)
    (P : Fin m → MatrixAlg D)
    (_hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (_hPsum : ∑ k : Fin m, P k = 1)
    (_hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hLift :
      ∀ k : Fin m, ∀ Q : MatrixAlg D,
        IsOrthogonalProjection Q →
        Q * P k = Q →
        P k * Q = Q →
        PreservesCorner Q (T ^ m) →
        ∃ R : MatrixAlg D,
          IsOrthogonalProjection R ∧
          PreservesCorner R T ∧
          (Q = 0 ↔ R = 0) ∧
          (Q = P k ↔ R = 1)) :
    ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
  intro k Q hQproj hQP hPQ hQinv
  rcases hLift k Q hQproj hQP hPQ hQinv with ⟨R, hRproj, hRinv, hQzero, hQfull⟩
  rcases hIrr R hRproj hRinv with hR0 | hR1
  · left
    exact hQzero.mpr hR0
  · right
    exact hQfull.mpr hR1
/-- Wolf Theorem 6.6 corollary: the `m`-step dynamics on each cyclic sector is primitive. -/
theorem isPrimitive_restriction_of_cyclic_decomp
    {T : MatrixEnd D} [NeZero D] {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k))
    (hPne : ∀ k : Fin m, P k ≠ 0) :
    ∀ k : Fin m,
      IsPrimitive
        (cornerRestriction (P k) (T ^ m)
          (preserves_corner_pow_of_cyclic_decomp
            (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight k)) := by
  let hInv : ∀ k : Fin m, PreservesCorner (P k) (T ^ m) :=
    preserves_corner_pow_of_cyclic_decomp (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight
  have hone_mem : (1 : ℂ) ∈ peripheralEigenvalues T := by
    rw [hperiph]
    exact ⟨0, by simp⟩
  rcases hone_mem.1.exists_hasEigenvector with ⟨ρ, hρeig⟩
  have hρ_fix : T ρ = ρ := by
    exact (Module.End.HasEigenvector.apply_eq_smul hρeig).trans (by simp)
  have hρ_ne : ρ ≠ 0 := (Module.End.hasEigenvector_iff.mp hρeig).2
  have hper_pow : ∀ μ : ℂ, μ ∈ peripheralEigenvalues T → μ ^ m = 1 := by
    intro μ hμ
    rw [hperiph] at hμ
    rcases hμ with ⟨j, rfl⟩
    calc
      (γ ^ (j : ℕ)) ^ m = γ ^ ((j : ℕ) * m) := by rw [pow_mul]
      _ = γ ^ (m * (j : ℕ)) := by rw [Nat.mul_comm]
      _ = (γ ^ m) ^ (j : ℕ) := by rw [pow_mul]
      _ = 1 := by simp [hγprim.pow_eq_one]
  have hperiph_pow : peripheralEigenvalues (T ^ m) = {1} :=
    peripheralEigenvalues_pow_eq_singleton
      (E := T) (p := m) (hp := Nat.pos_of_ne_zero (NeZero.ne m))
      hper_pow ρ hρ_fix hρ_ne
  let idx : Fin m → ℕ → Fin m := fun k n =>
    ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩
  have hidx_zero : ∀ k : Fin m, idx k 0 = k := by
    intro k
    ext
    simp [idx, Nat.mod_eq_of_lt k.is_lt]
  have hidx_succ : ∀ k : Fin m, ∀ n : ℕ, idx k (n + 1) = idx k n + 1 := by
    intro k n
    ext
    change ((k : ℕ) + (n + 1)) % m = ((((k : ℕ) + n) % m) + 1 % m) % m
    symm
    simp [Nat.add_assoc] using (Nat.add_mod ((k : ℕ) + n) 1 m)
  have hidx_full : ∀ k : Fin m, idx k m = k := by
    intro k
    ext
    change ((k : ℕ) + m) % m = k
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]
  have hcyclic_pow : ∀ n : ℕ, ∀ k : Fin m, (T ^ n) (P (idx k n)) = P k := by
    intro n
    induction n with
    | zero =>
        intro k
        simp [hidx_zero k]
    | succ n ih =>
        intro k
        calc
          (T ^ (n + 1)) (P (idx k (n + 1))) = (T ^ n) (T (P (idx k (n + 1)))) := by
            simp [pow_succ]
          _ = (T ^ n) (T (P (idx k n + 1))) := by rw [hidx_succ k n]
          _ = (T ^ n) (P (idx k n)) := by rw [hcyclic (idx k n)]
          _ = P k := ih k
  have hPk_fix : ∀ k : Fin m, (T ^ m) (P k) = P k := by
    intro k
    have hmk := hcyclic_pow m k
    simpa [hidx_full k] using hmk
  have hPk_corner : ∀ k : Fin m, P k ∈ cornerSubmodule (P k) := by
    intro k
    change P k * P k * P k = P k
    rw [Matrix.mul_assoc, (hPproj k).2, (hPproj k).2]
  have hcorner_fix : ∀ k : Fin m,
      cornerRestriction (P k) (T ^ m) (hInv k) ⟨P k, hPk_corner k⟩ = ⟨P k, hPk_corner k⟩ := by
    intro k
    apply Subtype.ext
    simpa using hPk_fix k
  have hcorner_ne : ∀ k : Fin m, (⟨P k, hPk_corner k⟩ : cornerSubmodule (P k)) ≠ 0 := by
    intro k hzero
    apply hPne k
    have hval := congrArg Subtype.val hzero
    simpa using hval
  have huniq : ∀ k : Fin m, ∀ μ : ℂ,
      Module.End.HasEigenvalue (cornerRestriction (P k) (T ^ m) (hInv k)) μ →
      ‖μ‖ = 1 → μ = 1 := by
    intro k μ hμeig hμnorm
    rcases hμeig.exists_hasEigenvector with ⟨X, hX⟩
    have hX_mem : X ∈ Module.End.eigenspace (cornerRestriction (P k) (T ^ m) (hInv k)) μ :=
      (Module.End.hasEigenvector_iff.mp hX).1
    have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
    have hX_eq : cornerRestriction (P k) (T ^ m) (hInv k) X = μ • X :=
      (Module.End.mem_eigenspace_iff).1 hX_mem
    have hX_eq_val : (T ^ m) X.1 = μ • X.1 := congrArg Subtype.val hX_eq
    have hX_mem_ambient : X.1 ∈ Module.End.eigenspace (T ^ m) μ :=
      (Module.End.mem_eigenspace_iff).2 hX_eq_val
    have hX_ne_ambient : X.1 ≠ 0 := by
      intro h0
      apply hX_ne
      apply Subtype.ext
      simpa using h0
    have hX_eig_ambient : Module.End.HasEigenvector (T ^ m) μ X.1 :=
      (Module.End.hasEigenvector_iff).2 ⟨hX_mem_ambient, hX_ne_ambient⟩
    have hμ_ambient : μ ∈ peripheralEigenvalues (T ^ m) :=
      ⟨Module.End.hasEigenvalue_of_hasEigenvector hX_eig_ambient, hμnorm⟩
    rw [hperiph_pow] at hμ_ambient
    exact hμ_ambient
  intro k
  exact isPrimitive_of_unique_norm_one
    (cornerRestriction (P k) (T ^ m) (hInv k))
    ⟨P k, hPk_corner k⟩
    (hcorner_fix k)
    (hcorner_ne k)
    (huniq k)
end PrimitivityOfSectors
