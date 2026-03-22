/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.ClosureFixedPoint
import TNLean.Channel.Peripheral.PeriodicityRemoval
import TNLean.Channel.Schwarz.Basic
import TNLean.QPF.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclic decomposition of periodic irreducible channels

This file formalizes the algebraic pieces of Wolf, *Quantum Channels & Operations*,
Theorem 6.6, for transfer maps of Kraus families.

The arguments are organized in three steps:

1. a peripheral eigenvector of an irreducible unital Schwarz map can be normalized to a
   unitary;
2. a finite-order peripheral unitary admits spectral projections that are cyclically permuted by
   the channel;
3. the `m`-th power of the channel preserves each cyclic sector, and abstract irreducibility /
   primitivity hypotheses can be transferred to the resulting corner restrictions.

To keep the statements algebraic, the peripheral cycle is represented by an abstract primitive
root `γ` with `IsPrimitiveRoot γ m` rather than by the analytic expression
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
      _ = Xᴴ := by rw [hfix_map]
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
              simp
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

This is the unitary part of Wolf Theorem 6.6. The formulation is stated for transfer maps of
Kraus families because the available Kadison--Schwarz / multiplicative-domain API is implemented
at that level. -/
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
      _ = (γ • X)ᴴ * (γ • X) := by rw [hEig_map]
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
  classical
  let invm : ℂ := (↑m : ℂ)⁻¹
  let oneIdx : ℕ := ((1 : Fin m) : ℕ)
  let P : Fin m → MatrixAlg D := fun k =>
    invm • Finset.sum (Finset.range m)
      (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have honeIdx_lt : oneIdx < m := by
    simpa [oneIdx] using ((1 : Fin m).is_lt)
  have honeIdx_mem : oneIdx ∈ Finset.range m := by
    simp [honeIdx_lt]
  have hγ_norm : ‖γ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hγprim.pow_eq_one hm0
  have hγ_star_mul : star γ * γ = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hγ_norm]
  have hγ_mul_star : γ * star γ = 1 := by
    simpa [mul_comm] using hγ_star_mul
  have hγ_star_eq_inv : star γ = γ⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hγ_mul_star
  have hγinv_prim : IsPrimitiveRoot (γ⁻¹) m := hγprim.inv
  have hγpow_mul_starpow (n : ℕ) : γ ^ n * (star γ) ^ n = 1 := by
    simpa [mul_pow] using congrArg (fun z : ℂ => z ^ n) hγ_mul_star
  have hstarpow_mul_γpow (n : ℕ) : (star γ) ^ n * γ ^ n = 1 := by
    simpa [mul_pow] using congrArg (fun z : ℂ => z ^ n) hγ_star_mul
  have hγ_pow_oneIdx : γ ^ oneIdx = γ := by
    by_cases hm1 : m = 1
    · subst hm1
      simp [oneIdx, IsPrimitiveRoot.one_right_iff.mp hγprim]
    · have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
      simp [oneIdx, Nat.mod_eq_of_lt hm_gt]
  have hU_pow_oneIdx : ((U : MatrixAlg D) ^ oneIdx) = (U : MatrixAlg D) := by
    by_cases hm1 : m = 1
    · subst hm1
      have hUeq : (U : MatrixAlg D) = 1 := by simpa using hUm
      simp [oneIdx, hUeq]
    · have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
      simp [oneIdx, Nat.mod_eq_of_lt hm_gt]
  have hsum_powers_fin (x : ℂ) (hxpow : x ^ m = 1) :
      ∑ k : Fin m, x ^ (k : ℕ) = if x = 1 then (m : ℂ) else 0 := by
    by_cases hx : x = 1
    · subst hx
      rw [if_pos rfl, Fin.sum_univ_eq_sum_range]
      simp
    · rw [if_neg hx, Fin.sum_univ_eq_sum_range]
      have hmul : (Finset.sum (Finset.range m) fun i => x ^ i) * (x - 1) = 0 := by
        simpa [hxpow] using (geom_sum_mul x m)
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hx)
  have hcoeff_sum_proj (j : ℕ) (hj : j < m) :
      ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) = if j = 0 then (m : ℂ) else 0 := by
    have hpowm : ((((star γ) ^ j : ℂ)) ^ m) = 1 := by
      calc
        ((((star γ) ^ j : ℂ)) ^ m) = (star γ : ℂ) ^ (j * m) := by rw [← pow_mul]
        _ = (star γ : ℂ) ^ (m * j) := by rw [Nat.mul_comm]
        _ = (((star γ : ℂ) ^ m) ^ j) := by rw [pow_mul]
        _ = 1 := by rw [hγ_star_eq_inv]; simp [hγprim.pow_eq_one]
    have hrewrite :
        ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) =
          ∑ k : Fin m, ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) = (star γ : ℂ) ^ ((k : ℕ) * j) := by rw [← pow_mul]
        _ = (star γ : ℂ) ^ (j * (k : ℕ)) := by rw [Nat.mul_comm]
        _ = ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by rw [pow_mul]
    rw [hrewrite, hsum_powers_fin ((star γ) ^ j) hpowm]
    by_cases hj0 : j = 0
    · subst hj0
      simp
    · have hne : ((star γ) ^ j : ℂ) ≠ 1 := by
        intro hpow
        have hdvd : m ∣ j :=
          (hγinv_prim.pow_eq_one_iff_dvd j).mp (by simpa [hγ_star_eq_inv] using hpow)
        exact hj0 (Nat.eq_zero_of_dvd_of_lt hdvd hj)
      rw [if_neg hne, if_neg hj0]
  have hcoeff_sum_spec (j : ℕ) (hj : j < m) :
      ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
        if j = oneIdx then (m : ℂ) else 0 := by
    have hpowm : (γ * (star γ) ^ j) ^ m = 1 := by
      calc
        (γ * (star γ) ^ j) ^ m = γ ^ m * ((((star γ) ^ j : ℂ)) ^ m) := by
          rw [mul_pow]
        _ = γ ^ m * (((star γ : ℂ) ^ m) ^ j) := by
          congr 1
          calc
            ((((star γ) ^ j : ℂ)) ^ m) = (star γ : ℂ) ^ (j * m) := by
              rw [← pow_mul]
            _ = (star γ : ℂ) ^ (m * j) := by
              rw [Nat.mul_comm]
            _ = (((star γ : ℂ) ^ m) ^ j) := by
              rw [pow_mul]
        _ = 1 := by
          rw [hγ_star_eq_inv]
          simp [hγprim.pow_eq_one]
    have hrewrite :
        ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
          ∑ k : Fin m, (γ * (star γ) ^ j) ^ (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
            = γ ^ (k : ℕ) * ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
                congr 1
                calc
                  ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) =
                      (star γ : ℂ) ^ ((k : ℕ) * j) := by
                    rw [← pow_mul]
                  _ = (star γ : ℂ) ^ (j * (k : ℕ)) := by
                    rw [Nat.mul_comm]
                  _ = ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
                    rw [pow_mul]
        _ = (γ * (star γ) ^ j) ^ (k : ℕ) := by
          rw [mul_pow]
    rw [hrewrite, hsum_powers_fin (γ * (star γ) ^ j) hpowm]
    by_cases hjeq : j = oneIdx
    · subst hjeq
      have hx : γ * (star γ) ^ oneIdx = 1 := by
        calc
          γ * (star γ) ^ oneIdx = γ ^ oneIdx * (star γ) ^ oneIdx := by rw [hγ_pow_oneIdx]
          _ = 1 := hγpow_mul_starpow oneIdx
      rw [if_pos hx, if_pos rfl]
    · have hne : γ * (star γ) ^ j ≠ 1 := by
        intro hx
        have hpoweq : γ ^ oneIdx = γ ^ j := by
          calc
            γ ^ oneIdx = γ := hγ_pow_oneIdx
            _ = γ * 1 := by simp
            _ = γ * ((star γ) ^ j * γ ^ j) := by rw [hstarpow_mul_γpow j]
            _ = (γ * (star γ) ^ j) * γ ^ j := by rw [mul_assoc]
            _ = 1 * γ ^ j := by rw [hx]
            _ = γ ^ j := by simp
        have hidxeq : oneIdx = j := hγprim.injOn_pow honeIdx_mem (by simp [hj]) hpoweq
        exact hjeq hidxeq.symm
      rw [if_neg hne, if_neg hjeq]
  have hbase_cyclic (k : Fin m) :
      ((star γ) ^ (((k + 1 : Fin m) : ℕ)) : ℂ) * γ = (star γ) ^ (k : ℕ) := by
    by_cases hk : (k : ℕ) + 1 < m
    · have hval : (((k + 1 : Fin m) : ℕ)) = (k : ℕ) + 1 := by
        simp [Fin.val_add, Nat.mod_eq_of_lt hk]
      rw [hval, pow_succ, mul_assoc, hγ_star_mul]
      simp
    · have hk_eq : (k : ℕ) + 1 = m := by
        have hle : m ≤ (k : ℕ) + 1 := by
          exact Nat.le_of_not_gt (show ¬ m > (k : ℕ) + 1 by simpa using hk)
        exact le_antisymm (Nat.succ_le_of_lt k.is_lt) hle
      have hval0 : (((k + 1 : Fin m) : ℕ)) = 0 := by
        simp [Fin.val_add, hk_eq]
      rw [hval0, pow_zero, one_mul]
      have hkval : (k : ℕ) = m - 1 := Nat.eq_sub_of_add_eq hk_eq
      rw [hkval]
      have hpowm_star : (star γ : ℂ) ^ m = 1 := by
        rw [hγ_star_eq_inv]
        simp [hγprim.pow_eq_one]
      have hmul : (star γ : ℂ) ^ (m - 1) * star γ = 1 := by
        calc
          (star γ : ℂ) ^ (m - 1) * star γ = (star γ : ℂ) ^ ((m - 1) + 1) := by
            simp [pow_succ]
          _ = 1 := by
            have hm' : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
            simpa [hm'] using hpowm_star
      have hpred : (star γ : ℂ) ^ (m - 1) = γ := by
        calc
          (star γ : ℂ) ^ (m - 1) = (star γ : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left hmul
          _ = γ := by rw [hγ_star_eq_inv, inv_inv]
      simpa using hpred.symm
  have hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k := by
    intro k
    dsimp [P, invm]
    calc
      T (((↑m : ℂ)⁻¹) • Finset.sum (Finset.range m)
          (fun j => ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
          = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
              (fun j => ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ)) •
                T ((U : MatrixAlg D) ^ j)) := by
              simp [map_sum]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => (((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j)) •
              ((U : MatrixAlg D) ^ j)) := by
            congr 2
            ext j
            rw [hPow j, smul_smul]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
            congr 2
            ext j
            have hcoef :
                ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j) =
                  ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
              calc
                ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j)
                    = ((((star γ) ^ (((k + 1 : Fin m) : ℕ)) : ℂ) * γ) ^ j : ℂ) := by
                        rw [← mul_pow]
                _ = ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
                        rw [hbase_cyclic k]
            rw [hcoef]
  have hcoeff_step (k : Fin m) (j : ℕ) :
      γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ)) =
        ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
    calc
      γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))
          = γ ^ (k : ℕ) * (((star γ) ^ (k : ℕ)) * (((star γ) ^ (k : ℕ)) ^ j)) := by
              rw [pow_succ']
      _ = (γ ^ (k : ℕ) * ((star γ) ^ (k : ℕ))) * (((star γ) ^ (k : ℕ)) ^ j) := by
              rw [mul_assoc]
      _ = ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
              rw [hγpow_mul_starpow (k : ℕ)]
              simp
  have hcoeff_last (k : Fin m) : ((((star γ) ^ (k : ℕ)) ^ (m - 1) : ℂ)) = γ ^ (k : ℕ) := by
    have hpowm : ((((star γ) ^ (k : ℕ) : ℂ)) ^ m) = 1 := by
      calc
        ((((star γ) ^ (k : ℕ) : ℂ)) ^ m) = (star γ : ℂ) ^ ((k : ℕ) * m) := by rw [← pow_mul]
        _ = (star γ : ℂ) ^ (m * (k : ℕ)) := by rw [Nat.mul_comm]
        _ = (((star γ : ℂ) ^ m) ^ (k : ℕ)) := by rw [pow_mul]
        _ = 1 := by rw [hγ_star_eq_inv]; simp [hγprim.pow_eq_one]
    have hmul : ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) * ((star γ) ^ (k : ℕ)) = 1 := by
      calc
        ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) * ((star γ) ^ (k : ℕ))
            = (((star γ) ^ (k : ℕ) : ℂ)) ^ ((m - 1) + 1) := by
                simp [pow_succ]
        _ = 1 := by
            have hm' : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
            simpa [hm'] using hpowm
    calc
      ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) = (((star γ) ^ (k : ℕ) : ℂ))⁻¹ :=
        eq_inv_of_mul_eq_one_left hmul
      _ = γ ^ (k : ℕ) := by
        rw [hγ_star_eq_inv, inv_pow]
        simp
  have hU_left : ∀ k : Fin m, (U : MatrixAlg D) * P k = γ ^ (k : ℕ) • P k := by
    intro k
    let a : ℕ → ℂ := fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
    have hm_pred_succ : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    have hdecomp :
        Finset.sum (Finset.range (m - 1))
            (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) + 1 =
          Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)) := by
      simpa [hm_pred_succ, a] using
        (Finset.sum_range_succ' (fun j : ℕ => a j • ((U : MatrixAlg D) ^ j)) (m - 1)).symm
    have hfactor :
        Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) =
          γ ^ (k : ℕ) • Finset.sum (Finset.range (m - 1))
            (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) := by
      calc
        Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1)))
            = Finset.sum (Finset.range (m - 1))
                (fun j => γ ^ (k : ℕ) • (a (j + 1) • ((U : MatrixAlg D) ^ (j + 1)))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [smul_smul]
        _ = γ ^ (k : ℕ) • Finset.sum (Finset.range (m - 1))
                (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) := by
                  rw [Finset.smul_sum]
    dsimp [P, invm]
    calc
      (U : MatrixAlg D) *
          ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)))
          = (↑m : ℂ)⁻¹ •
              ((U : MatrixAlg D) *
                Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
                rw [Matrix.mul_smul]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => a j • ((U : MatrixAlg D) * ((U : MatrixAlg D) ^ j))) := by
            congr 1
            simp [Finset.mul_sum]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) := by
            congr 2
            ext j
            rw [pow_succ']
      _ = (↑m : ℂ)⁻¹ •
            (Finset.sum (Finset.range (m - 1)) (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) +
              a (m - 1) • ((U : MatrixAlg D) ^ m)) := by
            have hsplit :
                Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) =
                  Finset.sum (Finset.range (m - 1))
                    (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) +
                    a (m - 1) • ((U : MatrixAlg D) ^ m) := by
              simpa [hm_pred_succ] using
                (Finset.sum_range_succ
                  (fun j : ℕ => a j • ((U : MatrixAlg D) ^ (j + 1)))
                  (m - 1))
            rw [hsplit]
      _ = (↑m : ℂ)⁻¹ •
            (Finset.sum (Finset.range (m - 1))
                (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
              γ ^ (k : ℕ) • (1 : MatrixAlg D)) := by
            congr 2
            · apply Finset.sum_congr rfl
              intro j hj
              have ha : a j = γ ^ (k : ℕ) * a (j + 1) := by
                dsimp [a]
                exact (hcoeff_step k j).symm
              rw [ha]
            · change
                ((((star γ) ^ (k : ℕ)) ^ (m - 1) : ℂ)) • ((U : MatrixAlg D) ^ m) =
                  γ ^ (k : ℕ) • (1 : MatrixAlg D)
              rw [hcoeff_last k, hUm]
      _ = (↑m : ℂ)⁻¹ •
            (γ ^ (k : ℕ) •
              (Finset.sum (Finset.range (m - 1))
                  (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) +
                1)) := by
            rw [hfactor, smul_add]
            simp [smul_smul]
      _ = (↑m : ℂ)⁻¹ •
            (γ ^ (k : ℕ) •
              Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
            rw [hdecomp]
      _ = γ ^ (k : ℕ) •
            ((↑m : ℂ)⁻¹ •
              Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
            simp [smul_smul, mul_comm]
  have hcommUP : ∀ k : Fin m, Commute (U : MatrixAlg D) (P k) := by
    intro k
    dsimp [P, invm]
    refine (Commute.sum_right (Finset.range m)
      (fun j : ℕ => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))
      (U : MatrixAlg D) ?_).smul_right ((↑m : ℂ)⁻¹)
    intro j hj
    exact ((Commute.refl (U : MatrixAlg D)).pow_right j).smul_right _
  have hU_right : ∀ k : Fin m, P k * (U : MatrixAlg D) = γ ^ (k : ℕ) • P k := by
    intro k
    rw [← (hcommUP k).eq]
    exact hU_left k
  have hPsum : ∑ k : Fin m, P k = 1 := by
    dsimp [P, invm]
    calc
      ∑ k : Fin m, (↑m : ℂ)⁻¹ •
          Finset.sum (Finset.range m)
            (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))
          = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
              Finset.sum (Finset.range m)
                (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
              symm
              rw [Finset.smul_sum]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j =>
              ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
            refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
            rw [Finset.sum_comm]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j =>
              (∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) • ((U : MatrixAlg D) ^ j)) := by
            refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_smul]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => (if j = 0 then (m : ℂ) else 0) • ((U : MatrixAlg D) ^ j)) := by
            refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcoeff_sum_proj j (Finset.mem_range.mp hj)]
      _ = (↑m : ℂ)⁻¹ • ((m : ℂ) • ((U : MatrixAlg D) ^ 0)) := by
            rw [Finset.sum_eq_single 0]
            · simp
            · intro j hj hj0
              simp [hj0]
            · intro hm
              exfalso
              exact hm (by simp [hm_pos])
      _ = 1 := by
            simp [hm0]
  have hUspec_sum : ∑ k : Fin m, γ ^ (k : ℕ) • P k = (U : MatrixAlg D) := by
    dsimp [P, invm]
    calc
      ∑ k : Fin m, γ ^ (k : ℕ) •
          ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
          = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
              Finset.sum (Finset.range m)
                (fun j =>
                  (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
                    ((U : MatrixAlg D) ^ j)) := by
              calc
                ∑ k : Fin m, γ ^ (k : ℕ) •
                    ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
                      (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
                    = ∑ k : Fin m, (↑m : ℂ)⁻¹ •
                        (γ ^ (k : ℕ) • Finset.sum (Finset.range m)
                          (fun j =>
                            ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        simp [smul_smul, mul_comm]
                _ = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
                        γ ^ (k : ℕ) • Finset.sum (Finset.range m)
                          (fun j =>
                            ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
                        symm
                        rw [Finset.smul_sum]
                _ = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
                        Finset.sum (Finset.range m)
                          (fun j =>
                            (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
                              ((U : MatrixAlg D) ^ j)) := by
                        refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
                        apply Finset.sum_congr rfl
                        intro k hk
                        rw [Finset.smul_sum]
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [smul_smul]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j =>
              ∑ k : Fin m,
                (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) • ((U : MatrixAlg D) ^ j)) := by
            refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
            rw [Finset.sum_comm]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j =>
              (∑ k : Fin m, γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
                ((U : MatrixAlg D) ^ j)) := by
            refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_smul]
      _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => (if j = oneIdx then (m : ℂ) else 0) • ((U : MatrixAlg D) ^ j)) := by
            refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcoeff_sum_spec j (Finset.mem_range.mp hj)]
      _ = (↑m : ℂ)⁻¹ • ((m : ℂ) • ((U : MatrixAlg D) ^ oneIdx)) := by
            rw [Finset.sum_eq_single oneIdx]
            · simp
            · intro j hj hj0
              simp [hj0]
            · simp [honeIdx_lt]
      _ = (U : MatrixAlg D) := by
            simp [hm0, hU_pow_oneIdx]
  have hpow_inj : ∀ {a b : Fin m}, γ ^ (a : ℕ) = γ ^ (b : ℕ) → a = b := by
    intro a b hab
    apply Fin.ext
    exact hγprim.injOn_pow (by simp [a.is_lt]) (by simp [b.is_lt]) hab
  have hPmul_zero : ∀ {k l : Fin m}, k ≠ l → P k * P l = 0 := by
    intro k l hkl
    have hkEig : (U : MatrixAlg D) * (P k * P l) = γ ^ (k : ℕ) • (P k * P l) := by
      calc
        (U : MatrixAlg D) * (P k * P l) = ((U : MatrixAlg D) * P k) * P l := by
          simp [Matrix.mul_assoc]
        _ = (γ ^ (k : ℕ) • P k) * P l := by rw [hU_left k]
        _ = γ ^ (k : ℕ) • (P k * P l) := by
          simp
    have hlEig : (U : MatrixAlg D) * (P k * P l) = γ ^ (l : ℕ) • (P k * P l) := by
      calc
        (U : MatrixAlg D) * (P k * P l) = ((U : MatrixAlg D) * P k) * P l := by
          simp [Matrix.mul_assoc]
        _ = (P k * (U : MatrixAlg D)) * P l := by rw [(hcommUP k).eq]
        _ = P k * ((U : MatrixAlg D) * P l) := by simp [Matrix.mul_assoc]
        _ = P k * (γ ^ (l : ℕ) • P l) := by rw [hU_left l]
        _ = γ ^ (l : ℕ) • (P k * P l) := by
          simp
    have hsub : (γ ^ (k : ℕ) - γ ^ (l : ℕ)) • (P k * P l) = 0 := by
      calc
        (γ ^ (k : ℕ) - γ ^ (l : ℕ)) • (P k * P l)
            = γ ^ (k : ℕ) • (P k * P l) - γ ^ (l : ℕ) • (P k * P l) := by
                simp [sub_smul]
        _ = 0 := by rw [← hkEig, ← hlEig]; simp
    have hneq : γ ^ (k : ℕ) - γ ^ (l : ℕ) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hpow
      exact hkl (hpow_inj hpow)
    exact (smul_eq_zero.mp hsub).resolve_left hneq
  have hPidem : ∀ k : Fin m, P k * P k = P k := by
    intro k
    have hsingle : ∑ l : Fin m, P k * P l = P k * P k := by
      exact Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (by
        intro l hl hne
        simpa using hPmul_zero hne.symm)
    have hEq : P k = P k * P k := by
      calc
        P k = P k * (1 : MatrixAlg D) := by simp
        _ = P k * (∑ l : Fin m, P l) := by rw [hPsum]
        _ = ∑ l : Fin m, P k * P l := by simp [Finset.mul_sum]
        _ = P k * P k := hsingle
    exact hEq.symm
  have hU_star_left : ∀ k : Fin m, (U : MatrixAlg D) * (P k)ᴴ = γ ^ (k : ℕ) • (P k)ᴴ := by
    intro k
    have hstar : (U : MatrixAlg D)ᴴ * (P k)ᴴ = star (γ ^ (k : ℕ)) • (P k)ᴴ := by
      simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul] using
        congrArg Matrix.conjTranspose (hU_right k)
    have hU_mul_star : (U : MatrixAlg D) * (U : MatrixAlg D)ᴴ = 1 := by
      exact (show (U : MatrixAlg D) * (U : MatrixAlg D)ᴴ = 1 from U.2.2)
    have hpre : (P k)ᴴ = star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) * (P k)ᴴ) := by
      calc
        (P k)ᴴ = (1 : MatrixAlg D) * (P k)ᴴ := by simp
        _ = ((U : MatrixAlg D) * (U : MatrixAlg D)ᴴ) * (P k)ᴴ := by rw [hU_mul_star]
        _ = (U : MatrixAlg D) * ((U : MatrixAlg D)ᴴ * (P k)ᴴ) := by simp [Matrix.mul_assoc]
        _ = (U : MatrixAlg D) * (star (γ ^ (k : ℕ)) • (P k)ᴴ) := by rw [hstar]
        _ = star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) * (P k)ᴴ) := by rw [Matrix.mul_smul]
    have hunit : γ ^ (k : ℕ) * star (γ ^ (k : ℕ)) = 1 := by
      simpa using hγpow_mul_starpow (k : ℕ)
    have hmain : (U : MatrixAlg D) * (P k)ᴴ = γ ^ (k : ℕ) • (P k)ᴴ := by
      calc
        (U : MatrixAlg D) * (P k)ᴴ = (1 : ℂ) • ((U : MatrixAlg D) * (P k)ᴴ) := by simp
        _ = (γ ^ (k : ℕ) * star (γ ^ (k : ℕ))) • ((U : MatrixAlg D) * (P k)ᴴ) := by rw [← hunit]
        _ = γ ^ (k : ℕ) • (star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) * (P k)ᴴ)) := by rw [smul_smul]
        _ = γ ^ (k : ℕ) • (P k)ᴴ := by rw [← hpre]
    exact hmain
  have hPmul_star_zero : ∀ {k l : Fin m}, k ≠ l → P l * (P k)ᴴ = 0 := by
    intro k l hkl
    have hlEig : (U : MatrixAlg D) * (P l * (P k)ᴴ) = γ ^ (l : ℕ) • (P l * (P k)ᴴ) := by
      calc
        (U : MatrixAlg D) * (P l * (P k)ᴴ) = ((U : MatrixAlg D) * P l) * (P k)ᴴ := by
          simp [Matrix.mul_assoc]
        _ = (γ ^ (l : ℕ) • P l) * (P k)ᴴ := by rw [hU_left l]
        _ = γ ^ (l : ℕ) • (P l * (P k)ᴴ) := by
          simp
    have hkEig : (U : MatrixAlg D) * (P l * (P k)ᴴ) = γ ^ (k : ℕ) • (P l * (P k)ᴴ) := by
      calc
        (U : MatrixAlg D) * (P l * (P k)ᴴ) = ((U : MatrixAlg D) * P l) * (P k)ᴴ := by
          simp [Matrix.mul_assoc]
        _ = (P l * (U : MatrixAlg D)) * (P k)ᴴ := by rw [(hcommUP l).eq]
        _ = P l * ((U : MatrixAlg D) * (P k)ᴴ) := by simp [Matrix.mul_assoc]
        _ = P l * (γ ^ (k : ℕ) • (P k)ᴴ) := by rw [hU_star_left k]
        _ = γ ^ (k : ℕ) • (P l * (P k)ᴴ) := by
          simp
    have hsub : (γ ^ (l : ℕ) - γ ^ (k : ℕ)) • (P l * (P k)ᴴ) = 0 := by
      calc
        (γ ^ (l : ℕ) - γ ^ (k : ℕ)) • (P l * (P k)ᴴ)
            = γ ^ (l : ℕ) • (P l * (P k)ᴴ) - γ ^ (k : ℕ) • (P l * (P k)ᴴ) := by
                simp [sub_smul]
        _ = 0 := by rw [← hlEig, ← hkEig]; simp
    have hneq : γ ^ (l : ℕ) - γ ^ (k : ℕ) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hpow
      exact hkl.symm (hpow_inj hpow)
    exact (smul_eq_zero.mp hsub).resolve_left hneq
  have hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k) := by
    intro k
    have hstar_eq : (P k)ᴴ = P k * (P k)ᴴ := by
      calc
        (P k)ᴴ = (1 : MatrixAlg D) * (P k)ᴴ := by simp
        _ = (∑ l : Fin m, P l) * (P k)ᴴ := by rw [hPsum]
        _ = ∑ l : Fin m, P l * (P k)ᴴ := by simp [Finset.sum_mul]
        _ = P k * (P k)ᴴ := by
            exact Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (by
              intro l hl hne
              simpa using hPmul_star_zero hne.symm)
    have hself_aux : P k = P k * (P k)ᴴ := by
      simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hstar_eq
    refine ⟨hstar_eq.trans hself_aux.symm, hPidem k⟩
  refine ⟨P, hPproj, hPsum, hUspec_sum.symm, hcyclic⟩

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

private def cyclicIndex (k : Fin m) (n : ℕ) : Fin m :=
  ⟨((k : ℕ) + n) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

@[simp] private lemma cyclicIndex_zero (k : Fin m) :
    cyclicIndex (m := m) k 0 = k := by
  ext
  simp [cyclicIndex, Nat.mod_eq_of_lt k.is_lt]

private lemma cyclicIndex_succ (k : Fin m) (n : ℕ) :
    cyclicIndex (m := m) k (n + 1) = cyclicIndex k n + 1 := by
  ext
  change (((k : ℕ) + n) + 1) % m = ((((k : ℕ) + n) % m) + 1 % m) % m
  exact Nat.add_mod ((k : ℕ) + n) 1 m

@[simp] private lemma cyclicIndex_self (k : Fin m) :
    cyclicIndex (m := m) k m = k := by
  ext
  change ((k : ℕ) + m) % m = k
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt k.is_lt]

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
  have hstep :
      ∀ n : ℕ, ∀ k : Fin m, ∀ X : MatrixAlg D,
        (T ^ n) (P (cyclicIndex k n) * X * P (cyclicIndex k n)) =
          P k * ((T ^ n) X) * P k := by
    intro n
    induction n with
    | zero =>
        intro k X
        simp
    | succ n ih =>
        intro k X
        calc
          (T ^ (n + 1))
              (P (cyclicIndex k (n + 1)) * X * P (cyclicIndex k (n + 1)))
              = (T ^ n) (T (P (cyclicIndex k (n + 1)) * X * P (cyclicIndex k (n + 1)))) := by
                  simp [pow_succ]
          _ = (T ^ n) (T (P (cyclicIndex k n + 1) * X * P (cyclicIndex k n + 1))) := by
                  rw [cyclicIndex_succ k n]
          _ = (T ^ n) (P (cyclicIndex k n) * T X * P (cyclicIndex k n)) := by
                  congr 1
                  calc
                    T (P (cyclicIndex k n + 1) * X * P (cyclicIndex k n + 1))
                        = T (P (cyclicIndex k n + 1) * X) * T (P (cyclicIndex k n + 1)) := by
                            exact hMulRight (cyclicIndex k n + 1) (P (cyclicIndex k n + 1) * X)
                    _ = (T (P (cyclicIndex k n + 1)) * T X) * T (P (cyclicIndex k n + 1)) := by
                            rw [hMulLeft (cyclicIndex k n + 1) X]
                    _ = P (cyclicIndex k n) * T X * P (cyclicIndex k n) := by
                            rw [hcyclic (cyclicIndex k n)]
          _ = P k * ((T ^ n) (T X)) * P k := ih k (T X)
          _ = P k * ((T ^ (n + 1)) X) * P k := by
                  simp [pow_succ]
  intro k X
  have hmk : (T ^ m) (P k * X * P k) = P k * ((T ^ m) X) * P k := by
    simpa using hstep m k X
  rw [hmk]
  calc
    P k * (P k * ((T ^ m) X) * P k) * P k
        = (P k * P k) * ((T ^ m) X) * (P k * P k) := by
            simp [Matrix.mul_assoc]
    _ = P k * ((T ^ m) X) * P k := by
            simp [Matrix.mul_assoc, (hPproj k).2]

/-- Permutation-based variant of `preserves_corner_pow_of_cyclic_decomp`.

This isolates the part of Wolf Thm. 6.16 that only needs a permutation action on blocks:
if `T` permutes a family of sector projections via a permutation `σ`, then the `orderOf σ`-th
iterate preserves each sector corner. -/
theorem preserves_corner_pow_orderOf_of_perm_decomp
    {ι : Type*}
    {T : MatrixEnd D}
    (σ : Equiv.Perm ι)
    (P : ι → MatrixAlg D)
    (hPproj : ∀ k : ι, IsOrthogonalProjection (P k))
    (hperm : ∀ k : ι, T (P (σ k)) = P k)
    (hMulLeft : ∀ k : ι, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : ι, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k)) :
    ∀ k : ι, PreservesCorner (P k) (T ^ orderOf σ) := by
  have hstep :
      ∀ n : ℕ, ∀ k : ι, ∀ X : MatrixAlg D,
        (T ^ n) (P ((σ ^ n) k) * X * P ((σ ^ n) k)) =
          P k * ((T ^ n) X) * P k := by
    intro n
    induction n with
    | zero =>
        intro k X
        simp
    | succ n ih =>
        intro k X
        calc
          (T ^ (n + 1)) (P ((σ ^ (n + 1)) k) * X * P ((σ ^ (n + 1)) k))
              = (T ^ n) (T (P ((σ ^ (n + 1)) k) * X * P ((σ ^ (n + 1)) k))) := by
                  simp [pow_succ]
          _ = (T ^ n) (T (P (σ ((σ ^ n) k)) * X * P (σ ((σ ^ n) k)))) := by
                  simp [pow_succ']
          _ = (T ^ n) (P ((σ ^ n) k) * T X * P ((σ ^ n) k)) := by
                  congr 1
                  calc
                    T (P (σ ((σ ^ n) k)) * X * P (σ ((σ ^ n) k))
                        ) = T (P (σ ((σ ^ n) k)) * X) * T (P (σ ((σ ^ n) k))) := by
                              exact hMulRight (σ ((σ ^ n) k)) (P (σ ((σ ^ n) k)) * X)
                    _ = (T (P (σ ((σ ^ n) k))) * T X) * T (P (σ ((σ ^ n) k))) := by
                          rw [hMulLeft (σ ((σ ^ n) k)) X]
                    _ = P ((σ ^ n) k) * T X * P ((σ ^ n) k) := by
                          rw [hperm ((σ ^ n) k)]
          _ = P k * ((T ^ n) (T X)) * P k := ih k (T X)
          _ = P k * ((T ^ (n + 1)) X) * P k := by simp [pow_succ]
  intro k X
  have hmain :
      (T ^ orderOf σ) (P ((σ ^ orderOf σ) k) * X * P ((σ ^ orderOf σ) k)) =
        P k * ((T ^ orderOf σ) X) * P k := hstep (orderOf σ) k X
  have hσ : (σ ^ orderOf σ) = 1 := by
    exact pow_orderOf_eq_one σ
  have hmk : (T ^ orderOf σ) (P k * X * P k) = P k * ((T ^ orderOf σ) X) * P k := by
    simpa [hσ] using hmain
  calc
    P k * (T ^ orderOf σ) (P k * X * P k) * P k
        = P k * (P k * ((T ^ orderOf σ) X) * P k) * P k := by rw [hmk]
    _ = (P k * P k) * ((T ^ orderOf σ) X) * (P k * P k) := by
            simp [Matrix.mul_assoc]
    _ = P k * ((T ^ orderOf σ) X) * P k := by
            simp [Matrix.mul_assoc, (hPproj k).2]
    _ = (T ^ orderOf σ) (P k * X * P k) := by rw [hmk]
/-- Wolf Theorem 6.6 corollary: an orbit-sum lift from invariant corner subprojections to
ambient invariant projections implies irreducibility of the `m`-step dynamics on each cyclic
sector. -/
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

/-- Concrete orbit-sum packaging for the `hLift` hypothesis used in
`isIrreducible_restriction_of_cyclic_decomp`.

Given a candidate corner projection `Q ≤ P k` invariant under `T ^ m`, define
`R = ∑ l : Fin m, (T ^ (l : ℕ)) Q`.  This theorem records the exact shape needed by
`isIrreducible_restriction_of_cyclic_decomp`: once one has proved the four orbit-sum facts
(projection, `T`-corner invariance, and the two endpoint equivalences), the abstract `hLift`
hypothesis is discharged directly. -/
theorem orbitSum_hLift_of_cyclic_decomp
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hLiftOrbit :
      ∀ k : Fin m, ∀ Q : MatrixAlg D,
        IsOrthogonalProjection Q →
        Q * P k = Q →
        P k * Q = Q →
        PreservesCorner Q (T ^ m) →
        let R : MatrixAlg D := ∑ l : Fin m, (T ^ (l : ℕ)) Q
        IsOrthogonalProjection R ∧
          PreservesCorner R T ∧
          (Q = 0 ↔ R = 0) ∧
          (Q = P k ↔ R = 1)) :
    ∀ k : Fin m, ∀ Q : MatrixAlg D,
      IsOrthogonalProjection Q →
      Q * P k = Q →
      P k * Q = Q →
      PreservesCorner Q (T ^ m) →
      ∃ R : MatrixAlg D,
        IsOrthogonalProjection R ∧
        PreservesCorner R T ∧
        (Q = 0 ↔ R = 0) ∧
        (Q = P k ↔ R = 1) := by
  intro k Q hQproj hQP hPQ hQinv
  refine ⟨∑ l : Fin m, (T ^ (l : ℕ)) Q, ?_⟩
  simpa using hLiftOrbit k Q hQproj hQP hPQ hQinv

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
  have hcyclic_pow : ∀ n : ℕ, ∀ k : Fin m, (T ^ n) (P (cyclicIndex k n)) = P k := by
    intro n
    induction n with
    | zero =>
        intro k
        simp
    | succ n ih =>
        intro k
        calc
          (T ^ (n + 1)) (P (cyclicIndex k (n + 1)))
              = (T ^ n) (T (P (cyclicIndex k (n + 1)))) := by
                  simp [pow_succ]
          _ = (T ^ n) (T (P (cyclicIndex k n + 1))) := by
                  rw [cyclicIndex_succ k n]
          _ = (T ^ n) (P (cyclicIndex k n)) := by
                  rw [hcyclic (cyclicIndex k n)]
          _ = P k := ih k
  have hPk_fix : ∀ k : Fin m, (T ^ m) (P k) = P k := by
    intro k
    simpa using hcyclic_pow m k
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
