/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition.Basic

/-!
# Peripheral unitaries for irreducible Schwarz maps

This file develops the first part of Wolf Theorem 6.6 for transfer maps of
Kraus families.

## Main statements

* `fixed_eq_scalar_of_irreducible_unital` — every fixed point of an
  irreducible unital Kraus map is scalar.
* `exists_peripheral_unitary_of_irreducible_schwarz` — a peripheral eigenvalue
  admits a unitary eigenvector.
* `map_powers_of_peripheral_unitary` — powers of that unitary remain peripheral
  eigenvectors.
* `exists_normalized_peripheral_unitary_of_irreducible_schwarz` — the unitary
  may be normalized to have exact order `m`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

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
  by_cases h : i = j
  · subst h
    have hone : ((↑c : ℂ) • (1 : MatrixAlg D)) i i = ↑c := by
      change ((↑c : ℂ) • ((1 : MatrixAlg D) i)) i = ↑c
      rw [Pi.smul_apply, Matrix.one_apply_eq]
      simp only [smul_eq_mul, mul_one]
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hone]
    simp only [ofReal_sub]
  · have hone : ((↑c : ℂ) • (1 : MatrixAlg D)) i j = 0 := by
      change ((↑c : ℂ) • ((1 : MatrixAlg D) i)) j = 0
      rw [Pi.smul_apply, Matrix.one_apply_ne h]
      simp only [smul_eq_mul, mul_zero]
    rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, hone]
    simp only [sub_self]

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
          = transferMap (d := r) (D := D) K H -
              transferMap (d := r) (D := D) K ((c0 : ℂ) • (1 : MatrixAlg D)) := by
              rw [LinearMap.map_sub]
      _ = transferMap (d := r) (D := D) K H -
            (c0 : ℂ) • transferMap (d := r) (D := D) K 1 := by
              rw [LinearMap.map_smul]
      _ = H - (c0 : ℂ) • 1 := by simp only [hfix, hone_fix, Complex.coe_smul]
  have hone_psd : (1 : MatrixAlg D).PosSemidef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := K) hIrr
      (1 : MatrixAlg D) (H - (c0 : ℂ) • 1) hone_psd one_ne_zero hshift_psd hone_fix hshift_fix with
    ⟨d, hd⟩
  refine ⟨d + c0, ?_⟩
  calc
    H = (H - (c0 : ℂ) • 1) + (c0 : ℂ) • 1 := by abel
    _ = d • 1 + (c0 : ℂ) • 1 := by rw [hd]
    _ = (d + c0) • 1 := by simp only [Complex.coe_smul, add_smul]

/-- For an irreducible unital Kraus map, every fixed point is a scalar multiple
of the identity matrix. -/
theorem fixed_eq_scalar_of_irreducible_unital
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
      _ = X + Xᴴ := by simp only [hfix, hfix_star]
  have hSkew_fix :
      transferMap (d := r) (D := D) K (Complex.I • (X - Xᴴ)) = Complex.I • (X - Xᴴ) := by
    calc
      transferMap (d := r) (D := D) K (Complex.I • (X - Xᴴ))
          = Complex.I • transferMap (d := r) (D := D) K (X - Xᴴ) := by
              simp only [map_smul, transferMap_apply]
      _ = Complex.I • (transferMap (d := r) (D := D) K X - transferMap (d := r) (D := D) K Xᴴ) := by
              simpa using congrArg (fun M => Complex.I • M)
                ((transferMap (d := r) (D := D) K).map_sub X Xᴴ)
      _ = Complex.I • (X - Xᴴ) := by simp only [hfix, hfix_star]
  have hHerm_herm : (X + Xᴴ).IsHermitian := by
    simp only [IsHermitian, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  have hSkew_herm : (Complex.I • (X - Xᴴ)).IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    change star (Complex.I * (X j i - star (X i j))) = Complex.I * (X i j - star (X j i))
    simp only [Complex.star_def, StarMul.star_mul, star_sub, Complex.conj_I,
      Complex.conj_conj]
    ring
  rcases hermitian_fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr (X + Xᴴ) hHerm_herm hHerm_fix with ⟨a, ha⟩
  rcases hermitian_fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrr (Complex.I • (X - Xᴴ)) hSkew_herm hSkew_fix with ⟨b, hb⟩
  refine ⟨(1 / 2 : ℂ) * (a - Complex.I * b), ?_⟩
  have hrecon :
      (X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ)) = (2 : ℂ) • X := by
    calc
      (X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ)) = (X + Xᴴ) + (X - Xᴴ) := by
            simp only [
              sub_eq_add_neg, smul_add, smul_neg, smul_smul, I_mul_I, neg_smul,
              one_smul, neg_add_rev, add_right_inj
            ]
            abel
      _ = (2 : ℂ) • X := by
            ext i j
            simp only [
              sub_eq_add_neg, add_apply, conjTranspose_apply, RCLike.star_def,
              neg_apply, add_left_comm, add_assoc, add_neg_cancel, add_zero,
              smul_apply, smul_eq_mul, two_mul
            ]
  calc
    X = (1 / 2 : ℂ) • ((2 : ℂ) • X) := by
      simp only [
        one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀
      ]
    _ = (1 / 2 : ℂ) • ((X + Xᴴ) - Complex.I • (Complex.I • (X - Xᴴ))) := by
          rw [← hrecon]
    _ = (1 / 2 : ℂ) • ((a • (1 : MatrixAlg D)) - Complex.I • (b • (1 : MatrixAlg D))) := by
          rw [ha, hb]
    _ = ((1 / 2 : ℂ) * (a - Complex.I * b)) • (1 : MatrixAlg D) := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp only [
              one_div, sub_eq_add_neg, smul_apply, add_apply, one_apply_eq, smul_eq_mul,
              mul_one, neg_apply, mul_comm, mul_left_comm, one_mul
            ]
          · simp only [
              one_div, smul_apply, sub_apply, ne_eq, hij, not_false_eq_true, one_apply_ne,
              smul_eq_mul, mul_zero, sub_self
            ]

section PeripheralUnitary

/-- A peripheral eigenvalue of an irreducible unital Schwarz transfer map admits a unitary
matrix eigenvector.

This is the unitary part of Wolf Theorem 6.6. The formulation is stated for transfer maps of
Kraus families because the available Kadison--Schwarz / multiplicative-domain interface is implemented
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
    simp only [normSq_eq_norm_sq, hγ_norm, one_pow, ofReal_one]
  have hγ_starRing_mul : (starRingEnd ℂ) γ * γ = 1 := by
    simpa [Complex.star_def] using hγ_star_mul
  have hXX_fix_map : Kraus.map K (Xᴴ * X) = Xᴴ * X := by
    calc
      Kraus.map K (Xᴴ * X) = (Kraus.map K X)ᴴ * Kraus.map K X := hKS_map
      _ = (γ • X)ᴴ * (γ • X) := by rw [hEig_map]
      _ = ((starRingEnd ℂ) γ * γ) • (Xᴴ * X) := by
            simp only [
              conjTranspose_smul, RCLike.star_def, Algebra.mul_smul_comm,
              Algebra.smul_mul_assoc, smul_smul, mul_comm
            ]
      _ = Xᴴ * X := by simp only [hγ_starRing_mul, one_smul]
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
    simp only [hXX_scalar, hc0, zero_smul]
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
      _ = 0 := by simp only [h0, ofReal_zero]
  have hcre_pos : 0 < c.re := lt_of_le_of_ne hcre_nonneg (Ne.symm hcre_ne0)
  set a : ℂ := (Real.sqrt c.re : ℂ)
  have ha_ne0 : a ≠ 0 := by
    have hsqrt_ne : ((Real.sqrt c.re : ℂ)) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr hcre_pos
    simpa [a] using hsqrt_ne
  have hstar_a : star a = a := by
    simp only [RCLike.star_def, conj_ofReal, a]
  have hstar_a_inv : (starRingEnd ℂ) a⁻¹ = a⁻¹ := by
    rw [map_inv₀]
    simpa [Complex.star_def] using hstar_a
  have hstar_a_inv' : star a⁻¹ = a⁻¹ := by
    simpa [Complex.star_def] using hstar_a_inv
  have hc_eq_sq : c = a * a := by
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = (((Real.sqrt c.re) ^ 2 : ℝ) : ℂ) := by
            simp only [Real.sq_sqrt hcre_nonneg]
      _ = a * a := by
            rw [pow_two]
            simp only [ofReal_mul, a]
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
            simp only [hscalar, one_smul]⟩, ?_⟩
  calc
    transferMap (d := r) (D := D) K (a⁻¹ • X) = a⁻¹ • transferMap (d := r) (D := D) K X := by
          simp only [map_smul, transferMap_apply]
    _ = a⁻¹ • (γ • X) := by rw [hEig_transfer]
    _ = γ • (a⁻¹ • X) := by simp only [smul_smul, mul_comm]

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
      _ = (U : MatrixAlg D) ^ m := by simp only [hγprim.pow_eq_one, one_smul]
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
      _ = ‖α⁻¹‖ := by simp only [hβm, norm_inv]
      _ = 1 := by simp only [norm_inv, hα_norm, inv_one]
  have hβ_norm : ‖β‖ = 1 := by
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg β) (NeZero.ne m)).1 hβ_norm_pow
  have hβ_unit : star β * β = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp only [normSq_eq_norm_sq, hβ_norm, one_pow, ofReal_one]
  have hβ_starRing_mul : (starRingEnd ℂ) β * β = 1 := by
    simpa [Complex.star_def] using hβ_unit
  have hU_star_mul : ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  refine ⟨⟨β • (U : MatrixAlg D), by
    rw [Matrix.mem_unitaryGroup_iff']
    calc
      (β • (U : MatrixAlg D))ᴴ * (β • (U : MatrixAlg D)) =
          ((starRingEnd ℂ) β * β) • ((U : MatrixAlg D)ᴴ * (U : MatrixAlg D)) := by
            simp only [
              conjTranspose_smul, RCLike.star_def, Algebra.mul_smul_comm,
              Algebra.smul_mul_assoc, smul_smul, mul_comm
            ]
      _ = 1 := by rw [hβ_starRing_mul, hU_star_mul]; simp only [one_smul]⟩, ?_, ?_⟩
  · calc
      transferMap (d := r) (D := D) K (β • (U : MatrixAlg D))
          = β • transferMap (d := r) (D := D) K (U : MatrixAlg D) := by
              simp only [map_smul, transferMap_apply]
      _ = β • (γ • (U : MatrixAlg D)) := by rw [hU]
      _ = γ • (β • (U : MatrixAlg D)) := by simp only [smul_smul, mul_comm]
  · calc
      (β • (U : MatrixAlg D)) ^ m = β ^ m • ((U : MatrixAlg D) ^ m) := by
            simpa using smul_pow β (U : MatrixAlg D) m
      _ = β ^ m • (α • (1 : MatrixAlg D)) := by rw [hUm_scalar]
      _ = ((β ^ m) * α) • (1 : MatrixAlg D) := by rw [smul_smul]
      _ = 1 := by
            have hα_ne0 : α ≠ 0 := by
              intro h0
              simp only [h0, star_zero, mul_zero, zero_ne_one] at hα_unit
            simp only [hβm, ne_eq, hα_ne0, not_false_eq_true, inv_mul_cancel₀, one_smul]

end PeripheralUnitary

end MPSTensor
