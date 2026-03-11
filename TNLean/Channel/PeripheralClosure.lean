/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PeripheralPowers
import TNLean.Channel.MultiplicativeDomainPowers
import TNLean.QPF.PosDef
import TNLean.MPS.Transfer

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Peripheral eigenvalues closed under powers

This file provides the missing “closure under powers” lemma for peripheral
(eigenvalue-norm $=1$) eigenvalues of **irreducible, bi-canonical** Kraus maps.

The key ingredients are:

* multiplicative-domain / Kadison–Schwarz theory (`MultiplicativeDomainPowers`)
  giving the *eigenvector* identity `E(X^n)=μ^n X^n` when `‖μ‖=1`, and
* quantum Perron–Frobenius (`QPF.PosDef`) turning a nonzero PSD fixed point into a
  positive definite one under irreducibility, which then implies `X` is invertible.

The main lemma is intended to feed directly into
`TNLean/Channel/PeripheralPowers.lean` via
`peripheral_isRootOfUnity_of_closed_powers`.
-/


open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace MPSTensor

/-! ## Task A: `transferMap` equals `krausMapL` -/

/-- The MPS transfer map is exactly the Kraus map packaged as a `ℂ`-linear map. -/
theorem transferMap_eq_krausMapL {d D : ℕ}
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    MPSTensor.transferMap (d := d) (D := D) K
      = KadisonSchwarz.krausMapL (d := d) (D := D) K := by
  ext X
  simp [MPSTensor.transferMap_apply, KadisonSchwarz.krausMapL_apply, KadisonSchwarz.krausMap]

end MPSTensor

/-! ## Task B: peripheral eigenvalues are closed under powers -/

/-- **Peripheral eigenvalues are closed under powers** for irreducible, bi-canonical
(unital + trace-preserving) Kraus maps.

This is the missing step needed for the standard “peripheral eigenvalues are roots of
unity” argument. -/
theorem peripheralEigenvalues_pow_mem_of_irreducible_biCanonical
    {d D : ℕ} [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus K)
    (h_tp : KadisonSchwarz.IsTPKraus K)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := d) (D := D) K)) :
    ∀ μ : ℂ,
      μ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) →
        ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) := by
  classical
  intro μ hμ n
  rcases hμ with ⟨hμ_eig, hμ_norm⟩
  -- Extract a nonzero eigenvector `X` with `E X = μ • X`.
  rcases hμ_eig.exists_hasEigenvector with ⟨X, hX_eigvec⟩
  have hX_mem :
      X ∈ Module.End.eigenspace (MPSTensor.transferMap (d := d) (D := D) K) μ :=
    (Module.End.hasEigenvector_iff.mp hX_eigvec).1
  have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX_eigvec).2
  have hEig_transfer : MPSTensor.transferMap (d := d) (D := D) K X = μ • X :=
    (Module.End.mem_eigenspace_iff).1 hX_mem
  -- Rewrite the eigenvector equation in terms of `krausMap`.
  have hEig_kraus : KadisonSchwarz.krausMap (d := d) (D := D) K X = μ • X := by
    simpa [MPSTensor.transferMap_apply, KadisonSchwarz.krausMap] using hEig_transfer
  -- KS equality holds at peripheral eigenvectors.
  have hKS :
      KadisonSchwarz.krausMap (d := d) (D := D) K (Xᴴ * X)
        = (KadisonSchwarz.krausMap (d := d) (D := D) K X)ᴴ
            * KadisonSchwarz.krausMap (d := d) (D := D) K X :=
    KadisonSchwarz.ks_equality_of_peripheral_eigenvector (K := K) h_unital h_tp X μ
      hEig_kraus hμ_norm
  -- Hence `Xᴴ * X` is a PSD fixed point.
  have hμ_star_mul : star μ * μ = 1 := by
    -- same computation as in `MultiplicativeDomain.lean`
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hμ_norm]
  have hfix_kraus : KadisonSchwarz.krausMap (d := d) (D := D) K (Xᴴ * X) = Xᴴ * X := by
    calc
      KadisonSchwarz.krausMap (d := d) (D := D) K (Xᴴ * X)
          = (KadisonSchwarz.krausMap (d := d) (D := D) K X)ᴴ
              * KadisonSchwarz.krausMap (d := d) (D := D) K X := hKS
      _ = (μ • X)ᴴ * (μ • X) := by simp [hEig_kraus]
      _ = (star μ * μ) • (Xᴴ * X) := by
            -- `simp` computes the scalar factor as `μ * star μ`; commutativity fixes the order.
            simp [conjTranspose_smul, smul_smul, mul_comm]
      _ = Xᴴ * X := by
            -- Rewrite `star μ` into the bundled `starRingEnd` form used by simp.
            have hμ_starRingEnd_mul : ((starRingEnd ℂ) μ) * μ = 1 := by
              simpa [Complex.star_def] using hμ_star_mul
            simp [hμ_starRingEnd_mul]
  have hfix_transfer : MPSTensor.transferMap (d := d) (D := D) K (Xᴴ * X) = Xᴴ * X := by
    simpa [MPSTensor.transferMap_apply, KadisonSchwarz.krausMap] using hfix_kraus
  have hρ_psd : (Xᴴ * X).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self X
  have hρ_ne : Xᴴ * X ≠ 0 := by
    intro h
    apply hX_ne
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h
  -- Irreducibility upgrades a nonzero PSD fixed point to positive definite.
  have hρ_posdef : (Xᴴ * X).PosDef :=
    MPSTensor.posSemidef_fixedPoint_isPosDef_of_irreducible (A := K) (d := d) (D := D)
      hIrr (ρ := Xᴴ * X) hρ_psd hρ_ne hfix_transfer
  -- From positive definiteness, `Xᴴ * X` is a unit, hence has nonzero determinant.
  have hUnit_rho : IsUnit (Xᴴ * X) := Matrix.PosDef.isUnit hρ_posdef
  have hUnit_det_rho : IsUnit ((Xᴴ * X).det) :=
    (Matrix.isUnit_iff_isUnit_det (Xᴴ * X)).1 hUnit_rho
  have hdet_rho_ne : (Xᴴ * X).det ≠ 0 := hUnit_det_rho.ne_zero
  -- `det (Xᴴ * X) = star(det X) * det X`, so `det X ≠ 0`.
  have hdet_rho_eq : (Xᴴ * X).det = star X.det * X.det := by
    calc
      (Xᴴ * X).det = (Xᴴ).det * X.det := Matrix.det_mul _ _
      _ = star X.det * X.det := by simp [Matrix.det_conjTranspose]
  have hdetX_ne : X.det ≠ 0 := by
    intro hdetX0
    apply hdet_rho_ne
    -- If `det X = 0`, then `det (Xᴴ * X) = 0`.
    simp [hdet_rho_eq, hdetX0]
  -- Hence `X` is a unit, so all powers are nonzero.
  have hUnit_detX : IsUnit X.det := (isUnit_iff_ne_zero).2 hdetX_ne
  have hUnit_X : IsUnit X := (Matrix.isUnit_iff_isUnit_det X).2 hUnit_detX
  have hXpow_ne : X ^ n ≠ 0 := by
    have hUnit_Xpow : IsUnit (X ^ n) := IsUnit.pow n hUnit_X
    exact hUnit_Xpow.ne_zero
  -- Apply the multiplicative-domain powers lemma to get `μ^n` as an eigenvalue.
  have hEigPow_kraus :
      Module.End.HasEigenvalue (KadisonSchwarz.krausMapL (d := d) (D := D) K) (μ ^ n) :=
    KadisonSchwarz.hasEigenvalue_pow_of_peripheral_eigenvector (K := K) h_unital h_tp X μ
      hEig_kraus hμ_norm n hXpow_ne
  have hEigPow_transfer :
      Module.End.HasEigenvalue (MPSTensor.transferMap (d := d) (D := D) K) (μ ^ n) := by
    simpa [MPSTensor.transferMap_eq_krausMapL (K := K)] using hEigPow_kraus
  refine ⟨hEigPow_transfer, norm_pow_eq_one_of_norm_eq_one hμ_norm n⟩

/-! ## Task C: roots of unity wrapper (optional) -/

/-- For irreducible, bi-canonical (unital + trace-preserving) Kraus maps,
every peripheral eigenvalue is a root of unity.

This is a thin wrapper around `peripheral_isRootOfUnity_of_closed_powers`. -/
theorem peripheral_isRootOfUnity_of_irreducible_biCanonical
    {d D : ℕ} [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus K)
    (h_tp : KadisonSchwarz.IsTPKraus K)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := d) (D := D) K)) :
    ∀ μ : ℂ,
      μ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) →
        ∃ p : ℕ, 0 < p ∧ μ ^ p = 1 := by
  intro μ hμ
  classical
  have hclosed : ∀ ν : ℂ,
      ν ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) →
        ∀ n : ℕ, ν ^ n ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) :=
    peripheralEigenvalues_pow_mem_of_irreducible_biCanonical (K := K) h_unital h_tp hIrr
  exact peripheral_isRootOfUnity_of_closed_powers (E := MPSTensor.transferMap (d := d) (D := D) K)
    hclosed μ hμ
