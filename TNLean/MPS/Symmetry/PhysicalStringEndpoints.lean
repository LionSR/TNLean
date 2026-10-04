/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.StringOrderDefs
import TNLean.MPS.Core.PhysicalRotation
import Mathlib.Data.Matrix.Basis

/-!
# Physical endpoints for string order

The endpoint coefficients of the physical string correlator are paired by
\(y = x^\dagger u_0\), where \(u_0\) is the physical symmetry with its peripheral
phase removed. Their nonvanishing is equivalent to a nonzero coefficient
\(\operatorname{tr}(V\Lambda A_n A_m^\dagger)\).

All statements fix the twist and its virtual intertwiner. No claim about the
existence of a nontrivial physical symmetry is imposed on this algebraic result.

Source: Pérez-García–Wolf–Sanz–Verstraete–Cirac, arXiv:0802.0447,
lines 241--276.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Removing a unit-modulus scalar phase preserves physical unitarity.
This is the phase shift preceding Theorem 1 of arXiv:0802.0447, lines 257--263. -/
theorem phaseShiftedPhysicalUnitary_mul_conjTranspose
    (u : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ)
    (hu : u * uᴴ = 1) (hμ : ‖μ‖ = 1) :
    (μ⁻¹ • u) * (μ⁻¹ • u)ᴴ = 1 := by
  have hμne : μ ≠ 0 := by
    intro h
    simp [h] at hμ
  have hp : μ⁻¹ * star (μ⁻¹) = 1 := by
    change μ⁻¹ * starRingEnd ℂ (μ⁻¹) = 1
    rw [map_inv₀, ← Complex.inv_eq_conj hμ, inv_inv, inv_mul_cancel₀ hμne]
  rw [Matrix.conjTranspose_smul, smul_mul_smul_comm, hu, hp, one_smul]

/-- Removing the peripheral phase gives an unphased local intertwining relation.
Source: arXiv:0802.0447, lines 257--263. -/
theorem rotatePhysical_phaseShift
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ) (hμ : μ ≠ 0)
    (hInter : ∀ i, rotatePhysical u A i = μ • (V * A i * Vᴴ)) (i : Fin d) :
    rotatePhysical (μ⁻¹ • u) A i = V * A i * Vᴴ := by
  calc
    rotatePhysical (μ⁻¹ • u) A i = μ⁻¹ • rotatePhysical u A i := by
      simp [rotatePhysical, Finset.smul_sum, smul_smul]
    _ = V * A i * Vᴴ := by rw [hInter, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- A physical twist mixes the left Kraus family in the transfer contraction. -/
lemma twistedTransferMap_eq_sum_rotatePhysical
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    twistedTransferMap A u X = ∑ i, rotatePhysical u A i * X * (A i)ᴴ := by
  rw [twistedTransferMap_apply, Finset.sum_comm]
  simp only [rotatePhysical, Finset.sum_mul, smul_mul_assoc]

/-- Taking adjoints in the physical and virtual arguments takes the adjoint of
the twisted transfer output. -/
lemma twistedTransferMap_conjTranspose
    (A : MPSTensor d D) (x : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    twistedTransferMap A xᴴ Xᴴ = (twistedTransferMap A x X)ᴴ := by
  simp only [twistedTransferMap_apply, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  simp only [Matrix.mul_assoc]

/-- The physical endpoint \(y=xu\) contracts to \(V\mathcal E_x(V^\dagger)\)
when the physical twist has an unphased virtual intertwiner.
Source: arXiv:0802.0447, lines 257--263. -/
lemma twistedTransferMap_mul_intertwiner
    (A : MPSTensor d D) (u x : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ)
    (hInter : ∀ i, rotatePhysical u A i = V * A i * Vᴴ) :
    twistedTransferMap A (x * u) 1 = V * twistedTransferMap A x Vᴴ := by
  rw [twistedTransferMap_eq_sum_rotatePhysical,
    ← rotatePhysical_rotatePhysical]
  rw [show rotatePhysical u A = (fun i => V * A i * Vᴴ) from funext hInter]
  simp only [Matrix.mul_one, rotatePhysical, Finset.sum_mul,
    smul_mul_assoc, Matrix.mul_assoc]
  rw [twistedTransferMap_apply, Matrix.mul_sum, Finset.sum_comm]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.mul_assoc]

/-- The physical endpoints \(x\) and \(x^\dagger u\) have conjugate string-order
coefficients for an unphased virtual intertwiner.
Source: arXiv:0802.0447, lines 257--263. -/
theorem physicalStringEndpoint_pairing
    (A : MPSTensor d D) (Λ V : Matrix (Fin D) (Fin D) ℂ)
    (u x : Matrix (Fin d) (Fin d) ℂ)
    (hΛ : Λ.IsHermitian) (hV : V * Vᴴ = 1)
    (hInter : ∀ i, rotatePhysical u A i = V * A i * Vᴴ) :
    Matrix.trace (Λ * Vᴴ * twistedTransferMap A (xᴴ * u) 1) =
      starRingEnd ℂ (Matrix.trace (Λ * twistedTransferMap A x V)) := by
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  rw [twistedTransferMap_mul_intertwiner A u xᴴ V hInter,
    ← Matrix.mul_assoc, Matrix.mul_assoc Λ Vᴴ V, hV', Matrix.mul_one,
    twistedTransferMap_conjTranspose]
  calc
    Matrix.trace (Λ * (twistedTransferMap A x V)ᴴ) =
        Matrix.trace ((Λ * twistedTransferMap A x V)ᴴ) := by
      rw [Matrix.conjTranspose_mul, hΛ.eq, Matrix.trace_mul_comm]
    _ = starRingEnd ℂ (Matrix.trace (Λ * twistedTransferMap A x V)) :=
      Matrix.trace_conjTranspose _

/-- The conjugated coefficient of the physical matrix entry \(y_{mn}\) is the
source trace \(\operatorname{tr}(V\Lambda A_m A_n^\dagger)\).
Source: arXiv:0802.0447, lines 263--273. -/
lemma physicalStringEndpoint_coefficient
    (A : MPSTensor d D) (Λ V : Matrix (Fin D) (Fin D) ℂ)
    (hΛ : Λ.IsHermitian) (n m : Fin d) :
    starRingEnd ℂ (Matrix.trace (Λ * Vᴴ * (A n * (A m)ᴴ))) =
      Matrix.trace (V * Λ * A m * (A n)ᴴ) := by
  calc
    starRingEnd ℂ (Matrix.trace (Λ * Vᴴ * (A n * (A m)ᴴ))) =
        Matrix.trace ((A m * (A n)ᴴ) * (V * Λ)) := by
      change star (Matrix.trace (Λ * Vᴴ * (A n * (A m)ᴴ))) = _
      rw [← Matrix.trace_conjTranspose]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hΛ.eq]
    _ = Matrix.trace (V * Λ * A m * (A n)ᴴ) := by
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc (V * Λ)]

/-- The left-eigenvector coefficient is nonzero for some physical endpoint exactly
when one of the source matrix coefficients is nonzero. A matrix unit suffices.
Source: arXiv:0802.0447, lines 263--273. -/
theorem exists_physicalStringEndpoint_left_iff
    (A : MPSTensor d D) (Λ V : Matrix (Fin D) (Fin D) ℂ)
    (hΛ : Λ.IsHermitian) :
    (∃ y : Matrix (Fin d) (Fin d) ℂ,
      Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) ≠ 0) ↔
      ∃ n m : Fin d, Matrix.trace (V * Λ * A n * (A m)ᴴ) ≠ 0 := by
  constructor
  · rintro ⟨y, hy⟩
    by_contra! hz
    apply hy
    have hcoeff : ∀ n m : Fin d,
        Matrix.trace (Λ * Vᴴ * (A n * (A m)ᴴ)) = 0 := by
      intro n m
      have h := physicalStringEndpoint_coefficient A Λ V hΛ n m
      rw [hz m n] at h
      simpa using congrArg (starRingEnd ℂ) h
    simp only [twistedTransferMap_apply, Matrix.mul_one, Matrix.mul_sum,
      Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul]
    simp [hcoeff]
  · rintro ⟨n, m, h⟩
    refine ⟨Matrix.single n m 1, ?_⟩
    intro hzero
    have hs : Matrix.trace (Λ * Vᴴ * (A m * (A n)ᴴ)) = 0 := by
      simpa [twistedTransferMap_apply, Matrix.single_apply, ite_and] using hzero
    have hc := physicalStringEndpoint_coefficient A Λ V hΛ m n
    exact h (by simpa [hs] using hc.symm)

/-- For a fixed physical unitary and virtual intertwiner, both physical endpoint
coefficients can be nonzero exactly when the source trace condition holds.
The endpoints can be chosen with \(y=x^\dagger u\).
Source: arXiv:0802.0447, lines 257--273. -/
theorem exists_physicalStringEndpoints_iff
    (A : MPSTensor d D) (Λ V : Matrix (Fin D) (Fin D) ℂ)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hΛ : Λ.IsHermitian) (hu : u * uᴴ = 1) (hV : V * Vᴴ = 1)
    (hInter : ∀ i, rotatePhysical u A i = V * A i * Vᴴ) :
    (∃ x y : Matrix (Fin d) (Fin d) ℂ,
      Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) ≠ 0 ∧
      Matrix.trace (Λ * twistedTransferMap A x V) ≠ 0) ↔
      ∃ n m : Fin d, Matrix.trace (V * Λ * A n * (A m)ᴴ) ≠ 0 := by
  constructor
  · rintro ⟨x, y, hy, _⟩
    exact (exists_physicalStringEndpoint_left_iff A Λ V hΛ).mp ⟨y, hy⟩
  · intro h
    obtain ⟨y, hy⟩ := (exists_physicalStringEndpoint_left_iff A Λ V hΛ).mpr h
    refine ⟨u * yᴴ, y, hy, ?_⟩
    have hu' : uᴴ * u = 1 := mul_eq_one_comm.mp hu
    have hp := physicalStringEndpoint_pairing A Λ V u (u * yᴴ) hΛ hV hInter
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, hu', Matrix.mul_one] at hp
    intro hz
    rw [hz, map_zero] at hp
    exact hy (by simpa only [Matrix.mul_assoc] using hp)

end MPSTensor
