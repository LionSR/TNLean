/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PeripheralSpectrum
import TNLean.Channel.PeripheralClosure
import TNLean.Channel.PeripheralClosureFixedPoint
import TNLean.Channel.Schwarz
import TNLean.QPF.Uniqueness
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
  sorry

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
  sorry

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
  sorry

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
  sorry

end MPSTensor

section PrimitivityOfSectors

variable {D m : ℕ} [NeZero m]

/-- The `m`-th power of the channel preserves each cyclic corner `P_k · M_D(ℂ) · P_k`. -/
theorem preserves_corner_pow_of_cyclic_decomp
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k) :
    ∀ k : Fin m, PreservesCorner (P k) (T ^ m) := by
  sorry

/-- Wolf Theorem 6.6 corollary: the `m`-step dynamics on each cyclic sector is irreducible. -/
theorem isIrreducible_restriction_of_cyclic_decomp
    {T : MatrixEnd D}
    (hIrr : IsIrreducibleMap T)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k) :
    ∀ k : Fin m, IsIrreducibleOnCorner (P k) (T ^ m) := by
  sorry

/-- Wolf Theorem 6.6 corollary: the `m`-step dynamics on each cyclic sector is primitive. -/
theorem isPrimitive_restriction_of_cyclic_decomp
    {T : MatrixEnd D} {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)))
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k) :
    ∀ k : Fin m,
      IsPrimitive
        (cornerRestriction (P k) (T ^ m)
          (preserves_corner_pow_of_cyclic_decomp (T := T) P hPproj hPsum hcyclic k)) := by
  sorry

end PrimitivityOfSectors
