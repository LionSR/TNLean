/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.EnvironmentDilation
import TNLean.Circuit.Channel.RegisterChannelLift

/-!
# Initializing and discarding appended local environments

The appended environment wires start in a literal product-zero state. The final
partial trace retains the original wires in their original order. These maps are
specified on all operators; no intermediate product-state assumption is made.
-/

open Matrix

namespace QuantumCircuit

noncomputable section

/-- Separate original and appended wire configurations without changing either order. -/
def appendConfigurationSplit (W A d : ℕ) :
    (Fin (W + A) → Fin d) ≃ (Fin W → Fin d) × (Fin A → Fin d) where
  toFun x := (fun i => x (Fin.castAdd A i), fun j => x (Fin.natAdd W j))
  invFun p := Fin.append p.1 p.2
  left_inv x := by
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  right_inv p := by
    ext i <;> simp

@[simp] theorem appendConfigurationSplit_append {W A d : ℕ}
    (x : Fin W → Fin d) (y : Fin A → Fin d) :
    appendConfigurationSplit W A d (Fin.append x y) = (x, y) := by
  ext i <;> simp [appendConfigurationSplit]

/-- Operator coordinates for the original system and appended environment. -/
def appendMatrixSplit (W A d : ℕ) :
    Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ ≃ₐ[ℂ]
      Matrix ((Fin W → Fin d) × (Fin A → Fin d))
        ((Fin W → Fin d) × (Fin A → Fin d)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (appendConfigurationSplit W A d)

/-- Operators on the original wires act as the identity on the entire appended
space, not just on its initialized zero vector. -/
theorem appendMatrixSplit_embedOp {W A d : ℕ}
    (U : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    appendMatrixSplit W A d (embedOp (Fin.castAdd A) U) =
      Matrix.kroneckerMap (· * ·) U (1 : Matrix (Fin A → Fin d) (Fin A → Fin d) ℂ) := by
  have hsplit : registerSumConfigurationSplit (d := d)
      (finSumFinEquiv : Fin W ⊕ Fin A ≃ Fin (W + A)) =
        appendConfigurationSplit W A d := by
    apply Equiv.ext
    intro x
    apply Prod.ext <;> funext i <;> simp [registerSumConfigurationSplit, appendConfigurationSplit]
  simpa only [hsplit, appendMatrixSplit, Fin.coe_castAddEmb] using
    registerSumConfigurationSplit_embedOp (d := d)
    (Fin.castAddEmb A) finSumFinEquiv (fun i => by simp) U

/-- Add a product-zero environment on the appended wires. -/
def appendEnvironmentInput (W A d : ℕ) [NeZero d] :
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ :=
  equivReindexMap (appendConfigurationSplit W A d).symm ∘ₗ
    freshEnvironmentInput (0 : Fin A → Fin d)

/-- Discard precisely the appended wires, retaining the original system. -/
def discardAppendedEnvironment (W A d : ℕ) :
    Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ :=
  partialTraceRightLM ∘ₗ equivReindexMap (appendConfigurationSplit W A d)

/-- The reduced operation in appended-wire coordinates is exactly the ordinary
system/environment unitary formula. -/
theorem discardAppendedEnvironment_conj {W A d : ℕ} [NeZero d]
    (U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ)
    (X : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    discardAppendedEnvironment W A d
      (U * appendEnvironmentInput W A d X * Uᴴ) =
      partialTraceRight
        (appendMatrixSplit W A d U * freshEnvironmentInput (0 : Fin A → Fin d) X *
          (appendMatrixSplit W A d U)ᴴ) := by
  let R := appendMatrixSplit W A d
  have hstar (Y : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ) :
      R Yᴴ = (R Y)ᴴ := rfl
  change partialTraceRight (R (U * R.symm (freshEnvironmentInput (0 : Fin A → Fin d) X) *
    Uᴴ)) = _
  simp only [map_mul, hstar, R.apply_symm_apply]
  rfl

/-- Appending an unused pure environment does not alter an operation on the original
wires. This includes the empty-environment boundary. -/
theorem discardAppendedEnvironment_lift {W A d : ℕ} [NeZero d]
    (U : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    discardAppendedEnvironment W A d ∘ₗ singleKrausMap (embedOp (Fin.castAdd A) U) ∘ₗ
      appendEnvironmentInput W A d = singleKrausMap U := by
  apply LinearMap.ext
  intro X
  change discardAppendedEnvironment W A d
    (_ * appendEnvironmentInput W A d X * _) = _
  rw [discardAppendedEnvironment_conj, appendMatrixSplit_embedOp,
    freshEnvironmentInput_eq_kronecker]
  rw [partialTraceRight_kronecker_conj_of_right_isometry U (1 : Matrix
    (Fin A → Fin d) (Fin A → Fin d) ℂ) (by simp)]
  rw [partialTraceRight_kronecker]
  simp

end

end QuantumCircuit
