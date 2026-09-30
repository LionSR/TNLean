/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.OrbitPhaseTwist
import TNLean.MPS.SharedInfra.IsometricBlockAssembly

/-!
# A common unitary for the blocked tensor and all orbit phase twists

The unitary identifying a blocked periodic tensor with its orbit direct sum
is independent of the phases subsequently assigned to those orbit blocks.
Every permitted phase family is realized by a trace-preserving one-site
root in the original bond space.

Source: arXiv:1708.00029, equations `eq:ZPA-is-cPA` and
`eq:Aprime-is-cPA`, lines 765--806.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- One unitary identifies the blocked tensor and all of its permitted
orbit phase twists with the corresponding weighted orbit direct sums.
Source: arXiv:1708.00029, equations `eq:ZPA-is-cPA` and
`eq:Aprime-is-cPA`, lines 765--806. -/
theorem IsPeriodic.exists_unitary_phaseTwisted_orbit_decomposition
    {d D m : ℕ} [NeZero m] (A : MPSTensor d D)
    (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    ∃ (dim : Fin (Nat.gcd m p) → ℕ)
      (C : (j : Fin (Nat.gcd m p)) → MPSTensor (blockPhysDim d p) (dim j))
      (Y : Matrix (Fin D) (Fin (∑ j, dim j)) ℂ),
      (∀ j, dim j ≠ 0) ∧
      (∀ j, IsPeriodic (m / Nat.gcd m p) (C j)) ∧
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      (∀ I, blockTensor A p I =
        Y * toTensorFromBlocks (fun _ => 1) C I * Yᴴ) ∧
      ∀ c : Fin (Nat.gcd m p) → Circle,
        (∀ j, c j ^ (m / Nat.gcd m p) = 1) →
        ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧
          ∀ I, blockTensor A' p I =
            Y * toTensorFromBlocks (fun j => (c j : ℂ)) C I * Yᴴ := by
  obtain ⟨dim, C, V, hdim, hPer, hV, hVsum, hletter, hTwist⟩ :=
    hA.exists_phaseTwisted_orbit_decomposition A hp
  obtain ⟨Y, hY, hY', hdiag⟩ := exists_unitary_of_isometric_block_decomposition V hV hVsum
  refine ⟨dim, C, Y, hdim, hPer, hY, hY', ?_, ?_⟩
  · intro I
    rw [hletter]
    simpa only [toTensorFromBlocks, one_smul] using (hdiag (fun j => C j I)).symm
  · intro c hc
    obtain ⟨A', hTP, hA'⟩ := hTwist c hc
    refine ⟨A', hTP, ?_⟩
    intro I
    rw [hA']
    simpa only [toTensorFromBlocks, Matrix.mul_smul, Matrix.smul_mul] using
      (hdiag (fun j => (c j : ℂ) • C j I)).symm

end MPSTensor
