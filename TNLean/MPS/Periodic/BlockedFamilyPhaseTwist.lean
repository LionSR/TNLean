/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.OrbitPhaseTwist
import TNLean.MPS.Periodic.UnitBlockTracePreserving
import TNLean.MPS.SharedInfra.NestedIsometricBlockAssembly
import TNLean.MPS.CanonicalForm.CPSVBlocking

/-!
# Simultaneous orbit phase twists of a weighted periodic family

The orbit decompositions of all periodic blocks are flattened using one
unitary on the full bond space. Every permitted orbit phase family is then
realized by twisting the one-site blocks. Unit-modulus outer weights make
the assembled one-site tensor trace preserving.

Source: arXiv:1708.00029, equations `eq:ZPA-is-cPA` and
`eq:Aprime-is-cPA`, lines 765--810.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The literal blocked decomposition and every permitted orbit phase twist
of a weighted periodic family share one global unitary. Trace preservation
of the twisted root follows when the outer weights have unit modulus.
Source: arXiv:1708.00029, equations `eq:ZPA-is-cPA` and
`eq:Aprime-is-cPA`, lines 765--810. -/
theorem exists_unitary_phaseTwisted_block_family
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ)
    (period : Fin r → ℕ) (hPer : ∀ j, IsPeriodic (period j) (A j))
    {p : ℕ} (hp : 0 < p) :
    let count := fun j => Nat.gcd (period j) p
    ∃ (innerDim : (j : Fin r) → Fin (count j) → ℕ)
      (C : (j : Fin r) → (a : Fin (count j)) → MPSTensor (blockPhysDim d p) (innerDim j a))
      (Y : Matrix (Fin (∑ j, dim j)) (Fin (∑ s, nestedBlockFlatDim count innerDim s)) ℂ),
      (∀ j a, innerDim j a ≠ 0) ∧
      (∀ j a, IsPeriodic (period j / count j) (C j a)) ∧
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      (∀ I, blockTensor (toTensorFromBlocks μ A) p I =
        Y * toTensorFromBlocks (fun s => μ (finSigmaFinEquiv.symm s).1 ^ p)
          (nestedBlockFlatTensor count innerDim C) I * Yᴴ) ∧
      ∀ c : (j : Fin r) → Fin (count j) → Circle,
        (∀ j a, c j a ^ (period j / count j) = 1) →
        (∀ j, ‖μ j‖ = 1) →
        ∃ A' : MPSTensor d (∑ j, dim j), IsLeftCanonical A' ∧
          ∀ I, blockTensor A' p I =
            Y * toTensorFromBlocks
              (fun s => μ (finSigmaFinEquiv.symm s).1 ^ p *
                (c (finSigmaFinEquiv.symm s).1 (finSigmaFinEquiv.symm s).2 : ℂ))
              (nestedBlockFlatTensor count innerDim C) I * Yᴴ := by
  classical
  dsimp only
  let count := fun j => Nat.gcd (period j) p
  have hEach (j : Fin r) := @IsPeriodic.exists_phaseTwisted_orbit_decomposition
    d (dim j) (period j) ⟨(hPer j).period_pos.ne'⟩ (A j) (hPer j) p hp
  choose innerDim C V hdim hPerC hV hVsum hletter hTwist using hEach
  obtain ⟨Y, hY, hY', hdiag⟩ :=
    exists_unitary_of_nested_isometric_block_decomposition count innerDim V hV hVsum
  refine ⟨innerDim, C, Y, hdim, hPerC, hY, hY', ?_, ?_⟩
  · intro I
    rw [blockTensor_toTensorFromBlocks_apply]
    have hblocks : ∀ j, ∑ a, V j a * (μ j ^ p • C j a I) * (V j a)ᴴ =
        μ j ^ p • blockTensor (A j) p I := by
      intro j
      rw [hletter j I]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
    have h := hdiag (fun j a => μ j ^ p • C j a I)
    rw [funext hblocks] at h
    exact h.symm
  · intro c hc hμ
    choose A' hTP hA' using fun j => hTwist j (c j) (hc j)
    refine ⟨toTensorFromBlocks μ A',
      leftCanonical_toTensorFromBlocks_of_weight_norm_one A' μ hTP hμ, ?_⟩
    intro I
    rw [blockTensor_toTensorFromBlocks_apply]
    have hblocks : ∀ j, ∑ a, V j a * ((μ j ^ p * (c j a : ℂ)) • C j a I) * (V j a)ᴴ =
        μ j ^ p • blockTensor (A' j) p I := by
      intro j
      rw [hA']
      simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_smul]
    have h := hdiag (fun j a => (μ j ^ p * (c j a : ℂ)) • C j a I)
    rw [funext hblocks] at h
    exact h.symm

end MPSTensor
