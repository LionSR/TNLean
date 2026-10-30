/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteQuasiLocalAction
import TNLean.QCA.IntervalTranslation

/-!
# Translation of actual finite MPU conjugations

Translating a consecutive interval leaves its periodic MPO matrix unchanged
in consecutive coordinates. The actual finite-chain conjugation therefore
translates by shifting the anchor, with no equality of translated matrix
types imposed as a premise.

Source: arXiv:1703.09188, Appendix translations and finite conjugation,
lines 2292--2306.

**Scope restriction (supplied standard form):** The completed forward
translation-covariance declarations use the supplied positive block and
its standard form. The finite conjugation identities require only actual
MPU unitarity. Bare-MPU and inverse assembly remain separate; see
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

namespace SpinChain

/-- Actual algebraic-local translation of finite MPU conjugation shifts
its interval anchor and transports the input by consecutive coordinates.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem algebraicLocalTranslation_finiteChainConjugation {d D : ℕ}
    {U : MPOTensor d D} (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (t b : ℤ)
    (A : LocalAlgebra d (finiteChainRegion b N)) :
    algebraicLocalTranslation d t (localObservable d (finiteChainRegion b N)
      (finiteChainConjugation hU hN b A)) =
      localObservable d (finiteChainRegion (b + t) N)
        (finiteChainConjugation hU hN (b + t)
          ((intervalCoordinates d (b + t) N).symm (intervalCoordinates d b N A))) := by
  rw [algebraicLocalTranslation_intervalCoordinates]
  congr 1
  apply EquivLike.injective (intervalCoordinates d (b + t) N)
  simp only [StarAlgEquiv.apply_symm_apply, intervalCoordinates_finiteChainConjugation]

/-- Actual quasi-local translation of finite MPU conjugation shifts its
interval anchor, with the same ordered periodic matrix in coordinates.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem quasiLocalTranslation_finiteChainConjugation {d D : ℕ} [NeZero d]
    {U : MPOTensor d D} (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (t b : ℤ)
    (A : LocalAlgebra d (finiteChainRegion b N)) :
    quasiLocalTranslation d t (quasiLocalObservable d (finiteChainRegion b N)
      (finiteChainConjugation hU hN b A)) =
      quasiLocalObservable d (finiteChainRegion (b + t) N)
        (finiteChainConjugation hU hN (b + t)
          ((intervalCoordinates d (b + t) N).symm (intervalCoordinates d b N A))) := by
  rw [quasiLocalTranslation_intervalCoordinates]
  congr 1
  apply EquivLike.injective (intervalCoordinates d (b + t) N)
  simp only [StarAlgEquiv.apply_symm_apply, intervalCoordinates_finiteChainConjugation]


variable {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
  (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
  {u : Matrix (Fin ℓ × Fin r)
    (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
  {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (Fin r × Fin ℓ) ℂ}
  (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)

/-- The actual completed forward MPU action commutes with lattice
translation on every finite observable. Both finite-chain expressions
are derived using actual sufficiently buffered intervals.
Source: arXiv:1703.09188, Appendix translation requirement, line 2306.
-/
theorem bufferedMPUQuasiLocalAction_translation_quasiLocalObservable
    (t : ℤ) (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    bufferedMPUQuasiLocalAction hU k hk S
      (quasiLocalTranslation d t (quasiLocalObservable d Λ A)) =
      quasiLocalTranslation d t
        (bufferedMPUQuasiLocalAction hU k hk S (quasiLocalObservable d Λ A)) := by
  classical
  obtain ⟨b, N, hN, hΛ, hb, _⟩ :=
    exists_finiteChainLocalObservable_bufferedMPULocalAction hU k Λ
  let hΛt := (translateRegion_mono t hΛ).trans (translateRegion_finiteChainRegion b t N).le
  have hbt : ∀ x ∈ translateRegion t Λ,
      b + t ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b + t + N := by
    intro x hx
    have h := hb (x - t) ((mem_translateRegion t Λ x).mp hx)
    omega
  rw [quasiLocalTranslation_quasiLocalObservable,
    bufferedMPUQuasiLocalAction_finiteChainConjugation hU k hk S
      (translateRegion t Λ) (b + t) N hN hΛt hbt,
    bufferedMPUQuasiLocalAction_finiteChainConjugation hU k hk S Λ b N hN hΛ hb,
    quasiLocalTranslation_finiteChainConjugation,
    intervalCoordinates_localInclusion_localTranslation]

/-- The actual completed forward MPU endomorphism commutes with every
integer lattice translation. No covariance premise or inverse is used.
Source: arXiv:1703.09188, Appendix, line 2306. -/
theorem bufferedMPUQuasiLocalAction_translation (t : ℤ) (X : QuasiLocalAlgebra d) :
    bufferedMPUQuasiLocalAction hU k hk S (quasiLocalTranslation d t X) =
      quasiLocalTranslation d t (bufferedMPUQuasiLocalAction hU k hk S X) := by
  induction X using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (bufferedMPUQuasiLocalAction_isometry hU k hk S).continuous.comp
          (quasiLocalTranslation_isometry d t).continuous
      · exact (quasiLocalTranslation_isometry d t).continuous.comp
          (bufferedMPUQuasiLocalAction_isometry hU k hk S).continuous
  | ih A =>
      induction A using DirectLimit.induction with
      | _ Λ A => exact bufferedMPUQuasiLocalAction_translation_quasiLocalObservable hU k hk S t Λ A

end SpinChain
