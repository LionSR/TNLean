/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FiniteWindowSupport

/-!
# The actual middle four-half-block output window

The fixed six-half-block output of the supplied standard-form action is
exactly the existing placement of its four-half-block two-link observable
at offset one half block. Both exterior half blocks carry identities.
This is a coordinate contraction of the actual output, with no support
or factor-presentation premise.

Source: arXiv:1703.09188, StandardForm and eq:appendix-1,
lines 603–622 and 2292–2306; the four-site output in the Appendix index
comparison, lines 2313–2334.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- The actual six-half-block output is the existing inclusion of its
four consecutive middle half blocks, with identity exterior half blocks.
Source: CPSV17, StandardForm and Appendix, lines 603–622 and 2300–2334. -/
theorem originalSiteHeisenbergOutputWindow_eq_chainWindowOperator
    {d ℓ r : ℕ} (k : ℕ) (hk : 0 < k)
    (u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ)
    (v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    originalSiteHeisenbergOutputWindow k u v A =
      MPSTensor.chainWindowOperator (3 * (2 * k)) k
        (Matrix.reindex (originalSiteHeisenbergOutputCentreEquiv d k)
          (originalSiteHeisenbergOutputCentreEquiv d k) (twoLinkOutputObservable u v A)) := by
  classical
  ext row col
  obtain ⟨⟨e, c⟩, rfl⟩ := (originalSiteHeisenbergOutputWindowEquiv d k).surjective row
  obtain ⟨⟨e', c'⟩, rfl⟩ := (originalSiteHeisenbergOutputWindowEquiv d k).surjective col
  rw [MPSTensor.chainWindowOperator_apply (by omega) (by omega)]
  simp only [originalSiteHeisenbergOutputWindow, Matrix.reindex_apply,
    Equiv.symm_apply_apply, Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, originalSiteHeisenbergOutputWindowEquiv_middle,
    originalSiteHeisenbergOutputWindowEquiv_outside_eq_iff]
  by_cases he : e = e' <;> simp [he]

/-- The actual fixed output acts only on the four middle half blocks,
namely the original-site interval from k through 5k−1. No support conclusion
is supplied as a hypothesis. Source: CPSV17, Appendix, lines 2300–2334. -/
theorem originalSiteHeisenbergOutputWindow_mem_supportedOperators
    {d ℓ r : ℕ} (k : ℕ) (hk : 0 < k)
    (u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ)
    (v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    originalSiteHeisenbergOutputWindow k u v A ∈ QuantumCircuit.supportedOperators d
      {i : Fin (3 * (2 * k)) | k ≤ i.val ∧ i.val < k + 4 * k} := by
  rw [originalSiteHeisenbergOutputWindow_eq_chainWindowOperator k hk u v A]
  exact MPSTensor.chainWindowOperator_mem_supportedOperators (by omega) (by omega) _

end MPOTensor
