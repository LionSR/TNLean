/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardFormSymmetryCriteria
import TNLean.MPS.MPU.TimeReversalSign

/-!
# The time-reversal sign of a standard form

For a time-reversal-invariant MPU in standard form, Proposition `PropChiral`
provides a unitary `x` and a sign `σ = ±1` with
`v₂₃ (u₁₂ ⊗ u₃₄) = σ (x₁₂ ⊗ x₃₄†) v₂₃†`. The normalized four-spin trace
`d⁻² tr[𝕊₁₂,₃₄ v₂₃ u₁₂ u₃₄ v₂₃]` recovers that sign. Here the local relation
is a consequence of the global symmetry, not a hypothesis.

## Main results

* `MPOTensor.IsMPUCanonicalFormII.standardForm_timeReversalSign`: the lemma
  containing `eq:sigma-from-trace`.

## References

* arXiv:1703.09188, `UUdaggertrick-2` and the lemma containing
  `eq:sigma-from-trace`, lines 1585--1611.
-/

open scoped Matrix Kronecker

namespace MPOTensor

namespace IsMPUCanonicalFormII

variable {d D : ℕ} {V : MPOTensor d D}

/-- **Trace formula for the time-reversal sign.** Let `u, v` be the gates of a
standard form of the two-site block of a tensor in canonical form II, and
suppose the generated MPU satisfies `U⁽ᴺ⁾ = U⁽ᴺ⁾†` for every even `N`. Then the
intermediate dimensions equal the physical dimension and, in these
coordinates, the normalized trace `σ = d⁻² tr[𝕊₁₂,₃₄ v₂₃ u₁₂ u₃₄ v₂₃]` is a
sign, with a unitary `x` satisfying `v₂₃ (u₁₂ ⊗ u₃₄) = σ (x₁₂ ⊗ x₃₄†) v₂₃†`.
Any sign in such a relation equals this trace, by
`MPOTensor.TwoSiteStandardFormData.timeReversalSign_eq_of_local_relation`.

Source: arXiv:1703.09188, lemma containing `eq:sigma-from-trace`, lines
1595--1603, with proof at lines 1605--1611. -/
theorem standardForm_timeReversalSign
    {ℓ r : ℕ} (hV : IsMPUCanonicalFormII V)
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (MPOTensor.blockTwo V) u v)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᴴ) :
    ∃ (hr : r = d) (hl : ℓ = d) (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ),
      let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
        (Equiv.refl _) u
      let v₀ := Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hr) (finCongr hl)) v
      (timeReversalSign u₀ v₀ = 1 ∨ timeReversalSign u₀ v₀ = -1) ∧
      staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
        timeReversalSign u₀ v₀ •
          ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
          (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᴴ := by
  obtain ⟨hr, hl, σ, x, hσ, hlocal⟩ := (hV.standardForm_even_timeReversal_iff S).mp hTR
  have hsign := (S.reindexRanks (finCongr hl) (finCongr hr)).timeReversalSign_eq_of_local_relation
    x hlocal
  refine ⟨hr, hl, x, ?_, ?_⟩
  · rw [hsign]
    exact hσ
  · rw [hsign]
    exact hlocal

end IsMPUCanonicalFormII

end MPOTensor
