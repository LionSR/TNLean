/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleCanonicalRepresentative
import TNLean.MPS.MPU.StandardFormTimeReversalSign
import TNLean.MPS.MPU.TimeReversalSignIntrinsic

/-!
# Well-definedness of the time-reversal sign

The sign `σ` of Proposition `PropChiral` is read from the normalized trace of
the length-two periodic operator of the standard-form tensor. That operator is
determined by the MPU, so the sign does not depend on the gauge or on the
standard-form representative. For every simple MPU whose standard form is
time-reversal invariant, the sign is `±1`: the local relation, and hence the
sign, comes from Proposition `PropChiral` applied to the simple canonical
representative. The trace depends continuously on the tensor, so along any
continuous path of simple MPUs that stay time-reversal invariant the sign is
constant. No standard forms, gates or local relations are required along the
path; they are constructed at each point. Time-reversal invariance is required
at even lengths of the two-spin standard-form chain, that is, at original
lengths divisible by four; see `docs/paper-gaps/mpu_standard_form_parity_gap.tex`.

## Main results

* `MPOTensor.IsMPUSimple.intrinsicTimeReversalSign_blockTwo_eq_standardForm_sign`:
  every standard form of the canonical representative has the same sign.
* `MPOTensor.IsMPUSimple.intrinsicTimeReversalSign_blockTwo_eq_one_or_neg_one`:
  the sign is `±1`.
* `MPOTensor.intrinsicTimeReversalSign_blockTwo_eq_on_path`: constancy under
  continuous deformations preserving time-reversal symmetry.

## References

* arXiv:1703.09188, Proposition `prop:sigma-well-defined`, lines 1616--1622,
  with proof at lines 1624--1631.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- Two-site blocking is continuous in the tensor. Source: arXiv:1703.09188,
definition `blocking`, lines 297--305. -/
theorem continuous_blockTwo : Continuous (blockTwo : MPOTensor d D → MPOTensor (d * d) D) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  exact ((continuous_apply _).comp (continuous_apply _)).matrix_mul
    ((continuous_apply _).comp (continuous_apply _))

/-- Equal periodic operators at every positive length give equal periodic
operators of the two-site blocks. Source: arXiv:1703.09188, definition
`blocking`, lines 297--305. -/
theorem mpo_blockTwo_eq_of_mpo_eq {D' : ℕ} {U : MPOTensor d D} {V : MPOTensor d D'}
    (hsame : ∀ N : ℕ, 0 < N → mpo V N = mpo U N) (N : ℕ) (hN : 0 < N) :
    mpo (blockTwo V) N = mpo (blockTwo U) N := by
  rw [mpo_blockTwo_eq_reindex_blockTensor, mpo_blockTwo_eq_reindex_blockTensor,
    mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex, hsame (N * 2) (by omega)]

namespace IsMPUSimple

variable [NeZero d] [NeZero D] {U : MPOTensor d D}

/-- For a simple MPU whose standard form is time-reversal invariant at every
even length, the intrinsic sign of its two-site block is the sign `σ` of
Proposition `PropChiral` for the canonical representative, with any choice of
standard-form gates of that representative.

Source: arXiv:1703.09188, Proposition `prop:sigma-well-defined`, lines
1616--1622, gauge independence, proof at lines 1624--1627. -/
theorem intrinsicTimeReversalSign_blockTwo_eq_standardForm_sign
    (hU : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (blockTwo U) N = (mpo (blockTwo U) N)ᴴ) :
    ∃ (E : ℕ) (V : MPOTensor d E) (hV : IsMPUCanonicalFormII V),
      IsMPUSimple V ∧ (∀ N : ℕ, 0 < N → mpo V N = mpo U N) ∧
      ∃ (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
        (hr : r[V] = d) (hl : ℓ[V] = d),
        let u₀ := Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
          (Equiv.refl _) (sourceU V hV.ρ hV.ρ_posDef)
        let v₀ := Matrix.reindex (Equiv.refl _)
          (Equiv.prodCongr (finCongr hr) (finCongr hl)) (sourceV V hV.ρ hV.ρ_posDef)
        timeReversalSign u₀ v₀ = intrinsicTimeReversalSign (blockTwo U) ∧
        staircaseMiddle (A := Fin d) (E := Fin d) v₀ * (u₀ ⊗ₖ u₀) =
          intrinsicTimeReversalSign (blockTwo U) •
            ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
              (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ) *
            (staircaseMiddle (A := Fin d) (E := Fin d) v₀)ᴴ := by
  obtain ⟨E, _hE, V, hV, hsV, _hdim, hsame, ⟨S⟩⟩ := hU.exists_reduced_twoSiteStandardFormData
  have hblock := mpo_blockTwo_eq_of_mpo_eq hsame
  have hTRV : ∀ N : ℕ, 1 < N → Even N →
      mpo (blockTwo V) N = (mpo (blockTwo V) N)ᴴ := by
    intro N hN heven
    rw [hblock N (by omega)]
    exact hTR N hN heven
  obtain ⟨hr, hl, x, -, hlocal⟩ := hV.standardForm_timeReversalSign S hTRV
  have hint : timeReversalSign
      (Matrix.reindex (Equiv.prodCongr (finCongr hl) (finCongr hr))
        (Equiv.refl _) (sourceU V hV.ρ hV.ρ_posDef))
      (Matrix.reindex (Equiv.refl _)
        (Equiv.prodCongr (finCongr hr) (finCongr hl)) (sourceV V hV.ρ hV.ρ_posDef)) =
      intrinsicTimeReversalSign (blockTwo U) :=
    (S.reindexRanks (finCongr hl) (finCongr hr)).timeReversalSign_eq_intrinsic.trans
      (intrinsicTimeReversalSign_eq_of_mpo_two_eq (hblock 2 (by norm_num)))
  refine ⟨E, V, hV, hsV, hsame, x, hr, hl, hint, ?_⟩
  rw [← hint]
  exact hlocal

/-- The time-reversal sign of a simple MPU whose standard form is
time-reversal invariant at every even length is `±1`.

Source: arXiv:1703.09188, Proposition `prop:sigma-well-defined`, lines
1616--1622, and `UUdaggertrick-2`, lines 1585--1593. -/
theorem intrinsicTimeReversalSign_blockTwo_eq_one_or_neg_one
    (hU : IsMPUSimple U)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (blockTwo U) N = (mpo (blockTwo U) N)ᴴ) :
    intrinsicTimeReversalSign (blockTwo U) = 1 ∨
      intrinsicTimeReversalSign (blockTwo U) = -1 := by
  obtain ⟨E, _hE, V, hV, _hsV, _hdim, hsame, ⟨S⟩⟩ := hU.exists_reduced_twoSiteStandardFormData
  have hblock := mpo_blockTwo_eq_of_mpo_eq hsame
  have hTRV : ∀ N : ℕ, 1 < N → Even N →
      mpo (blockTwo V) N = (mpo (blockTwo V) N)ᴴ := by
    intro N hN heven
    rw [hblock N (by omega)]
    exact hTR N hN heven
  obtain ⟨hr, hl, -, hsign, -⟩ := hV.standardForm_timeReversalSign S hTRV
  rw [← intrinsicTimeReversalSign_eq_of_mpo_two_eq (hblock 2 (by norm_num)),
    ← (S.reindexRanks (finCongr hl) (finCongr hr)).timeReversalSign_eq_intrinsic]
  exact hsign

end IsMPUSimple

/-- **Constancy of the time-reversal sign.** Along a continuous path of simple
MPU tensors whose standard forms stay time-reversal invariant at every even
length, the time-reversal sign is constant. Standard forms and local relations
are constructed at each point; none is assumed to vary continuously.

Source: arXiv:1703.09188, Proposition `prop:sigma-well-defined`, lines
1616--1622, with proof at lines 1624--1631. -/
theorem intrinsicTimeReversalSign_blockTwo_eq_on_path [NeZero d] [NeZero D]
    (U : ℝ → MPOTensor d D) (hU : ContinuousOn U (Set.Icc (0 : ℝ) 1))
    (hsimple : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsMPUSimple (U t))
    (hTR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ N : ℕ, 1 < N → Even N →
      mpo (blockTwo (U t)) N = (mpo (blockTwo (U t)) N)ᴴ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      intrinsicTimeReversalSign (blockTwo (U t)) =
        intrinsicTimeReversalSign (blockTwo (U 0)) := by
  have hcont : ContinuousOn (fun t ↦ intrinsicTimeReversalSign (blockTwo (U t)))
      (Set.Icc (0 : ℝ) 1) :=
    (continuous_intrinsicTimeReversalSign.comp continuous_blockTwo).comp_continuousOn hU
  have hsq : Set.EqOn ((fun t ↦ intrinsicTimeReversalSign (blockTwo (U t))) ^ 2) 1
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    simpa only [Pi.pow_apply, Pi.one_apply] using sq_eq_one_iff.mpr
      ((hsimple t ht).intrinsicTimeReversalSign_blockTwo_eq_one_or_neg_one (hTR t ht))
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  rcases isPreconnected_Icc.eq_one_or_eq_neg_one_of_sq_eq hcont hsq with h | h
  · exact fun t ht ↦ (h ht).trans (h h0).symm
  · exact fun t ht ↦ (h ht).trans (h h0).symm

end MPOTensor
