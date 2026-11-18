/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardFormCanonicalRepresentative
import TNLean.MPS.MPU.ConjugationDeterminantInvariant
import TNLean.MPS.MPU.Examples.ConjugationPhaseRepresentatives

/-!
# The two phases under conjugation when one rank is odd

Example `ex:all-phases-under-conjugation` of arXiv:1703.09188 (lines 1845--1876) states that, when
one of the ranks `ℓ, r` is odd, the gates `(u₊, v₊)` and `(u₊, v₋)`, with `u₊ = v₊ = 1` and
`v₋ = diag(-1, 1, …, 1)` read through an identification `ℂ^ℓ ⊗ ℂ^r ≅ ℂ^d ⊗ ℂ^d`, realize the two
classes of Theorem `conjphs`.

Tensors in canonical form carrying these gates come from
`exists_isMPUCanonicalForm_twoSiteStandardFormData`. Their MPUs are invariant under conjugation
(`conjugation_caseI_gates`), and `det(u₊ v_±) = ±1`. By Theorem `conjphs`
(`strictlyEquivalentUnderSymmetry_conjugation_iff_det_mul_eq`) the two tensors are not strictly
equivalent under conjugation. Every other tensor on pairs in canonical form, with a standard form of
the same ranks and an MPU invariant under conjugation, has `det(u v) = ±1`, read off the MPU on one
standard-form site (`TwoSiteStandardFormData.det_mpo_one_eq`), so it is strictly equivalent to one
of the two.

## Main results

* `MPOTensor.ConjugationExamples.exists_isMPUCanonicalForm_signGates`: a tensor in canonical form
  with the example gates, invariant under conjugation.
* `MPOTensor.ConjugationExamples.conjugation_oddRank_two_phases`: the odd-rank half of the example.
-/

open scoped Matrix
open Matrix

namespace MPOTensor

namespace ConjugationExamples

variable {d ℓ r : ℕ}

/-- **A tensor in canonical form with the example gates.** For every pair of signs, there is a
tensor on pairs in canonical form with standard-form gates `u_{s₁}, v_{s₂}` read through `e`, whose
MPU is invariant under conjugation at every positive length.

Source: arXiv:1703.09188, Example `ex:all-phases-under-conjugation`, lines 1845--1876. -/
theorem exists_isMPUCanonicalForm_signGates [NeZero d] [NeZero ℓ] [NeZero r]
    (e : Fin ℓ × Fin r ≃ Fin d × Fin d) (s₁ s₂ : Bool) :
    ∃ (K : ℕ) (W : MPOTensor (d * d) K),
      MPSTensor.IsMPUCanonicalForm W.toMPSTensor ∧
        Nonempty (TwoSiteStandardFormData W (gateU e (signGate s₁)) (gateV e (signGate s₂))) ∧
          ∀ N : ℕ, 0 < N → mpo W N = (mpo W N).map (starRingEnd ℂ) := by
  obtain ⟨K, W, hcf, hS, hmpo⟩ := exists_isMPUCanonicalForm_twoSiteStandardFormData
    (gateU e (signGate s₁)) (gateV e (signGate s₂))
    (gateU_isUnitaryBetween e (signGate_mem_unitaryGroup s₁))
    (gateV_isUnitaryBetween e (signGate_mem_unitaryGroup s₂))
  have hinv := (conjugation_caseI_gates (e := e) s₁ s₂).1
  refine ⟨K, W, hcf, hS, fun N hN ↦ ?_⟩
  have h := hinv (N := N) hN
  change (mpo (reindexPhysical (Equiv.refl _) _) N).map (starRingEnd ℂ) =
    mpo (reindexPhysical (Equiv.refl _) _) N at h
  rw [mpo_reindexPhysical] at h
  simp only [Matrix.reindex_apply, Equiv.symm_symm] at h
  rw [hmpo N hN]
  convert h.symm using 2 <;> ext <;> rfl

/-- The determinant `det(u v)` of a standard form of a tensor whose MPU on one standard-form site
is fixed by complex conjugation is `1` or `-1`. -/
private theorem det_mul_eq_one_or_neg_one {D : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (hc : mpo W 1 = (mpo W 1).map (starRingEnd ℂ)) :
    ((u * v).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det = 1 ∨
      ((u * v).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det = -1 := by
  have hW : IsMPU W := TwoSiteStandardFormData.isMPU W u v S
  have hdet := S.det_mpo_one_eq
  set ε : ℂ := (Equiv.Perm.sign (Equiv.prodComm (Fin d) (Fin d)) : ℂ)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.prodComm (Fin d) (Fin d))) with h | h <;>
      simp [ε, h]
  rcases hW.det_mpo_one_eq_one_or_neg_one_of_map_star_eq hc.symm with h | h <;>
    rcases hε with hε | hε <;> rw [hdet, hε] at h
  · left; simpa using h
  · right; linear_combination -h
  · right; simpa using h
  · left; linear_combination -h

/-- **Example `ex:all-phases-under-conjugation`, one rank odd.** Suppose one of `ℓ, r` is odd, and
fix an identification `e : ℂ^ℓ ⊗ ℂ^r ≅ ℂ^d ⊗ ℂ^d`. There are tensors `W₊, W₋` on pairs in canonical
form, invariant under conjugation, with standard-form gates `(u₊, v₊)` and `(u₊, v₋)`, which are
not strictly equivalent under conjugation. Every tensor on pairs in canonical form, invariant under
conjugation, with a standard form of the same ranks, is strictly equivalent under conjugation to
`Wp` or to `Wm`. So the two gate pairs realize the two classes of Theorem `conjphs`.

Source: arXiv:1703.09188, Example `ex:all-phases-under-conjugation`, lines 1845--1876, with
Theorem `conjphs`, lines 1406--1446. -/
theorem conjugation_oddRank_two_phases [NeZero d] [NeZero ℓ] [NeZero r]
    (e : Fin ℓ × Fin r ≃ Fin d × Fin d) (hodd : Odd ℓ ∨ Odd r) :
    ∃ (Kp Km : ℕ) (Wp : MPOTensor (d * d) Kp) (Wm : MPOTensor (d * d) Km),
      MPSTensor.IsMPUCanonicalForm Wp.toMPSTensor ∧ MPSTensor.IsMPUCanonicalForm Wm.toMPSTensor ∧
      Nonempty (TwoSiteStandardFormData Wp (gateU e (signGate true))
        (gateV e (signGate true))) ∧
      Nonempty (TwoSiteStandardFormData Wm (gateU e (signGate true))
        (gateV e (signGate false))) ∧
      (∀ N : ℕ, 0 < N → mpo Wp N = (mpo Wp N).map (starRingEnd ℂ)) ∧
      (∀ N : ℕ, 0 < N → mpo Wm N = (mpo Wm N).map (starRingEnd ℂ)) ∧
      ¬ StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d)) Wp Wm rfl ∧
      ∀ {D : ℕ} (W : MPOTensor (d * d) D) {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
        {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}, TwoSiteStandardFormData W u v →
        MPSTensor.IsMPUCanonicalForm W.toMPSTensor →
        (∀ N : ℕ, 0 < N → mpo W N = (mpo W N).map (starRingEnd ℂ)) →
        StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d)) Wp W rfl ∨
          StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d)) Wm W rfl := by
  obtain ⟨Kp, Wp, hcfp, ⟨Sp⟩, hcp⟩ := exists_isMPUCanonicalForm_signGates e true true
  obtain ⟨Km, Wm, hcfm, ⟨Sm⟩, hcm⟩ := exists_isMPUCanonicalForm_signGates e true false
  have hdetp := (conjugation_caseI_gates (e := e) true true).2.2.2.2
  have hdetm := (conjugation_caseI_gates (e := e) true false).2.2.2.2
  simp only [boolSign, ite_true, Bool.false_eq_true, ite_false, mul_one, one_mul] at hdetp hdetm
  refine ⟨Kp, Km, Wp, Wm, hcfp, hcfm, ⟨Sp⟩, ⟨Sm⟩, hcp, hcm, ?_, ?_⟩
  · rw [strictlyEquivalentUnderSymmetry_conjugation_iff_det_mul_eq hcfp hcfm hcp hcm Sp Sm hodd,
      hdetp, hdetm]
    norm_num
  · intro D W u v S hcf hc
    rw [strictlyEquivalentUnderSymmetry_conjugation_iff_det_mul_eq hcfp hcf hcp hc Sp S hodd,
      strictlyEquivalentUnderSymmetry_conjugation_iff_det_mul_eq hcfm hcf hcm hc Sm S hodd,
      hdetp, hdetm]
    rcases det_mul_eq_one_or_neg_one S (hc 1 Nat.one_pos) with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

end ConjugationExamples

end MPOTensor
