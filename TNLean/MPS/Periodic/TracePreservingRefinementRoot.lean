/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.CanonicalRefinementWitness
import TNLean.MPS.Periodic.RefinementRootWeightNorm
import TNLean.MPS.Periodic.RepeatedFamilyUnitaryMatching

/-!
# Trace-preserving refinement of a literal periodic block family

A periodic block root whose blocked vectors agree with a unit-weight periodic
family can be modified to agree with that family letter by letter. The
modification uses finite-order orbit phases and a unitary change of bond
coordinates, and preserves the original one-site physical dimension.

Source: arXiv:1708.00029, Theorem 4.1, lines 752--810.

**Scope restriction (literal normalized target):** The target is an actual
weighted direct sum of periodic blocks with unit-modulus weights. This
restriction corrects the missing trace-preservation hypothesis and excludes
arbitrary non-unitary bond gauges; see
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- A normalized literal periodic target admits a trace-preserving root with
exact blocked letters whenever it has the blocked vectors of a weighted
periodic family. Source: arXiv:1708.00029, Theorem 4.1, lines 752--810.
The literal block hypotheses are essential; equality of vector families alone
does not make an arbitrary bond gauge trace preserving. -/
theorem exists_leftCanonical_root_of_blocked_periodic_sameMPV₂Pos
    {d r s : ℕ} {dim : Fin r → ℕ} {dim' : Fin s → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (periodA : Fin r → ℕ) (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    {p : ℕ} (hp : 0 < p)
    (B : (k : Fin s) → MPSTensor (blockPhysDim d p) (dim' k))
    (ν : Fin s → ℂ) (hν : ∀ k, ‖ν k‖ = 1)
    (periodB : Fin s → ℕ) (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hSame : SameMPV₂Pos (blockTensor (toTensorFromBlocks μ A) p)
      (toTensorFromBlocks ν B)) :
    ∃ R : MPSTensor d (∑ k, dim' k),
      IsLeftCanonical R ∧ blockTensor R p = toTensorFromBlocks ν B := by
  classical
  have hnorm := (weight_norm_eq_one_of_blocked_periodic_sameMPV₂Pos
    A μ hμ periodA hPerA hp B ν hν periodB hPerB hSame).1
  let count := fun j => Nat.gcd (periodA j) p
  obtain ⟨innerDim, C, Y, _, hPerC, hYY, hY, hbase, hTwist⟩ :=
    exists_unitary_phaseTwisted_block_family A μ periodA hPerA hp
  let F := nestedBlockFlatTensor count innerDim C
  let weight : Fin (∑ j, count j) → ℂ := fun x => μ (finSigmaFinEquiv.symm x).1 ^ p
  let per : Fin (∑ j, count j) → ℕ := fun x =>
    periodA (finSigmaFinEquiv.symm x).1 / count (finSigmaFinEquiv.symm x).1
  have hBaseSame : SameMPV₂Pos (blockTensor (toTensorFromBlocks μ A) p)
      (toTensorFromBlocks weight F) := by
    apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Yᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hY)
    intro I
    simpa only [Matrix.conjTranspose_conjTranspose] using hbase I
  obtain ⟨c, W, hc, hWW, hW, hMatch⟩ :=
    exists_unitary_matching_of_periodic_block_families_sameMPV₂Pos
      F weight (fun _ => pow_ne_zero p (hμ _)) B ν
      (fun k => Complex.ne_zero_of_norm_eq_one (hν k)) per periodB
      (fun x => hPerC (finSigmaFinEquiv.symm x).1 (finSigmaFinEquiv.symm x).2)
      hPerB (hBaseSame.symm.trans hSame)
  have hcnorm (x) : ‖c x‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (hc x)
      (hPerC (finSigmaFinEquiv.symm x).1 (finSigmaFinEquiv.symm x).2).period_pos.ne'
  let phase : (j : Fin r) → Fin (count j) → Circle :=
    fun j a => ⟨c (finSigmaFinEquiv ⟨j, a⟩),
      mem_sphere_zero_iff_norm.2 (hcnorm (finSigmaFinEquiv ⟨j, a⟩))⟩
  have hphase : ∀ j a, phase j a ^ (periodA j / count j) = 1 := by
    intro j a
    apply Subtype.ext
    change c (finSigmaFinEquiv ⟨j, a⟩) ^ (periodA j / count j) = 1
    simpa only [per, Equiv.symm_apply_apply] using hc (finSigmaFinEquiv ⟨j, a⟩)
  obtain ⟨A', hA', hblock⟩ := hTwist phase hphase hnorm
  let T := Y * W
  have hT : Matrix.IsUnitaryBetween T :=
    Matrix.IsUnitaryBetween.mul Y W ⟨hY, hYY⟩ ⟨hW, hWW⟩
  have hTT : T * Tᴴ = 1 := hT.2
  have hT'T : Tᴴ * T = 1 := hT.1
  have hblock' (I) : blockTensor A' p I =
      T * toTensorFromBlocks ν B I * Tᴴ := by
    rw [hblock I]
    have hweights : (fun x => μ (finSigmaFinEquiv.symm x).1 ^ p *
        (phase (finSigmaFinEquiv.symm x).1 (finSigmaFinEquiv.symm x).2 : ℂ)) =
        (fun x => c x * weight x) := by
      funext x
      simp only [phase, Sigma.eta, Equiv.apply_symm_apply, weight, mul_comm]
    rw [hweights, hMatch I]
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  let R : MPSTensor d (∑ k, dim' k) := fun i => Tᴴ * A' i * T
  refine ⟨R, ?_, ?_⟩
  · change ∑ i, (Tᴴ * A' i * T)ᴴ * (Tᴴ * A' i * T) = 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc T Tᴴ, hTT, Matrix.one_mul]
    simp only [← Matrix.mul_assoc (A' _)ᴴ (A' _), ← Matrix.mul_sum,
      ← Matrix.sum_mul]
    rw [hA', Matrix.one_mul]
    exact hT'T
  · funext I
    have hw : wordOfBlock d p I ≠ [] := by
      intro h
      have := congrArg List.length h
      exact hp.ne' (by simpa only [Kraus.length_wordOfBlock, List.length_nil] using this)
    have h := evalWord_eq_coisometry_reconstruction_of_ne_nil T hTT
      (A := R) (B := A') (fun _ => rfl) (wordOfBlock d p I) hw
    change blockTensor R p I = Tᴴ * blockTensor A' p I * T at h
    rw [h, hblock']
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, hT'T,
      Matrix.one_mul, Matrix.mul_one]

/-- An arbitrary refinement root can first be replaced by its active periodic
blocks. Thus the exact trace-preserving root construction requires no canonical
hypothesis on the original root. Source: arXiv:1708.00029, Theorem 4.1,
lines 752--810, using the irreducible reduction at lines 238--275. -/
theorem exists_leftCanonical_root_of_sameMPV₂Pos_blockTensor
    {d D s p : ℕ} {dim : Fin s → ℕ}
    (A : MPSTensor d D) (hp : 0 < p)
    (B : (k : Fin s) → MPSTensor (blockPhysDim d p) (dim k))
    (ν : Fin s → ℂ) (hν : ∀ k, ‖ν k‖ = 1)
    (period : Fin s → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hSame : SameMPV₂Pos (blockTensor A p) (toTensorFromBlocks ν B)) :
    ∃ R : MPSTensor d (∑ k, dim k),
      IsLeftCanonical R ∧ blockTensor R p = toTensorFromBlocks ν B := by
  obtain ⟨P, _, _, ⟨perP, hPerP⟩, _, hAP⟩ :=
    exists_active_irreducible_sectorDecomposition A
  exact exists_leftCanonical_root_of_blocked_periodic_sameMPV₂Pos
    P.flatBasis P.flatWeight (fun x => P.weight_ne_zero _ _)
    (fun x => perP (P.flatIndexEquiv.symm x).1)
    (fun x => hPerP (P.flatIndexEquiv.symm x).1) hp B ν hν period hPer
    ((sameMPV₂Pos_blockTensor A P.toTensor hAP p hp).symm.trans hSame)

end MPSTensor
