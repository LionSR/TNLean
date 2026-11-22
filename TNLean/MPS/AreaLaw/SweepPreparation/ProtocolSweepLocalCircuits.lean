/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepPath
import TNLean.MPS.AreaLaw.SweepPreparation.ChainStageIncidence
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepFrames
import TNLean.MPS.AreaLaw.SweepPreparation.BandInformation
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Conditional circuits on the actual eighteen-operation stage path

The construction combines the two initial births, the actual eight-operation
bands, and the exceptional first
left death with seven identity circuits. The source and target are the existing
nineteen stage boundaries. Private entrance and exit permutations are composed
inside the adjacent primitive operations and occupy no additional slot.

All information hypotheses concern the original vector and the actual primitive
sheets. They are explicit intermediate assumptions, not a replacement for the
physical information estimates. No circuit, trajectory, endpoint identity,
owner relation, aggregate information certificate or lifetime bound is supplied.
The existing chronological composition and error/count theorems are not repeated.

The stage-sheet geometry and the eight-operation band construction are those
of the existing modules; their hypotheses and retained auxiliary labels are unchanged.

Source: the one-dimensional note, Part II, `con:sweep`, lines 330–343,
`con:band`, lines 260–276, and `prop:sweep`, proof, lines 365–378.

**Local fix (half-open lattice bands):** The operations and their retained
auxiliaries are those of the corrected band construction. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

## Physical local circuits for the chain sweep

A uniform logarithmic width supplies every primitive information estimate
needed by the existing eighteen-operation stage construction. The two
information constants and length cutoffs are enlarged before the chain,
Hamiltonian, ground state, width and stage are introduced.
All estimates concern the same original ground-state vector.

It constructs circuits only for one actual stage. Chronological composition,
total participation, total error and the final approximation are separate.

**Scope restriction (contiguous chains):** The sites are `Fin L`. See
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (half-open lattice bands):** The actual corrected bands and
retained auxiliary owners are used. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Sources: the one-dimensional note, Part II, `lem:logsep`, lines 472–488;
Part II, `con:sweep`, lines 330–343, and `prop:sweep`, lines 365–378.
The selected constant gives information at exponent 24 and local circuit
error at exponent 12.
-/

section

open ManyBody (interval mem_interval)

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice TNLean.Lattice.PartyCircuit TNLean.Lattice.Sheet

variable {L w q : ℕ}

/-- The actual local boundary may select or restore the labelled left copy.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
private theorem left_boundary_perm (k : Fin (stageCount L w)) (hk : 0 < k.val)
    (j : Fin 9) :
    (stageBoundaryFrames L w k (j.val + 2)).Perm
      (leftBandFrames L w k hk j.val) := by
  by_cases h0 : j.val = 0
  · simpa only [h0, zero_add] using stageBoundaryFrames_left_entrance_perm k hk
  · by_cases h8 : j.val = 8
    · simpa only [h8, Nat.reduceAdd, stageBoundaryFrames_ten] using
        (leftBandFrames_eight_perm k hk).symm
    · rw [stageBoundaryFrames_left k hk (by omega) (by have h := j.isLt; omega)]
      have he : j.val + 2 - 2 = j.val := by omega
      rw [he]

/-- The actual local boundary may select or restore the labelled right copy.
Source: Part II, `con:sweep`, move (4), lines 339–342. -/
private theorem right_boundary_perm (k : Fin (stageCount L w)) (j : Fin 9) :
    (stageBoundaryFrames L w k (j.val + 10)).Perm
      (rightBandFrames L w k j.val) := by
  by_cases h0 : j.val = 0
  · simpa only [h0, zero_add] using stageBoundaryFrames_right_entrance_perm k
  · by_cases h8 : j.val = 8
    · simpa only [h8, stageBoundaryFrames_last k (by decide : 18 ≤ 18)] using
        (rightBandFrames_eight_perm k).symm
    · rw [stageBoundaryFrames_right k (by omega) (by have h := j.isLt; omega)]
      have he : j.val + 10 - 10 = j.val := by omega
      rw [he]

/-- The existing eight-operation construction with a uniform error bound.
The eight hypotheses remain the actual primitive information inequalities.
Source: Part II, `con:band`, lines 260–276. -/
private theorem band_changes (own : Fin L → Party L w) (A B C : Party L w) (a : ℕ)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C)
    (hA : ∀ x ∈ interval L a (a + w), own x = A)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI0 : ManyBody.regionMutualInformation Ω (interval L (a - 6 * w) (a -
      w)) ((OneBand.aux₀ (Party := Party L w) C).birthEnv C) ≤ (L : ℝ) ^
      (-24 : ℤ))
    (hI1 : ManyBody.regionMutualInformation Ω (interval L (a - 5 * w) (a - 2
      * w)) ((OneBand.aux₁ (Party := Party L w) B C a w).birthEnv B) ≤ (L : ℝ)
      ^ (-24 : ℤ))
    (hI2 : ManyBody.regionMutualInformation Ω (interval L (a - 4 * w) (a - 3
      * w)) ((OneBand.aux₂ (Party := Party L w) A B C a w).birthEnv A) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI3 : ManyBody.regionMutualInformation Ω
      (OneBand.exchangeTSet own A B C a w) (OneBand.exchangeESet own A B C a w) ≤
        (L : ℝ) ^ (-24 : ℤ))
    (hI4 : ManyBody.regionMutualInformation Ω (interval L (a - 4 * w) a)
      ((OneBand.main₅ (Party := Party L w) own A B C a w).birthEnv A) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI5 : ManyBody.regionMutualInformation Ω (interval L (a - 5 * w) (a +
      w)) ((OneBand.main₆ (Party := Party L w) own A B C a w).birthEnv B) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI6 : ManyBody.regionMutualInformation Ω (interval L (a - 3 * w) a)
      ((OneBand.main₆ (Party := Party L w) own A B C a w).birthEnv B) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI7 : ManyBody.regionMutualInformation Ω (interval L (a - 6 * w) (a - 3
      * w)) ((OneBand.main₈ (Party := Party L w) own A B C a w).birthEnv C) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (post : List (Sheet (Fin L) (Party L w))) :
    ∀ j : Fin 8, Sheet.HasSourceBoundedChange (ℓ := []) Ω
      (OneBand.frames (Party := Party L w) own A B C a w j.val ++ post)
      (OneBand.frames (Party := Party L w) own A B C a w (j.val + 1) ++ post)
        (1 : ℂ)
      (OneBand.participants A B C j) 1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
  obtain ⟨c, hc⟩ := OneBand.circuits_of_primitive_information (ℓ := []) own A
    B C a w
    hw hleft hC hA hΩ
    hI0 hI1 hI2 hI3 hI4 hI5 hI6 hI7 [] post (1 : ℂ) (by simp)
  intro j
  have he : (if j.val = 3 then 4 * (L : ℝ) ^ (-12 : ℤ)
      else (L : ℝ) ^ (-12 : ℤ)) ≤ 4 * (L : ℝ) ^ (-12 : ℤ) := by
    have hε : 0 ≤ (L : ℝ) ^ (-12 : ℤ) := by positivity
    split_ifs <;> nlinarith
  exact ⟨c j, ((hc j).1).mono (fun _ h ↦ h) le_rfl le_rfl he, (hc j).2.1⟩

/-- The boundary band is initially held by the actual remainder party.
No additional owner hypothesis is supplied by the stage theorem.
Source: Part II, `con:sweep`, exceptional move (3), lines 337–338. -/
private theorem first_band_owned (k : Fin (stageCount L w)) (hk : k.val = 0) :
    ∀ x ∈ interval L 0 w,
      (afterBlockBirth L w k).owner x = Sum.inl k.castSucc := by
  intro x hx
  have hxw : x.val < w := (mem_interval.mp hx).2
  have hR : x ∉ remainderBirthTarget L w k := by
    simp only [remainderBirthTarget, hk, zero_add, one_mul, mem_interval]
    omega
  have hB : x ∉ blockBirthTarget L w k := by
    simp only [blockBirthTarget, hk, zero_mul, zero_add, one_mul, mem_interval]
    omega
  simp [afterBlockBirth, afterRemainderBirth, Sheet.changeOwner, hR, hB,
    stageFrame, stageOwner, hk]

/-- The actual local circuits of a stage, conditional only on the original-state
primitive information inequalities. The seven exceptional padding positions
are actual identities with zero error and no nonprivate gate.
This is an intermediate statement, not the physical information theorem.
Source: Part II, `con:sweep`, lines 330–343, and `prop:sweep`, lines 365–378. -/
theorem local_stage_circuits_of_primitive_information
    (hw : 1 ≤ w) (k : Fin (stageCount L w))
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (hRem : ManyBody.regionMutualInformation Ω
      (remainderBirthTarget L w k) ((stageFrame L w k.castSucc).birthEnv
        (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hBlock : ManyBody.regionMutualInformation Ω
      (blockBirthTarget L w k) ((afterRemainderBirth L w k).birthEnv
        (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hBoundary : k.val = 0 →
      ManyBody.regionMutualInformation Ω
        (leftBandTarget L w k) ((afterLeftTransfer L w k).birthEnv (Sum.inr k)) ≤
          (L : ℝ) ^ (-24 : ℤ))
    (hLeft0 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω (interval
      L ((k.val * (20 * w)) - 6 * w) ((k.val * (20 * w)) - w)) ((OneBand.aux₀ (Party := Party L w)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))).birthEnv
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft1 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω (interval
      L ((k.val * (20 * w)) - 5 * w) ((k.val * (20 * w)) - 2 * w)) ((OneBand.aux₁
      (Party := Party L w) (Sum.inr k) (Sum.inr (⟨k.val - 1, by omega⟩ : Fin
      (stageCount L w))) (k.val * (20 * w)) w).birthEnv (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft2 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω (interval
      L ((k.val * (20 * w)) - 4 * w) ((k.val * (20 * w)) - 3 * w)) ((OneBand.aux₂
      (Party := Party L w) (Sum.inl k.castSucc) (Sum.inr k) (Sum.inr (⟨k.val -
      1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv (Sum.inl k.castSucc)) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hLeft3 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω
      (OneBand.exchangeTSet (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
        (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w)
      (OneBand.exchangeESet (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
        (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hLeft4 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω (interval
      L ((k.val * (20 * w)) - 4 * w) (k.val * (20 * w))) ((OneBand.main₅ (Party := Party L w)
      (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv
      (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft5 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω (interval
      L ((k.val * (20 * w)) - 5 * w) ((k.val * (20 * w)) + w)) ((OneBand.main₆ (Party := Party L w)
      (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv
      (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft6 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω (interval
      L ((k.val * (20 * w)) - 3 * w) (k.val * (20 * w))) ((OneBand.main₆ (Party := Party L w)
      (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv
      (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft7 : ∀ hk : 0 < k.val, ManyBody.regionMutualInformation Ω (interval
      L ((k.val * (20 * w)) - 6 * w) ((k.val * (20 * w)) - 3 * w)) ((OneBand.main₈
      (Party := Party L w) (afterBlockBirth L w k).owner (Sum.inl
      k.castSucc) (Sum.inr k) (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20
      * w)) w).birthEnv (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))) ≤ (L : ℝ) ^
      (-24 : ℤ))
    (hRight0 : ManyBody.regionMutualInformation Ω (interval L (((k.val + 1) *
      (20 * w)) - 6 * w) (((k.val + 1) * (20 * w)) - w)) ((OneBand.aux₀ (Party := Party L w)
      (Sum.inr k)).birthEnv (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight1 : ManyBody.regionMutualInformation Ω (interval L (((k.val + 1) *
      (20 * w)) - 5 * w) (((k.val + 1) * (20 * w)) - 2 * w)) ((OneBand.aux₁ (Party := Party L w)
      (Sum.inl k.succ) (Sum.inr k) ((k.val + 1) * (20 * w)) w).birthEnv
      (Sum.inl k.succ)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight2 : ManyBody.regionMutualInformation Ω (interval L (((k.val + 1) *
      (20 * w)) - 4 * w) (((k.val + 1) * (20 * w)) - 3 * w)) ((OneBand.aux₂ (Party := Party L w)
      (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k) ((k.val + 1) * (20 *
      w)) w).birthEnv (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight3 : ManyBody.regionMutualInformation Ω
      (OneBand.exchangeTSet (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ)
        (Sum.inr k) ((k.val + 1) * (20 * w)) w)
      (OneBand.exchangeESet (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ)
        (Sum.inr k) ((k.val + 1) * (20 * w)) w) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight4 : ManyBody.regionMutualInformation Ω (interval L (((k.val + 1) *
      (20 * w)) - 4 * w) ((k.val + 1) * (20 * w))) ((OneBand.main₅ (Party := Party L w)
      (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight5 : ManyBody.regionMutualInformation Ω (interval L (((k.val + 1) *
      (20 * w)) - 5 * w) (((k.val + 1) * (20 * w)) + w)) ((OneBand.main₆ (Party := Party L w)
      (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ)
      (Sum.inr k) ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inl k.succ)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight6 : ManyBody.regionMutualInformation Ω (interval L (((k.val + 1) *
      (20 * w)) - 3 * w) ((k.val + 1) * (20 * w))) ((OneBand.main₆ (Party := Party L w)
      (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inl k.succ)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight7 : ManyBody.regionMutualInformation Ω (interval L (((k.val + 1) *
      (20 * w)) - 6 * w) (((k.val + 1) * (20 * w)) - 3 * w)) ((OneBand.main₈ (Party := Party L w)
      (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ)
      (Sum.inr k) ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    : ∃ c : (j : Fin 18) → OriginalCircuit
        (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) [])
        (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k (j.val + 1)) []),
      ∀ j, (c j).IsBoundedChange (stageParticipants k j) 1 1
          (4 * (L : ℝ) ^ (-12 : ℤ))
          (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val))
          (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))) ∧
        (c j).IsSourceBounded 1 ∧ (c j).nonprivateCount ≤ 1 ∧
        ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) →
          (c j).nonprivateCount = 0 ∧
            ‖(c j).eval (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val)) -
              framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
            HEq (c j) (OriginalCircuit.id
              (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) []))) := by
  classical
  have hε : 0 ≤ (L : ℝ) ^ (-12 : ℤ) := by positivity
  have h4ε : 0 ≤ 4 * (L : ℝ) ^ (-12 : ℤ) := by positivity
  have hsmall : (L : ℝ) ^ (-12 : ℤ) ≤ 4 * (L : ℝ) ^ (-12 : ℤ) := by nlinarith
  have hbirth0 : Sheet.HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k 0) (stageBoundaryFrames L w k 1)
      (1 : ℂ) {Sum.inl k.castSucc, Sum.inl k.succ} 1 1 1
      (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hop := OneBand.birth_liftOne (ℓ := []) (stageFrame L w k.castSucc)
      (remainderBirthTarget L w k) (Sum.inl k.castSucc) (Sum.inl k.succ)
      (birth_targets_owned hw k).1 hΩ hRem []
      ((initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val)) (1 : ℂ) (by simp)
    have hwiden := hop.mono (fun _ h ↦ h) le_rfl le_rfl le_rfl hsmall
    simpa only [stageBoundaryFrames_zero, stageBoundaryFrames_one, sweepFrames,
      afterRemainderBirth, Fin.val_castSucc, List.nil_append] using hwiden
  have hbirth1 : Sheet.HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k 1) (stageBoundaryFrames L w k 2)
      (1 : ℂ) {Sum.inl k.castSucc, Sum.inr k} 1 1 1
      (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hop := OneBand.birth_liftOne (ℓ := []) (afterRemainderBirth L w k)
      (blockBirthTarget L w k) (Sum.inl k.castSucc) (Sum.inr k)
      (birth_targets_owned hw k).2 hΩ hBlock []
      ((initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val)) (1 : ℂ) (by simp)
    have hwiden := hop.mono (fun _ h ↦ h) le_rfl le_rfl le_rfl hsmall
    simpa only [stageBoundaryFrames_one, stageBoundaryFrames_two, afterBlockBirth,
      List.nil_append] using hwiden
  have hleft (hk : 0 < k.val) : ∀ j : Fin 8, Sheet.HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k (j.val + 2))
      (stageBoundaryFrames L w k (j.val + 2 + 1)) (1 : ℂ)
      (OneBand.participants (Sum.inl k.castSucc) (Sum.inr k)
        (Sum.inr ⟨k.val - 1, by omega⟩) j) 1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    obtain ⟨hC, hA, -⟩ := left_band_owners hw k hk
    have hb := band_changes (afterBlockBirth L w k).owner
      (Sum.inl k.castSucc) (Sum.inr k) (Sum.inr ⟨k.val - 1, by omega⟩)
      (k.val * (20 * w)) hw (stage_left_margin w k.val (by omega)) hC hA hΩ
      (hLeft0 hk) (hLeft1 hk) (hLeft2 hk) (hLeft3 hk)
      (hLeft4 hk) (hLeft5 hk) (hLeft6 hk) (hLeft7 hk)
      (((initialAuxiliaryOrder L w).erase (leftCopyLabel L w k hk)).map
        (auxiliaryFrameBefore L w k.val))
    intro j
    have hop := hb j
    change Sheet.HasSourceBoundedChange (ℓ := []) Ω (leftBandFrames L w k hk j.val)
      (leftBandFrames L w k hk (j.val + 1)) (1 : ℂ) _ 1 1 1 _ at hop
    have ht := left_boundary_perm k hk j.succ
    have he : j.val + 1 + 2 = j.val + 2 + 1 := by omega
    simpa only [Fin.val_castSucc, Fin.val_succ, he] using
      (hop.perm_left (left_boundary_perm k hk j.castSucc)).perm_right
        ht.symm
  have hright : ∀ j : Fin 8, Sheet.HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k (j.val + 10))
      (stageBoundaryFrames L w k (j.val + 10 + 1)) (1 : ℂ)
      (OneBand.participants (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k) j)
      1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    obtain ⟨hC, hA, -⟩ := right_band_owners k
    have howners : leftBandMain L w k = afterLeftTransfer L w k :=
      leftBandMain_eq_afterLeftTransfer hw k
    have hlow : 8 * w ≤ (k.val + 1) * (20 * w) := by
      have ht := Nat.mul_le_mul_right (20 * w) (show 1 ≤ k.val + 1 by omega)
      nlinarith
    have hb := band_changes (leftBandMain L w k).owner
      (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) hw hlow
      (by simpa only [howners] using hC) (by simpa only [howners] using hA) hΩ
      hRight0 hRight1 hRight2 hRight3 hRight4 hRight5 hRight6 hRight7
      (((initialAuxiliaryOrder L w).erase (Sum.inl k)).map (leftAuxiliaryFrame L w k))
    intro j
    have hop := hb j
    change Sheet.HasSourceBoundedChange (ℓ := []) Ω (rightBandFrames L w k j.val)
      (rightBandFrames L w k (j.val + 1)) (1 : ℂ) _ 1 1 1 _ at hop
    have ht := right_boundary_perm k j.succ
    have he : j.val + 1 + 10 = j.val + 10 + 1 := by omega
    simpa only [Fin.val_castSucc, Fin.val_succ, he] using
      (hop.perm_left (right_boundary_perm k j.castSucc)).perm_right
        ht.symm
  have hboundary (hk : k.val = 0) : Sheet.HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k 2) (stageBoundaryFrames L w k 3)
      (1 : ℂ) {Sum.inr k, Sum.inl k.castSucc} 1 1 1
      (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hraw : OneBand.main₀
        (afterBlockBirth L w k).owner = afterBlockBirth L w k := rfl
    have ht : leftBandTarget L w k = interval L 0 w := by simp [leftBandTarget, hk]
    have hI : ManyBody.regionMutualInformation Ω
        (interval L 0 w) (((OneBand.main₀
          (afterBlockBirth L w k).owner).changeOwner (interval L 0 w)
            (Sum.inr k)).birthEnv (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ) := by
      simpa only [afterLeftTransfer, ht, hraw] using hBoundary hk
    have hop := OneBand.boundary_change_of_primitive_information (ℓ := [])
      (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k) w
      (first_band_owned k hk) hΩ hI []
      ((initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val))
      (1 : ℂ) (by simp)
    have hwiden := hop.mono (fun _ h ↦ h) le_rfl le_rfl le_rfl hsmall
    rw [stageBoundaryFrames_two, stageBoundaryFrames_first_death k hk, ht]
    simpa only [List.nil_append, hraw] using hwiden
  have hsteps : ∀ j : Fin 18, ∃ c : OriginalCircuit
        (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) [])
        (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k (j.val + 1)) []),
      c.IsBoundedChange (stageParticipants k j) 1 1 (4 * (L : ℝ) ^ (-12 : ℤ))
          (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val))
          (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))) ∧
        c.IsSourceBounded 1 ∧
        ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) → c.nonprivateCount = 0 ∧
          ‖c.eval (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val)) -
            framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
          HEq c (OriginalCircuit.id
            (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) []))) := by
    intro j
    by_cases h0 : j.val = 0
    · have he : j = 0 := Fin.ext h0
      subst j
      obtain ⟨c, hc, hs⟩ := hbirth0
      refine ⟨c, ?_, hs, ?_⟩
      · simpa [stageParticipants] using hc
      · rintro ⟨_, hlo, _⟩
        omega
    · by_cases h1 : j.val = 1
      · have he : j = 1 := Fin.ext h1
        subst j
        obtain ⟨c, hc, hs⟩ := hbirth1
        refine ⟨c, ?_, hs, ?_⟩
        · simpa [stageParticipants] using hc
        · rintro ⟨_, hlo, _⟩
          omega
      · by_cases hlt : j.val < 10
        · by_cases hk : 0 < k.val
          · let u : Fin 8 := ⟨j.val - 2, by omega⟩
            have he : u.val + 2 = j.val := by dsimp [u]; omega
            have hp : stageParticipants k j =
                OneBand.participants (Sum.inl k.castSucc) (Sum.inr k)
                  (Sum.inr ⟨k.val - 1, by omega⟩) u := by
              simp only [stageParticipants, dite_eq_right h0, dite_eq_right h1,
                dite_eq_left hlt, dite_eq_left hk]
              rfl
            have hop : Sheet.HasSourceBoundedChange (ℓ := []) Ω
                (stageBoundaryFrames L w k j.val)
                (stageBoundaryFrames L w k (j.val + 1)) (1 : ℂ)
                (stageParticipants k j) 1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
              rw [hp]
              simpa only [he] using hleft hk u
            obtain ⟨c, hc, hs⟩ := hop
            refine ⟨c, hc, hs, ?_⟩
            rintro ⟨hk0, _, _⟩
            omega
          · have hk0 : k.val = 0 := by omega
            by_cases h2 : j.val = 2
            · have he : j = 2 := Fin.ext h2
              subst j
              obtain ⟨c, hc, hs⟩ := hboundary hk0
              refine ⟨c, ?_, hs, ?_⟩
              · simpa [stageParticipants, hk0] using hc
              · rintro ⟨_, hlo, _⟩
                omega
            · have hS : stageBoundaryFrames L w k j.val = afterLeftFrames L w k :=
                stageBoundaryFrames_first_left k hk0 (by omega) (by omega)
              have hT : stageBoundaryFrames L w k (j.val + 1) =
                  afterLeftFrames L w k :=
                stageBoundaryFrames_first_left k hk0 (by omega) (by omega)
              rw [hS, hT]
              refine ⟨OriginalCircuit.id _,
                OriginalCircuit.isBoundedChange_id (stageParticipants k j) 1 1 h4ε _,
                trivial, ?_⟩
              intro _
              refine ⟨rfl, ?_, HEq.rfl⟩
              change ‖framesVec (Sheet.refFamily Ω) (afterLeftFrames L w k) -
                framesVec (Sheet.refFamily Ω) (afterLeftFrames L w k)‖ = 0
              simp
        · let u : Fin 8 := ⟨j.val - 10, by have hj := j.isLt; omega⟩
          have he : u.val + 10 = j.val := by dsimp [u]; omega
          have hp : stageParticipants k j =
              OneBand.participants (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k) u := by
            simp only [stageParticipants, dite_eq_right h0, dite_eq_right h1, dite_eq_right hlt]
            rfl
          have hop : Sheet.HasSourceBoundedChange (ℓ := []) Ω
              (stageBoundaryFrames L w k j.val)
              (stageBoundaryFrames L w k (j.val + 1)) (1 : ℂ)
              (stageParticipants k j) 1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
            rw [hp]
            simpa only [he] using hright u
          obtain ⟨c, hc, hs⟩ := hop
          refine ⟨c, hc, hs, ?_⟩
          rintro ⟨_, _, hbad⟩
          omega
  choose c hc using hsteps
  exact ⟨c, fun j ↦ ⟨(hc j).1, (hc j).2.1, (hc j).1.nonprivateCount_le, (hc j).2.2⟩⟩

end TNLean.MPS.AreaLaw.ChainSweep
end

end

section

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice TNLean.Lattice.PartyCircuit TNLean.Lattice.Sheet

open ManyBody (IsGapped groundSpace ChainInteraction)

/-- The physical assumptions imply the actual eighteen local circuits at
every stage, including the seven identity operations after the first direct
death. The constants precede all chain and state data. Neither information
bounds nor owner, circuit, endpoint or norm conclusions are assumed.
Source: Part II, `prop:sweep`, construction and geometric proof, lines 365–378,
using Part II, `lem:logsep`, lines 472–488. -/
theorem local_stage_circuits_of_logarithmic_separation
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (D₂₄ : ℝ) (L₀ : ℕ), 0 < D₂₄ ∧ 1 ≤ L₀ ∧
      ∀ (L : ℕ), L₀ ≤ L →
      ∀ (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (w : ℕ), 1 ≤ w →
        D₂₄ * Real.log (L : ℝ) ≤ (w : ℝ) →
      ∀ k : Fin (stageCount L w),
        ∃ c : (j : Fin 18) → OriginalCircuit
            (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) [])
            (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k (j.val + 1)) []),
          ∀ j, (c j).IsBoundedChange (stageParticipants k j) 1 1
              (4 * (L : ℝ) ^ (-12 : ℤ))
              (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val))
              (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))) ∧
            (c j).IsSourceBounded 1 ∧ (c j).nonprivateCount ≤ 1 ∧
            ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) →
              (c j).nonprivateCount = 0 ∧
                ‖(c j).eval (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val)) -
                  framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
                HEq (c j) (OriginalCircuit.id
                  (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) []))) := by
  classical
  obtain ⟨Dstage, Nstage, hDstage, hNstage, hstage⟩ :=
    birth_death_information_of_logarithmic_separation q hq R J Δ hΔ
  obtain ⟨Dband, Nband, _, _, hband⟩ :=
    OneBand.primitive_information_of_logarithmic_separation q hq R J Δ hΔ
  refine ⟨max Dstage Dband, max Nstage Nband,
    hDstage.trans_le (le_max_left _ _), hNstage.trans (le_max_left _ _), ?_⟩
  intro L hL h hh hhJ Ω E₀ hΩ hgap hspan w hw hwidth k
  have hLs : Nstage ≤ L := (le_max_left _ _).trans hL
  have hLb : Nband ≤ L := (le_max_right _ _).trans hL
  have hlog : 0 ≤ Real.log (L : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hNstage.trans hLs)
  have hwidthStage : Dstage * Real.log (L : ℝ) ≤ (w : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog).trans hwidth
  have hwidthBand : Dband * Real.log (L : ℝ) ≤ (w : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog).trans hwidth
  have hdiv : 4 ≤ L / (20 * w) := by
    have hk := k.isLt
    unfold stageCount at hk
    omega
  have hfour : 4 * (20 * w) ≤ L :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 20 * w)).1 hdiv
  have hgeometry : 3 * (20 * w) ≤ L := by omega
  obtain ⟨hRem, hBlock, hBoundary⟩ :=
    hstage L hLs h hh hhJ Ω E₀ hΩ hgap hspan w hw hwidthStage k
  have hleftOwners := left_band_owners hw k
  have hleft (hk : 0 < k.val) :=
    hband L hLb h hh hhJ Ω E₀ hΩ hgap hspan (Party L w)
      (afterBlockBirth L w k).owner
      (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))
      (k.val * (20 * w)) w (by simp)
      (by
        intro he
        have hv := congrArg Fin.val (Sum.inr.inj he)
        change k.val = k.val - 1 at hv
        omega)
      hw (stage_left_margin w k.val (by omega))
      (hleftOwners hk).1 (hleftOwners hk).2.1 (hleftOwners hk).2.2 hwidthBand
  have hrightOwners := right_band_owners k
  rw [← leftBandMain_eq_afterLeftTransfer hw k]
    at hrightOwners
  have hright :=
    hband L hLb h hh hhJ Ω E₀ hΩ hgap hspan (Party L w)
      (leftBandMain L w k).owner
      (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) w (by simp) (by simp)
      hw (stage_left_margin w (k.val + 1) (by omega))
      hrightOwners.1 hrightOwners.2.1 hrightOwners.2.2 hwidthBand
  exact local_stage_circuits_of_primitive_information (q := q)
    hw k Ω hΩ hRem hBlock hBoundary
    (fun hk ↦ (hleft hk).1) (fun hk ↦ (hleft hk).2.1)
    (fun hk ↦ (hleft hk).2.2.1) (fun hk ↦ (hleft hk).2.2.2.1)
    (fun hk ↦ (hleft hk).2.2.2.2.1) (fun hk ↦ (hleft hk).2.2.2.2.2.1)
    (fun hk ↦ (hleft hk).2.2.2.2.2.2.1) (fun hk ↦ (hleft hk).2.2.2.2.2.2.2)
    hright.1 hright.2.1 hright.2.2.1 hright.2.2.2.1
    hright.2.2.2.2.1 hright.2.2.2.2.2.1 hright.2.2.2.2.2.2.1 hright.2.2.2.2.2.2.2

end TNLean.MPS.AreaLaw.ChainSweep
end

end
