/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepPath
import TNLean.MPS.AreaLaw.OwnershipChanges
import TNLean.MPS.AreaLaw.ChainStageIncidence

/-!
# Conditional circuits on the actual eighteen-operation stage path

The construction combines the two initial births, the actual eight-operation
bands, and the exceptional first
left death with seven identity circuits. The source and target are the existing
nineteen stage boundaries. Private entrance and exit permutations are composed
inside the adjacent primitive operations and occupy no additional slot.

All information hypotheses concern the original vector and the actual primitive
frames. They are explicit intermediate assumptions, not a replacement for the
physical information estimates. No circuit, trajectory, endpoint identity,
owner relation, aggregate information certificate or lifetime bound is supplied.
The existing chronological composition and error/count theorems are not repeated.

The stage-frame geometry and the eight-operation band construction are those
of the existing modules; their hypotheses and retained auxiliary labels are unchanged.

Source: the one-dimensional note, Part II, `con:sweep`, lines 330–343,
`con:band`, lines 260–276, and `prop:sweep`, proof, lines 365–378.

**Local fix (half-open lattice bands):** The operations and their retained
auxiliaries are those of the corrected band construction. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.PairEffect TNLean.PEPS.EncodedFrame

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

variable [NeZero q]

/-- A private specialization of the existing public birth and stack lift.
This is the second copy of this short proof across two files, not a claimed
third occurrence. Source: Part II, `con:sweep`, moves (1)–(2), lines 334–335. -/
private theorem stage_birth (F : Sheet (Fin L) (Party L w)) (T : Finset (Fin L))
    (P Q : Party L w) (hTP : ∀ x ∈ T, F.owner x = P) (hF : F.holes = [])
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω T
      (F.birthEnv P) ≤ (L : ℝ) ^ (-24 : ℤ)) (post : List (Sheet (Fin L) (Party L w))) :
    HasSourceBoundedChange (ℓ := []) Ω (F :: post) (F.changeOwner T Q :: post) (1 : ℂ)
      {P, Q} 1 1 1 ((L : ℝ) ^ (-12 : ℤ)) := by
  let F₀ : Sheet (Fin L) (Party L w) := Sheet.mk F.owner
  have hraw : F₀ = F := by
    rcases F with ⟨own, holes, hdisjoint⟩
    dsimp [F₀] at hF ⊢
    subst holes
    rfl
  have hI' : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω T
      (F₀.birthEnv P) ≤ (L : ℝ) ^ (-(2 * (12 : ℝ))) := by
    simpa only [hraw, show -(2 * (12 : ℝ)) = (-24 : ℝ) by norm_num,
      Real.rpow_neg_ofNat] using hI
  obtain ⟨_, _, _, v, hv, hu, hs, _, herr⟩ :=
    birth_bounded_rpow F.owner T P Q hTP hΩ (12 : ℝ) hI'
  have hop : HasSourceBoundedChange (ℓ := []) Ω (F₀ :: post)
      (F₀.changeOwner T Q :: post) (1 : ℂ) {P, Q} 1 1 1
        ((L : ℝ) ^ (-12 : ℤ)) :=
    hasSourceBoundedChange_liftOne [] post
      (Word.isBoundedChange_toOriginalCircuit hv hu hs le_rfl
        (by convert herr using 1 <;> first | rfl | simp only [Real.rpow_neg_ofNat]))
      (v.isSourceBounded_toOriginalCircuit hv) hΩ.le (by simp)
  simpa only [hraw] using hop

/-- The existing eight-operation construction with a uniform error bound.
The eight hypotheses remain the actual primitive information inequalities.
Source: Part II, `con:band`, lines 260–276. -/
private theorem band_changes (own : Fin L → Party L w) (A B C : Party L w) (a : ℕ)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a) (hright : a + 2 * w ≤ L)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C)
    (hA : ∀ x ∈ interval L a (a + w), own x = A)
    (hB : ∀ x ∈ interval L (a + w) (a + 2 * w), own x = B)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hI0 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (a - 6 * w) (a -
      w)) ((OneBand.aux₀ (Party := Party L w) C).birthEnv C) ≤ (L : ℝ) ^
      (-24 : ℤ))
    (hI1 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (a - 5 * w) (a - 2
      * w)) ((OneBand.aux₁ (Party := Party L w) B C a w).birthEnv B) ≤ (L : ℝ)
      ^ (-24 : ℤ))
    (hI2 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (a - 4 * w) (a - 3
      * w)) ((OneBand.aux₂ (Party := Party L w) A B C a w).birthEnv A) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI3 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω ((OneBand.exchange
      (Party := Party L w) own A B C a w).tSet C) ((OneBand.exchange
      (Party := Party L w) own A B C a w).eSet C) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hI4 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (a - 4 * w) a)
      ((OneBand.main₅ (Party := Party L w) own A B C a w).birthEnv A) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI5 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (a - 5 * w) (a +
      w)) ((OneBand.main₆ (Party := Party L w) own A B C a w).birthEnv B) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI6 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (a - 3 * w) a)
      ((OneBand.main₆ (Party := Party L w) own A B C a w).birthEnv B) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hI7 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (a - 6 * w) (a - 3
      * w)) ((OneBand.main₈ (Party := Party L w) own A B C a w).birthEnv C) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (post : List (Sheet (Fin L) (Party L w))) :
    ∀ j : Fin 8, HasSourceBoundedChange (ℓ := []) Ω
      (OneBand.frames (Party := Party L w) own A B C a w j.val ++ post)
      (OneBand.frames (Party := Party L w) own A B C a w (j.val + 1) ++ post)
        (1 : ℂ)
      (OneBand.participants A B C j) 1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
  obtain ⟨c, hc⟩ := OneBand.circuits_of_primitive_information (ℓ := []) own A
    B C a w
    hAB hAC hBC hw hleft hright hC hA hB hΩ
    hI0 hI1 hI2 hI3 hI4 hI5 hI6 hI7 [] post (1 : ℂ) (by simp)
  intro j
  have he : (if j.val = 3 then 4 * (L : ℝ) ^ (-12 : ℤ)
      else (L : ℝ) ^ (-12 : ℤ)) ≤ 4 * (L : ℝ) ^ (-12 : ℤ) := by
    have hε : 0 ≤ (L : ℝ) ^ (-12 : ℤ) := by positivity
    split_ifs <;> nlinarith
  exact ⟨c j, ((hc j).1).mono (fun _ h ↦ h) le_rfl le_rfl he, (hc j).2.1⟩

omit [NeZero q] in
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
    stageFrame, Sheet.mk, stageOwner, hk]

/-- The actual local circuits of a stage, conditional only on the original-state
primitive information inequalities. The seven exceptional padding positions
are actual identities with zero error and no nonprivate gate.
This is an intermediate statement, not the physical information theorem.
Source: Part II, `con:sweep`, lines 330–343, and `prop:sweep`, lines 365–378. -/
theorem local_stage_circuits_of_primitive_information
    (hw : 1 ≤ w) (hL : 3 * (20 * w) ≤ L) (k : Fin (stageCount L w))
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (hRem : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (remainderBirthTarget L w k) ((stageFrame L w k.castSucc).birthEnv
        (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hBlock : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      (blockBirthTarget L w k) ((afterRemainderBirth L w k).birthEnv
        (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hBoundary : k.val = 0 →
      FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
        (leftBandTarget L w k) ((afterLeftTransfer L w k).birthEnv (Sum.inr k)) ≤
          (L : ℝ) ^ (-24 : ℤ))
    (hLeft0 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval
      L ((k.val * (20 * w)) - 6 * w) ((k.val * (20 * w)) - w)) ((OneBand.aux₀ (Party := Party L w)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))).birthEnv
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft1 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval
      L ((k.val * (20 * w)) - 5 * w) ((k.val * (20 * w)) - 2 * w)) ((OneBand.aux₁
      (Party := Party L w) (Sum.inr k) (Sum.inr (⟨k.val - 1, by omega⟩ : Fin
      (stageCount L w))) (k.val * (20 * w)) w).birthEnv (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft2 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval
      L ((k.val * (20 * w)) - 4 * w) ((k.val * (20 * w)) - 3 * w)) ((OneBand.aux₂
      (Party := Party L w) (Sum.inl k.castSucc) (Sum.inr k) (Sum.inr (⟨k.val -
      1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv (Sum.inl k.castSucc)) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hLeft3 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
      ((OneBand.exchange (Party := Party L w) (afterBlockBirth L w
      k).owner (Sum.inl k.castSucc) (Sum.inr k) (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L
      w))) (k.val * (20 * w)) w).tSet (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))))
      ((OneBand.exchange (Party := Party L w) (afterBlockBirth L w
      k).owner (Sum.inl k.castSucc) (Sum.inr k) (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L
      w))) (k.val * (20 * w)) w).eSet (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))) ≤
      (L : ℝ) ^ (-24 : ℤ))
    (hLeft4 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval
      L ((k.val * (20 * w)) - 4 * w) (k.val * (20 * w))) ((OneBand.main₅ (Party := Party L w)
      (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv
      (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft5 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval
      L ((k.val * (20 * w)) - 5 * w) ((k.val * (20 * w)) + w)) ((OneBand.main₆ (Party := Party L w)
      (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv
      (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft6 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval
      L ((k.val * (20 * w)) - 3 * w) (k.val * (20 * w))) ((OneBand.main₆ (Party := Party L w)
      (afterBlockBirth L w k).owner (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20 * w)) w).birthEnv
      (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hLeft7 : ∀ hk : 0 < k.val, FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval
      L ((k.val * (20 * w)) - 6 * w) ((k.val * (20 * w)) - 3 * w)) ((OneBand.main₈
      (Party := Party L w) (afterBlockBirth L w k).owner (Sum.inl
      k.castSucc) (Sum.inr k) (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w))) (k.val * (20
      * w)) w).birthEnv (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))) ≤ (L : ℝ) ^
      (-24 : ℤ))
    (hRight0 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (((k.val + 1) *
      (20 * w)) - 6 * w) (((k.val + 1) * (20 * w)) - w)) ((OneBand.aux₀ (Party := Party L w)
      (Sum.inr k)).birthEnv (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight1 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (((k.val + 1) *
      (20 * w)) - 5 * w) (((k.val + 1) * (20 * w)) - 2 * w)) ((OneBand.aux₁ (Party := Party L w)
      (Sum.inl k.succ) (Sum.inr k) ((k.val + 1) * (20 * w)) w).birthEnv
      (Sum.inl k.succ)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight2 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (((k.val + 1) *
      (20 * w)) - 4 * w) (((k.val + 1) * (20 * w)) - 3 * w)) ((OneBand.aux₂ (Party := Party L w)
      (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k) ((k.val + 1) * (20 *
      w)) w).birthEnv (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight3 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω ((OneBand.exchange
      (Party := Party L w) (leftBandMain L w k).owner (Sum.inl
      k.castSucc) (Sum.inl k.succ) (Sum.inr k) ((k.val + 1) * (20 * w)) w).tSet (Sum.inr k))
      ((OneBand.exchange (Party := Party L w) (leftBandMain L w k).owner
      (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k) ((k.val + 1) * (20 * w)) w).eSet (Sum.inr
      k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight4 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (((k.val + 1) *
      (20 * w)) - 4 * w) ((k.val + 1) * (20 * w))) ((OneBand.main₅ (Party := Party L w)
      (q := q) (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inl k.castSucc)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight5 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (((k.val + 1) *
      (20 * w)) - 5 * w) (((k.val + 1) * (20 * w)) + w)) ((OneBand.main₆ (Party := Party L w)
      (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ)
      (Sum.inr k) ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inl k.succ)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight6 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (((k.val + 1) *
      (20 * w)) - 3 * w) ((k.val + 1) * (20 * w))) ((OneBand.main₆ (Party := Party L w)
      (q := q) (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inl k.succ)) ≤ (L : ℝ) ^ (-24 : ℤ))
    (hRight7 : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (interval L (((k.val + 1) *
      (20 * w)) - 6 * w) (((k.val + 1) * (20 * w)) - 3 * w)) ((OneBand.main₈ (Party := Party L w)
      (leftBandMain L w k).owner (Sum.inl k.castSucc) (Sum.inl k.succ)
      (Sum.inr k) ((k.val + 1) * (20 * w)) w).birthEnv (Sum.inr k)) ≤ (L : ℝ) ^ (-24 : ℤ))
    : ∃ c : (j : Fin 18) → OriginalCircuit
        (stackRegs (stageBoundaryFrames L w k j.val) [])
        (stackRegs (stageBoundaryFrames L w k (j.val + 1)) []),
      ∀ j, (c j).IsBoundedChange (stageParticipants k j) 1 1
          (4 * (L : ℝ) ^ (-12 : ℤ))
          (framesVec Ω (stageBoundaryFrames L w k j.val))
          (framesVec Ω (stageBoundaryFrames L w k (j.val + 1))) ∧
        (c j).IsSourceBounded 1 ∧ (c j).nonprivateCount ≤ 1 ∧
        ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) →
          (c j).nonprivateCount = 0 ∧
            ‖(c j).eval (framesVec Ω (stageBoundaryFrames L w k j.val)) -
              framesVec Ω (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
            HEq (c j) (OriginalCircuit.id
              (stackRegs (stageBoundaryFrames L w k j.val) []))) := by
  classical
  have hε : 0 ≤ (L : ℝ) ^ (-12 : ℤ) := by positivity
  have h4ε : 0 ≤ 4 * (L : ℝ) ^ (-12 : ℤ) := by positivity
  have hsmall : (L : ℝ) ^ (-12 : ℤ) ≤ 4 * (L : ℝ) ^ (-12 : ℤ) := by nlinarith
  have hmargin := stage_right_margin L w hL k
  have hbirth0 : HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k 0) (stageBoundaryFrames L w k 1)
      (1 : ℂ) {Sum.inl k.castSucc, Sum.inl k.succ} 1 1 1
      (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hop := stage_birth (stageFrame L w k.castSucc)
      (remainderBirthTarget L w k) (Sum.inl k.castSucc) (Sum.inl k.succ)
      (birth_targets_owned hw k).1 rfl hΩ hRem
      ((initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val))
    have hwiden := hop.mono (fun _ h ↦ h) le_rfl le_rfl le_rfl hsmall
    simpa only [stageBoundaryFrames_zero, stageBoundaryFrames_one, sweepFrames,
      afterRemainderBirth, Fin.val_castSucc] using hwiden
  have hbirth1 : HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k 1) (stageBoundaryFrames L w k 2)
      (1 : ℂ) {Sum.inl k.castSucc, Sum.inr k} 1 1 1
      (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hop := stage_birth (afterRemainderBirth L w k)
      (blockBirthTarget L w k) (Sum.inl k.castSucc) (Sum.inr k)
      (birth_targets_owned hw k).2 rfl hΩ hBlock
      ((initialAuxiliaryOrder L w).map (auxiliaryFrameBefore L w k.val))
    have hwiden := hop.mono (fun _ h ↦ h) le_rfl le_rfl le_rfl hsmall
    simpa only [stageBoundaryFrames_one, stageBoundaryFrames_two, afterBlockBirth] using hwiden
  have hleft (hk : 0 < k.val) : ∀ j : Fin 8, HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k (j.val + 2))
      (stageBoundaryFrames L w k (j.val + 2 + 1)) (1 : ℂ)
      (OneBand.participants (Sum.inl k.castSucc) (Sum.inr k)
        (Sum.inr ⟨k.val - 1, by omega⟩) j) 1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hAB : (Sum.inl k.castSucc : Party L w) ≠ Sum.inr k := by simp
    have hAC : (Sum.inl k.castSucc : Party L w) ≠ Sum.inr ⟨k.val - 1, by omega⟩ := by simp
    have hBC : (Sum.inr k : Party L w) ≠ Sum.inr ⟨k.val - 1, by omega⟩ := by
      intro h
      have hv := congrArg Fin.val (Sum.inr.inj h)
      change k.val = k.val - 1 at hv
      omega
    obtain ⟨hC, hA, hB⟩ := left_band_owners (q := q) hw k hk
    have hb := band_changes (afterBlockBirth L w k).owner
      (Sum.inl k.castSucc) (Sum.inr k) (Sum.inr ⟨k.val - 1, by omega⟩)
      (k.val * (20 * w)) hAB hAC hBC hw (stage_left_margin w k.val (by omega))
      (by nlinarith [hmargin]) hC hA hB hΩ
      (hLeft0 hk) (hLeft1 hk) (hLeft2 hk) (hLeft3 hk)
      (hLeft4 hk) (hLeft5 hk) (hLeft6 hk) (hLeft7 hk)
      (((initialAuxiliaryOrder L w).erase (leftCopyLabel L w k hk)).map
        (auxiliaryFrameBefore L w k.val))
    intro j
    have hop := hb j
    change HasSourceBoundedChange (ℓ := []) Ω (leftBandFrames L w k hk j.val)
      (leftBandFrames L w k hk (j.val + 1)) (1 : ℂ) _ 1 1 1 _ at hop
    have ht := left_boundary_perm (q := q) k hk j.succ
    have he : j.val + 1 + 2 = j.val + 2 + 1 := by omega
    simpa only [Fin.val_castSucc, Fin.val_succ, he] using
      (hop.perm_left (left_boundary_perm (q := q) k hk j.castSucc)).perm_right
        ht.symm
  have hright : ∀ j : Fin 8, HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k (j.val + 10))
      (stageBoundaryFrames L w k (j.val + 10 + 1)) (1 : ℂ)
      (OneBand.participants (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k) j)
      1 1 1 (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hAB : (Sum.inl k.castSucc : Party L w) ≠ Sum.inl k.succ := by
      intro h
      have hv := congrArg Fin.val (Sum.inl.inj h)
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    have hAC : (Sum.inl k.castSucc : Party L w) ≠ Sum.inr k := by simp
    have hBC : (Sum.inl k.succ : Party L w) ≠ Sum.inr k := by simp
    obtain ⟨hC, hA, hB⟩ := right_band_owners (q := q) hw k
    have howners : leftBandMain L w k = afterLeftTransfer L w k :=
      leftBandMain_eq_afterLeftTransfer hw hL k
    have hlow : 8 * w ≤ (k.val + 1) * (20 * w) := by
      have ht := Nat.mul_le_mul_right (20 * w) (show 1 ≤ k.val + 1 by omega)
      nlinarith
    have hb := band_changes (leftBandMain L w k).owner
      (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) hAB hAC hBC hw hlow (by nlinarith [hmargin])
      (by simpa only [howners] using hC) (by simpa only [howners] using hA)
      (by simpa only [howners] using hB) hΩ
      hRight0 hRight1 hRight2 hRight3 hRight4 hRight5 hRight6 hRight7
      (((initialAuxiliaryOrder L w).erase (Sum.inl k)).map (leftAuxiliaryFrame L w k))
    intro j
    have hop := hb j
    change HasSourceBoundedChange (ℓ := []) Ω (rightBandFrames L w k j.val)
      (rightBandFrames L w k (j.val + 1)) (1 : ℂ) _ 1 1 1 _ at hop
    have ht := right_boundary_perm (q := q) k j.succ
    have he : j.val + 1 + 10 = j.val + 10 + 1 := by omega
    simpa only [Fin.val_castSucc, Fin.val_succ, he] using
      (hop.perm_left (right_boundary_perm (q := q) k j.castSucc)).perm_right
        ht.symm
  have hboundary (hk : k.val = 0) : HasSourceBoundedChange (ℓ := []) Ω
      (stageBoundaryFrames L w k 2) (stageBoundaryFrames L w k 3)
      (1 : ℂ) {Sum.inr k, Sum.inl k.castSucc} 1 1 1
      (4 * (L : ℝ) ^ (-12 : ℤ)) := by
    have hraw : OneBand.main₀
        (afterBlockBirth L w k).owner = afterBlockBirth L w k := rfl
    have ht : leftBandTarget L w k = interval L 0 w := by simp [leftBandTarget, hk]
    have hI : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
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
        (stackRegs (stageBoundaryFrames L w k j.val) [])
        (stackRegs (stageBoundaryFrames L w k (j.val + 1)) []),
      c.IsBoundedChange (stageParticipants k j) 1 1 (4 * (L : ℝ) ^ (-12 : ℤ))
          (framesVec Ω (stageBoundaryFrames L w k j.val))
          (framesVec Ω (stageBoundaryFrames L w k (j.val + 1))) ∧
        c.IsSourceBounded 1 ∧
        ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) → c.nonprivateCount = 0 ∧
          ‖c.eval (framesVec Ω (stageBoundaryFrames L w k j.val)) -
            framesVec Ω (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
          HEq c (OriginalCircuit.id
            (stackRegs (stageBoundaryFrames L w k j.val) []))) := by
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
            have hop : HasSourceBoundedChange (ℓ := []) Ω
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
              change ‖framesVec Ω (afterLeftFrames L w k) -
                framesVec Ω (afterLeftFrames L w k)‖ = 0
              simp
        · let u : Fin 8 := ⟨j.val - 10, by have hj := j.isLt; omega⟩
          have he : u.val + 10 = j.val := by dsimp [u]; omega
          have hp : stageParticipants k j =
              OneBand.participants (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k) u := by
            simp only [stageParticipants, dite_eq_right h0, dite_eq_right h1, dite_eq_right hlt]
            rfl
          have hop : HasSourceBoundedChange (ℓ := []) Ω
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
