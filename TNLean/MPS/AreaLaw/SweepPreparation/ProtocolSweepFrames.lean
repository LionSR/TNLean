/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolTerminalCoordinates
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepGeometry
import TNLean.MPS.AreaLaw.SweepPreparation.BandDissolution
import TNLean.MPS.AreaLaw.Entropy.AreaLaw
import Mathlib.Data.Nat.Dist
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The main sheets of successive chain stages

The main sheet is a sheet of the chain, an owner for each site. The two births
and the endpoints of the two band transfers are explicit changes of owner.
The ownership calculations identify the next stage, the actual environments
of both births, and the flanks required for both band operations. The corrected
one-band construction supplies the actual main sheets with these endpoints.
At stage zero the left transfer is a direct death; there is no fictitious
left-hand party.

These are intermediate ownership statements, not constructions of the gates
or their information estimates. Source: the one-dimensional note, Part II,
`part2b_mps_protocol.tex`, Construction `con:sweep`, lines 330–343, and the
proof of Proposition `prop:sweep`, lines 365–378.

**Local fix (half-open lattice bands):** Integer-ended bands are half-open;
the unchanged open exchange window belongs to the separate band construction.
The correction is recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

## Information estimates for the births and the first direct death

The two births of a sweep stage and the direct death at stage zero use
their actual before-birth or after-death environments. These regions are
separated from their targets by at least the chosen width. The physical
logarithmic-separation theorem then gives information at most L⁻⁶⁰ for
the original ground state. The constants are chosen before the chain,
Hamiltonian, vector, stage and width. No information estimate is assumed.

**Scope restriction (contiguous chains):** The sites are `Fin L`. The
finite-domain distinction is recorded in
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (half-open lattice bands):** The targets use the existing
half-open convention, recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Sources: the one-dimensional note, Part II, `con:sweep`, lines 330–343,
and `prop:sweep`, proof, lines 365–374; Part II, `lem:logsep`, lines
472–488. The information exponent is 24, as in the source's logarithmic
width choice.
-/

section

open ManyBody (interval mem_interval)

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open QuantumCircuit.Party

variable {L w : ℕ}

/-- Before stage `k`, completed blocks retain their respective parties and the
suffix belongs to the remainder party `R_k`.
Source: Part II, `con:sweep`, lines 331–332. -/
def stageOwner (L w : ℕ) (k : Fin (stageCount L w + 1)) (x : Fin L) : Party L w :=
  if hx : x.val < k.val * (20 * w) then
    .inr ⟨x.val / (20 * w), Nat.lt_of_lt_of_le
      (Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hx))
      (Nat.le_of_lt_succ k.isLt)⟩
  else .inl k

/-- The actual main sheet before a stage.
Source: Part II, `con:sweep`, lines 331–332. -/
def stageFrame (L w : ℕ) (k : Fin (stageCount L w + 1)) : Sheet (Fin L) (Party L w) :=
  ⟨stageOwner L w k⟩

/-- The first birth gives the far suffix to the next remainder party.
Source: Part II, `con:sweep`, move (1), line 334. -/
def remainderBirthTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L ((k.val + 1) * (20 * w) + w) L

/-- The second birth gives the interior of the next block to its new owner.
Source: Part II, `con:sweep`, move (2), line 335. -/
def blockBirthTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L (k.val * (20 * w) + w) ((k.val + 1) * (20 * w))

/-- The left band at stage `k`, including stage zero's direct death.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def leftBandTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L (k.val * (20 * w)) (k.val * (20 * w) + w)

/-- The right band at stage `k`.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def rightBandTarget (L w : ℕ) (k : Fin (stageCount L w)) : Finset (Fin L) :=
  interval L ((k.val + 1) * (20 * w)) ((k.val + 1) * (20 * w) + w)

/-- The sheet after the first actual birth target changes owner.
Source: Part II, `con:sweep`, move (1), line 334. -/
def afterRemainderBirth (L w : ℕ) (k : Fin (stageCount L w)) : Sheet (Fin L) (Party L w) :=
  (stageFrame L w k.castSucc).changeOwner (remainderBirthTarget L w k) (.inl k.succ)

/-- The sheet after both actual birth targets change owner.
Source: Part II, `con:sweep`, moves (1)–(2), lines 333–334. -/
def afterBlockBirth (L w : ℕ) (k : Fin (stageCount L w)) : Sheet (Fin L) (Party L w) :=
  (afterRemainderBirth L w k).changeOwner (blockBirthTarget L w k) (.inr k)

/-- The main-sheet endpoint of the left band transfer. At stage zero the same
endpoint is obtained by a direct death. Realizing this change is separate.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def afterLeftTransfer (L w : ℕ) (k : Fin (stageCount L w)) : Sheet (Fin L) (Party L w) :=
  (afterBlockBirth L w k).changeOwner (leftBandTarget L w k) (.inr k)

/-- The main-sheet endpoint of the right band transfer. Realization by the
corrected band construction is a separate obligation.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def afterRightTransfer (L w : ℕ) (k : Fin (stageCount L w)) : Sheet (Fin L) (Party L w) :=
  (afterLeftTransfer L w k).changeOwner (rightBandTarget L w k) (.inl k.succ)

/-- A site in the kth half-open block has quotient k.
Source: Part II, `eq:blocks`, lines 247–255. -/
private theorem div_eq_of_mem_block (hw : 1 ≤ w) {x k : ℕ}
    (hlo : k * (20 * w) ≤ x) (hhi : x < (k + 1) * (20 * w)) :
    x / (20 * w) = k := by
  have ht : 0 < 20 * w := by omega
  have h₁ : k ≤ x / (20 * w) := (Nat.le_div_iff_mul_le ht).2 hlo
  have h₂ : x / (20 * w) < k + 1 := (Nat.div_lt_iff_lt_mul ht).2 hhi
  omega

/-- A completed block keeps its actual finite party label at a later stage.
Source: Part II, `con:sweep`, lines 331–332. -/
private theorem stageOwner_at_block (hw : 1 ≤ w)
    (k : Fin (stageCount L w + 1)) (j : Fin (stageCount L w)) (x : Fin L)
    (hjk : j.val < k.val) (hlo : j.val * (20 * w) ≤ x.val)
    (hhi : x.val < (j.val + 1) * (20 * w)) : stageOwner L w k x = Sum.inr j := by
  have hmul := Nat.mul_le_mul_right (20 * w) (show j.val + 1 ≤ k.val by omega)
  have hx : x.val < k.val * (20 * w) := hhi.trans_le hmul
  have hdiv := div_eq_of_mem_block hw hlo hhi
  unfold stageOwner
  rw [dite_eq_left hx]
  exact congrArg Sum.inr (Fin.ext hdiv)

/-- Neither birth changes a site before the new block interior.
Source: Part II, `con:sweep`, moves (1)–(2), lines 334–335. -/
private theorem unused_births_of_lt (k : Fin (stageCount L w)) (x : Fin L)
    (hx : x.val < k.val * (20 * w) + w) :
    x ∉ remainderBirthTarget L w k ∧ x ∉ blockBirthTarget L w k := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  simp only [remainderBirthTarget, blockBirthTarget, mem_interval]
  omega

/-- The completed-block birth and left transfer do not change a site in
the next remainder. Source: Part II, `con:sweep`, moves (2)–(3), lines 335–338. -/
private theorem passed_targets_of_le (k : Fin (stageCount L w)) (x : Fin L)
    (hx : (k.val + 1) * (20 * w) ≤ x.val) :
    x ∉ blockBirthTarget L w k ∧ x ∉ leftBandTarget L w k := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  simp only [blockBirthTarget, leftBandTarget, mem_interval]
  omega

/-- Initially the entire main sheet belongs to `R_0`.
Source: Part II, `con:sweep`, line 331. -/
theorem stageOwner_zero (L w : ℕ) :
    stageOwner L w 0 = fun _ ↦ Sum.inl (0 : Fin (stageCount L w + 1)) := by
  funext x
  simp [stageOwner]

/-- The final stage has exactly the previously specified terminal main owner.
Source: Part II, `con:sweep`, line 342. -/
theorem stageOwner_last (L w : ℕ) :
    stageOwner L w (Fin.last (stageCount L w)) = mainOwner L w := by
  rfl

/-- Both birth targets are actually held by `R_k` immediately before their
respective births. Source: Part II, `prop:sweep`, proof, lines 365–369. -/
theorem birth_targets_owned (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    (∀ x ∈ remainderBirthTarget L w k,
      (stageFrame L w k.castSucc).owner x = Sum.inl k.castSucc) ∧
    (∀ x ∈ blockBirthTarget L w k,
      (afterRemainderBirth L w k).owner x = Sum.inl k.castSucc) := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  constructor
  · intro x hx
    have hx' : (k.val + 1) * (20 * w) + w ≤ x.val ∧ x.val < L := by
      simpa only [remainderBirthTarget, mem_interval] using hx
    have hpre : ¬x.val < k.val * (20 * w) := by omega
    simp [stageFrame, stageOwner, hpre]
  · intro x hx
    have hx' : k.val * (20 * w) + w ≤ x.val ∧
        x.val < (k.val + 1) * (20 * w) := by
      simpa only [blockBirthTarget, mem_interval] using hx
    have hpre : ¬x.val < k.val * (20 * w) := by omega
    have hR : x ∉ remainderBirthTarget L w k := by
      simp only [remainderBirthTarget, mem_interval]
      omega
    simp [afterRemainderBirth, Sheet.changeOwner, stageFrame, stageOwner, hR, hpre]

/-- The environments are computed from the actual before-birth sheets, rather
than supplied as hypotheses. Source: Part II, `prop:sweep`, lines 365–369. -/
theorem birth_environments (k : Fin (stageCount L w)) :
    (stageFrame L w k.castSucc).birthEnv (.inl k.castSucc) =
        interval L 0 (k.val * (20 * w)) ∧
      (afterRemainderBirth L w k).birthEnv (.inl k.castSucc) =
        interval L 0 (k.val * (20 * w)) ∪ remainderBirthTarget L w k := by
  have hne : k.succ ≠ k.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  constructor
  · ext x
    by_cases hx : x.val < k.val * (20 * w)
    · simp [Sheet.mem_birthEnv, stageFrame, stageOwner, mem_interval, hx]
    · simp [Sheet.mem_birthEnv, stageFrame, stageOwner, mem_interval, hx]
  · ext x
    by_cases hx : x.val < k.val * (20 * w) <;>
      by_cases hR : x ∈ remainderBirthTarget L w k <;>
      simp [Sheet.mem_birthEnv, afterRemainderBirth, Sheet.changeOwner, stageFrame,
        stageOwner,
        mem_interval, hx, hR, hne]

/-- At a positive stage the completed block supplies the left flank of the
left band, while the new block supplies its right flank.
Source: Part II, `prop:sweep`, lines 370–374. -/
theorem left_band_owners (hw : 1 ≤ w) (k : Fin (stageCount L w)) (hk : 0 < k.val) :
    let a := k.val * (20 * w)
    (∀ x ∈ interval L (a - 8 * w) a,
      (afterBlockBirth L w k).owner x =
        Sum.inr ⟨k.val - 1, by omega⟩) ∧
      (∀ x ∈ interval L a (a + w),
        (afterBlockBirth L w k).owner x = Sum.inl k.castSucc) ∧
      (∀ x ∈ interval L (a + w) (a + 2 * w),
        (afterBlockBirth L w k).owner x = Sum.inr k) := by
  dsimp only
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  have hp : k.val - 1 + 1 = k.val := by omega
  have hpred := congrArg (fun n : ℕ ↦ n * (20 * w)) hp
  simp only [Nat.add_mul, Nat.one_mul] at hpred
  have hmargin : 8 * w ≤ k.val * (20 * w) := stage_left_margin w k.val (by omega)
  constructor
  · intro x hx
    have hx' : k.val * (20 * w) - 8 * w ≤ x.val ∧
        x.val < k.val * (20 * w) := by simpa only [mem_interval] using hx
    have hlo : (k.val - 1) * (20 * w) ≤ x.val := by omega
    have hhi : x.val < (k.val - 1 + 1) * (20 * w) := by simpa only [hp] using hx'.2
    have howner := stageOwner_at_block (L := L) hw k.castSucc
      (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)) x
      (by change k.val - 1 < k.val; omega) hlo hhi
    obtain ⟨hR, hB⟩ := unused_births_of_lt k x (by omega)
    simpa [afterBlockBirth, afterRemainderBirth, Sheet.changeOwner, stageFrame,
      hR, hB] using howner
  · constructor
    · intro x hx
      have hx' : k.val * (20 * w) ≤ x.val ∧
          x.val < k.val * (20 * w) + w := by simpa only [mem_interval] using hx
      have hpre : ¬x.val < k.val * (20 * w) := by omega
      obtain ⟨hR, hB⟩ := unused_births_of_lt k x (by omega)
      simp [afterBlockBirth, afterRemainderBirth, Sheet.changeOwner,
        stageFrame, stageOwner, hR, hB, hpre]
    · intro x hx
      have hx' : k.val * (20 * w) + w ≤ x.val ∧
          x.val < k.val * (20 * w) + 2 * w := by simpa only [mem_interval] using hx
      have hB : x ∈ blockBirthTarget L w k := by
        simp only [blockBirthTarget, mem_interval]
        omega
      simp [afterBlockBirth, Sheet.changeOwner, hB]

/-- The exceptional first left transfer is a direct death whose after-death
environment is the rest of the chain. Source: Part II, `prop:sweep`, lines 373–374. -/
theorem first_left_death_environment (k : Fin (stageCount L w))
    (hk : k.val = 0) :
    (afterLeftTransfer L w k).birthEnv (.inr k) = interval L (20 * w) L := by
  ext x
  have hP : (afterLeftTransfer L w k).owner x = Sum.inr k ↔
      x.val < 20 * w := by
    simp only [afterLeftTransfer, afterBlockBirth, afterRemainderBirth,
      Sheet.changeOwner, stageFrame, stageOwner, leftBandTarget,
      blockBirthTarget, remainderBirthTarget, mem_interval, Fin.val_castSucc, hk,
      zero_mul, zero_add, one_mul, Nat.not_lt_zero, dite_false]
    split_ifs <;> simp_all
    omega
  simp only [Sheet.mem_birthEnv, ne_eq, hP, mem_interval]
  have hxL := x.isLt
  omega

/-- After the left transfer the new completed block supplies the full left
flank of the right band. Source: Part II, `prop:sweep`, lines 374–376. -/
theorem right_band_owners (k : Fin (stageCount L w)) :
    let b := (k.val + 1) * (20 * w)
    (∀ x ∈ interval L (b - 8 * w) b,
      (afterLeftTransfer L w k).owner x = Sum.inr k) ∧
      (∀ x ∈ interval L b (b + w),
        (afterLeftTransfer L w k).owner x = Sum.inl k.castSucc) ∧
      (∀ x ∈ interval L (b + w) (b + 2 * w),
        (afterLeftTransfer L w k).owner x = Sum.inl k.succ) := by
  dsimp only
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  constructor
  · intro x hx
    have hx' : (k.val + 1) * (20 * w) - 8 * w ≤ x.val ∧
        x.val < (k.val + 1) * (20 * w) := by simpa only [mem_interval] using hx
    have hB : x ∈ blockBirthTarget L w k := by
      simp only [blockBirthTarget, mem_interval]
      omega
    have hleft : x ∉ leftBandTarget L w k := by
      simp only [leftBandTarget, mem_interval]
      omega
    simp [afterLeftTransfer, afterBlockBirth, Sheet.changeOwner, hleft, hB]
  · constructor
    · intro x hx
      have hx' : (k.val + 1) * (20 * w) ≤ x.val ∧
          x.val < (k.val + 1) * (20 * w) + w := by simpa only [mem_interval] using hx
      have hpre : ¬x.val < k.val * (20 * w) := by omega
      have hR : x ∉ remainderBirthTarget L w k := by
        simp only [remainderBirthTarget, mem_interval]
        omega
      obtain ⟨hB, hleft⟩ := passed_targets_of_le k x hx'.1
      simp [afterLeftTransfer, afterBlockBirth, afterRemainderBirth,
        Sheet.changeOwner, stageFrame, stageOwner, hpre, hR, hB, hleft]
    · intro x hx
      have hx' : (k.val + 1) * (20 * w) + w ≤ x.val ∧
          x.val < (k.val + 1) * (20 * w) + 2 * w := by simpa only [mem_interval] using hx
      have hR : x ∈ remainderBirthTarget L w k := by
        simp only [remainderBirthTarget, mem_interval]
        have hxL := x.isLt
        omega
      obtain ⟨hB, hleft⟩ := passed_targets_of_le k x (by omega)
      simp [afterLeftTransfer, afterBlockBirth, afterRemainderBirth,
        Sheet.changeOwner, hR, hB, hleft]

/-- The four specified owner changes give exactly the next stage, including
stage zero. No ownership recurrence is assumed.
Source: Part II, `prop:sweep`, lines 375–376. -/
theorem afterRightTransfer_eq_stageFrame (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    afterRightTransfer L w k = stageFrame L w k.succ := by
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  have howner : (afterRightTransfer L w k).owner = stageOwner L w k.succ := by
    funext x
    by_cases hx : x.val < k.val * (20 * w)
    · have hnext : x.val < (k.val + 1) * (20 * w) := by omega
      obtain ⟨hR, hB⟩ := unused_births_of_lt k x (by omega)
      have hleft : x ∉ leftBandTarget L w k := by
        simp only [leftBandTarget, mem_interval]
        omega
      have hright : x ∉ rightBandTarget L w k := by
        simp only [rightBandTarget, mem_interval]
        omega
      simp [afterRightTransfer, afterLeftTransfer, afterBlockBirth,
        afterRemainderBirth, Sheet.changeOwner, stageFrame, stageOwner,
        hR, hB, hleft, hright, hx, hnext]
    · by_cases hmid : x.val < (k.val + 1) * (20 * w)
      · have hnext : stageOwner L w k.succ x = Sum.inr k :=
          stageOwner_at_block hw k.succ k x (by simp) (by omega) hmid
        rw [hnext]
        have hR : x ∉ remainderBirthTarget L w k := by
          simp only [remainderBirthTarget, mem_interval]
          omega
        have hright : x ∉ rightBandTarget L w k := by
          simp only [rightBandTarget, mem_interval]
          omega
        by_cases hband : x.val < k.val * (20 * w) + w
        · have hleft : x ∈ leftBandTarget L w k := by
            simp only [leftBandTarget, mem_interval]
            omega
          simp [afterRightTransfer, afterLeftTransfer, Sheet.changeOwner, hright, hleft]
        · have hleft : x ∉ leftBandTarget L w k := by
            simp only [leftBandTarget, mem_interval]
            omega
          have hB : x ∈ blockBirthTarget L w k := by
            simp only [blockBirthTarget, mem_interval]
            omega
          simp [afterRightTransfer, afterLeftTransfer, afterBlockBirth,
            Sheet.changeOwner, hright, hleft, hB]
      · have hnext : stageOwner L w k.succ x = Sum.inl k.succ := by
          simp [stageOwner, hmid]
        rw [hnext]
        by_cases hband : x.val < (k.val + 1) * (20 * w) + w
        · have hright : x ∈ rightBandTarget L w k := by
            simp only [rightBandTarget, mem_interval]
            omega
          simp [afterRightTransfer, Sheet.changeOwner, hright]
        · have hR : x ∈ remainderBirthTarget L w k := by
            simp only [remainderBirthTarget, mem_interval]
            have hxL := x.isLt
            omega
          obtain ⟨hB, hleft⟩ := passed_targets_of_le k x (by omega)
          have hright : x ∉ rightBandTarget L w k := by
            simp only [rightBandTarget, mem_interval]
            omega
          simp [afterRightTransfer, afterLeftTransfer, afterBlockBirth,
            afterRemainderBirth, Sheet.changeOwner, hR, hB, hleft, hright]
  exact Sheet.ext howner

/-- The actual main sheet after the corrected left-band construction, except
that stage zero uses the prescribed direct death. The previous completed party
is introduced only in the positive-stage branch.
Source: Part II, `con:sweep`, move (3), lines 336–338. -/
def leftBandMain (L w : ℕ) (k : Fin (stageCount L w)) : Sheet (Fin L) (Party L w) :=
  if k.val = 0 then afterLeftTransfer L w k
  else OneBand.main₈ (afterBlockBirth L w k).owner
    (.inl k.castSucc) (.inr k)
    (.inr ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)
    (k.val * (20 * w)) w

/-- The actual main sheet after the corrected right-band construction, using
the main sheet produced by the left construction.
Source: Part II, `con:sweep`, move (4), lines 339–340. -/
def rightBandMain (L w : ℕ) (k : Fin (stageCount L w)) : Sheet (Fin L) (Party L w) :=
  OneBand.main₈ (leftBandMain L w k).owner
    (.inl k.castSucc) (.inl k.succ) (.inr k) ((k.val + 1) * (20 * w)) w

/-- The actual left-band sheet has the specified transfer endpoint. The band
margins and owner hypotheses are derived from the constructed stage.
Source: Part II, `prop:sweep`, lines 370–374. -/
theorem leftBandMain_eq_afterLeftTransfer (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    leftBandMain L w k = afterLeftTransfer L w k := by
  unfold leftBandMain
  split_ifs with hk
  · rfl
  · have hkpos : 0 < k.val := by omega
    have hC := (left_band_owners hw k hkpos).1
    have hleft : 8 * w ≤ k.val * (20 * w) := stage_left_margin w k.val (by omega)
    have he := OneBand.main₈_eq_changeOwner
      (afterBlockBirth L w k).owner
      (.inl k.castSucc) (.inr k)
      (.inr ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)
      (k.val * (20 * w)) w hw hleft hC
    simpa only [OneBand.main₀, afterLeftTransfer, leftBandTarget] using he

/-- The actual right-band sheet has the specified transfer endpoint. No final
ownership identity or band hypothesis is supplied as an additional premise.
Source: Part II, `prop:sweep`, lines 374–376. -/
theorem rightBandMain_eq_afterRightTransfer (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    rightBandMain L w k = afterRightTransfer L w k := by
  unfold rightBandMain
  rw [leftBandMain_eq_afterLeftTransfer hw k]
  have hC := (right_band_owners k).1
  have hleft : 8 * w ≤ (k.val + 1) * (20 * w) :=
    stage_left_margin w (k.val + 1) (by omega)
  have he := OneBand.main₈_eq_changeOwner
    (afterLeftTransfer L w k).owner
    (.inl k.castSucc) (.inl k.succ) (.inr k) ((k.val + 1) * (20 * w)) w
    hw hleft hC
  simpa only [OneBand.main₀, afterRightTransfer, rightBandTarget] using he

/-- The actual corrected band sheets complete the next main-sheet stage,
including the exceptional first stage. This is a sheet identity, not yet the
construction of its quantum circuit or information bounds.
Source: Part II, `prop:sweep`, lines 375–376. -/
theorem rightBandMain_eq_stageFrame (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    rightBandMain L w k = stageFrame L w k.succ := by
  rw [rightBandMain_eq_afterRightTransfer hw k, afterRightTransfer_eq_stageFrame hw k]

end TNLean.MPS.AreaLaw.ChainSweep
end

end

section

open scoped Matrix.Norms.L2Operator

open ManyBody (interval mem_interval ChainInteraction)

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open QuantumCircuit.Party

open ManyBody (IsGapped groundSpace)

variable {L w : ℕ}

/-- Exact separations for the two births and the exceptional first death.
The third environment is evaluated after that death.
Source: Part II, `prop:sweep`, proof, lines 365–374. -/
theorem birth_death_separation (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    (∀ x ∈ remainderBirthTarget L w k,
      ∀ y ∈ (stageFrame L w k.castSucc).birthEnv (.inl k.castSucc),
        w ≤ Nat.dist x.val y.val) ∧
      (∀ x ∈ blockBirthTarget L w k,
        ∀ y ∈ (afterRemainderBirth L w k).birthEnv (.inl k.castSucc),
          w ≤ Nat.dist x.val y.val) ∧
      (k.val = 0 → ∀ x ∈ leftBandTarget L w k,
        ∀ y ∈ (afterLeftTransfer L w k).birthEnv (.inr k),
          w ≤ Nat.dist x.val y.val) := by
  obtain ⟨hE₁, hE₂⟩ := birth_environments k
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hE₁] at hy
    simp only [remainderBirthTarget, mem_interval] at hx
    simp only [mem_interval] at hy
    have hdist := Nat.dist_tri_left' x.val y.val
    omega
  · intro x hx y hy
    rw [hE₂] at hy
    simp only [blockBirthTarget, mem_interval] at hx
    rcases Finset.mem_union.mp hy with hy | hy
    · simp only [mem_interval] at hy
      have hdist := Nat.dist_tri_left' x.val y.val
      omega
    · simp only [remainderBirthTarget, mem_interval] at hy
      have hdist := Nat.dist_tri_left x.val y.val
      omega
  · intro hk x hx y hy
    rw [first_left_death_environment k hk] at hy
    simp only [leftBandTarget, mem_interval, hk, zero_mul, zero_add] at hx
    simp only [mem_interval] at hy
    have hdist := Nat.dist_tri_left x.val y.val
    omega

/-- The original ground state's information bounds for the actual two birth
targets and first-stage death follow from physical logarithmic separation.
The constants precede every chain, state, width and stage.
Source: Part II, `lem:logsep`, lines 472–488, and Part II, `prop:sweep`,
proof, lines 365–374. -/
theorem birth_death_information_of_logarithmic_separation
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
        (ManyBody.regionMutualInformation Ω
          (remainderBirthTarget L w k)
          ((stageFrame L w k.castSucc).birthEnv (.inl k.castSucc)) ≤
            (L : ℝ) ^ (-24 : ℤ)) ∧
        (ManyBody.regionMutualInformation Ω
          (blockBirthTarget L w k)
          ((afterRemainderBirth L w k).birthEnv (.inl k.castSucc)) ≤
            (L : ℝ) ^ (-24 : ℤ)) ∧
        (k.val = 0 → ManyBody.regionMutualInformation Ω
          (leftBandTarget L w k)
          ((afterLeftTransfer L w k).birthEnv (.inr k)) ≤
            (L : ℝ) ^ (-24 : ℤ)) := by
  classical
  obtain ⟨D₂₄, L₀, hD, hL₀, hlogsep⟩ :=
    ManyBody.ChainInteraction.mutualInformation_le_of_logarithmic_separation
      q hq R J Δ hΔ 24 (by norm_num) 1 le_rfl
  refine ⟨D₂₄, L₀, hD, hL₀, ?_⟩
  intro L hL h hh hhJ Ω E₀ hΩ hgap hspan w hw hwidth k
  obtain ⟨hd₁, hd₂, hd₃⟩ := birth_death_separation hw k
  have hinterval (b c : ℕ) (E : Finset (Fin L))
      (hd : ∀ x ∈ interval L b c, ∀ y ∈ E, w ≤ Nat.dist x.val y.val) :
      ManyBody.regionMutualInformation Ω
        (interval L b c) E ≤ (L : ℝ) ^ (-24 : ℤ) := by
    have hT : ∃ (n : ℕ) (a z : Fin n → ℕ), n ≤ 1 ∧
        interval L b c = Finset.univ.biUnion (fun i ↦ interval L (a i) (z i)) :=
      ⟨1, fun _ ↦ b, fun _ ↦ c, le_rfl, by simp⟩
    have hi := hlogsep L hL h hh hhJ Ω E₀ hΩ hgap hspan (interval L b c) E hT
      (fun x hx y hy ↦ hwidth.trans (by exact_mod_cast hd x hx y hy))
    have hexponent : -(24 : ℝ) = ((-24 : ℤ) : ℝ) := by norm_num
    rw [hexponent, Real.rpow_intCast] at hi
    exact hi
  refine ⟨?_, ?_, ?_⟩
  · exact hinterval _ _ _ hd₁
  · exact hinterval _ _ _ hd₂
  · intro hk
    exact hinterval _ _ _ (hd₃ hk)

end TNLean.MPS.AreaLaw.ChainSweep
end

end
