/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepPlacement
import TNLean.MPS.AreaLaw.ProtocolTerminalWord
import TNLean.MPS.AreaLaw.ProtocolTerminalReference
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Conditional preparation from the actual local-stage circuits

The circuit is the chronological composite of the constructed private
initialization, the specified chronological middle,
and the actual terminal private word. The sole conditional construction input
is the local circuit family with the conclusion of the local-stage theorem.
The physical information estimates producing that family are not proved here.

Every nonprivate occurrence of the complete circuit retains the stage and
slot support of its middle occurrence. Its arity and the block distance
between its participants follow from that support. The two private ends
contribute no nonprivate occurrences.

The split-output coordinates are the existing terminal stack coordinates,
transported back through the actual terminal regrouping isometry. The physical
density uses the standard physical/private readout of the actual final layout;
its equality with the original main marginal is proved by the existing terminal
coordinate theorem. No terminal vector or density is supplied as a hypothesis.

Source: the one-dimensional note, Part II, Construction `con:sweep` and
Proposition `prop:sweep`, lines 330–384, and Theorem B with its routing
argument, lines 575–603.
This is a conditional intermediate result, not the full sweep proposition.

**Local fix (terminal auxiliary registers):** Only main registers form the
physical blocks. Every auxiliary copy-site label remains private at its actual
retired owner, including parties with scalar physical output. The auxiliary
reference is a product by original copy label, not by party. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice TNLean.Lattice.PartyCircuit TNLean.Lattice.Sheet ContinuousLinearMap

variable {L w q : ℕ}

/-- A private circuit contributes no lifetime participation.
Source: Part II, `prop:sweep`, lines 350–355. -/
private theorem participation_zero {P : Type} {a b : Layout P}
    (c : OriginalCircuit a b) (hc : c.nonprivateCount = 0) (p : P) :
    c.participationCount p = 0 := by
  let := OriginalCircuit.isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero c hc
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- The verified terminal word, with its source layout identified with the
actual terminal sheet stack. No operation is added by this equality transport.
Source: Part II, `prop:sweep`, lines 355–360. -/
private def finalRegroupingCircuit (L w : ℕ) :
    OriginalCircuit (stackRegs (Sheet.regs q) (terminalFrames L w) [])
      (familyPhysicalOutputLayout (physicalDimension L w q)
        (physicalOrder L w) (privateLayout L w q)) :=
  ((terminalRegroupingWord (q := q) (terminalRawOrder L w)
    (terminalRawOrder_nodup L w) mem_terminalRawOrder).toOriginalCircuit
      (terminalRegroupingWord_props (q := q) (terminalRawOrder L w)
        (terminalRawOrder_nodup L w) mem_terminalRawOrder).1).castLayouts
          (stackRegs_terminalFrames L w).symm rfl

private theorem finalRegroupingCircuit_nonprivateCount :
    (finalRegroupingCircuit (q := q) L w).nonprivateCount = 0 := by
  unfold finalRegroupingCircuit
  rw [OriginalCircuit.nonprivateCount_castLayouts, Word.nonprivateCount_toOriginalCircuit]
  exact (terminalRegroupingWord_props (q := q) (terminalRawOrder L w)
    (terminalRawOrder_nodup L w) mem_terminalRawOrder).2.2

private theorem eval_finalRegroupingCircuit
    (y : Mem (stackRegs (Sheet.regs q) (terminalFrames L w) [])) :
    (finalRegroupingCircuit L w).eval y =
      terminalRegrouping (q := q) (terminalRawOrder L w)
        (terminalRawOrder_nodup L w) mem_terminalRawOrder
          (Layout.memCongr (stackRegs_terminalFrames L w) y) := by
  unfold finalRegroupingCircuit
  obtain ⟨x, rfl⟩ :=
    (Layout.memCongr (stackRegs_terminalFrames L w).symm).surjective y
  rw [OriginalCircuit.eval_castLayouts_memCongr, Word.eval_toOriginalCircuit]
  simp only [Layout.memCongr_rfl, LinearIsometryEquiv.coe_refl, id_eq]
  have hcancel : Layout.memCongr (stackRegs_terminalFrames L w)
      (Layout.memCongr (stackRegs_terminalFrames L w).symm x) = x := by
    rw [Layout.memCongr_symm]
    exact LinearIsometryEquiv.apply_symm_apply _ x
  rw [hcancel]
  exact eval_terminalRegroupingWord (q := q) (terminalRawOrder L w)
    (terminalRawOrder_nodup L w) mem_terminalRawOrder x


variable (c : (k : Fin (stageCount L w)) → (j : Fin 18) → OriginalCircuit
  (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k j.val) [])
  (stackRegs (Sheet.regs q) (stageBoundaryFrames L w k (j.val + 1)) []))

variable (Ω : EuclideanSpace ℂ (Fin L → Fin q))

variable (hc : ∀ k j, (c k j).IsBoundedChange (stageParticipants k j) 1 1
    (4 * (L : ℝ) ^ (-12 : ℤ))
    (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val))
    (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))) ∧
  (c k j).IsSourceBounded 1 ∧ (c k j).nonprivateCount ≤ 1 ∧
  ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) → (c k j).nonprivateCount = 0 ∧
    ‖(c k j).eval (framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k j.val)) -
      framesVec (Sheet.refFamily Ω) (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
    HEq (c k j) (OriginalCircuit.id (stackRegs (Sheet.regs q)
      (stageBoundaryFrames L w k j.val) []))))

include hc

/-- Construct the private preparation, the actual chronological middle and
its private terminal regrouping from the specified local circuit family.
All resources and errors are conclusions. Auxiliary normalization is derived
from the original unit vector, with no product-by-party assumption. Every
nonprivate occurrence has derived stage/slot support, arity at most 40 and
participant block distance at most two.
Source: Part II, `con:sweep`, `prop:sweep`, and Theorem B with its routing
argument, lines 330–384 and 575–603. -/
theorem exists_preparation_of_local_circuits (hL : 0 < L) (hΩ : ‖Ω‖ = 1) :
    let Fs := initialFrames L w
    let holder : Sheet (Fin L) (Party L w) → Party L w := fun F ↦ F.owner ⟨0, hL⟩
    let H := fun p ↦ framesSpace (Sheet.regs q) (Fs.filter fun F ↦ holder F = p)
    let rs := terminalRawOrder L w
    let hn := terminalRawOrder_nodup L w
    let hr := mem_terminalRawOrder (L := L) (w := w)
    let R := terminalRegrouping (q := q) rs hn hr
    let hT := stackRegs_terminalFrames (q := q) L w
    let A : Mem (privateLayout L w q) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (AuxiliarySite L w → Fin q) :=
      groupIso (auxiliaryOwner L w) Finset.univ.toList
        (List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _) (by simp))
    letI := A.symm.toLinearEquiv.finiteDimensional
    ∃ hx : ∀ p, ‖framesVec (Sheet.refFamily Ω) (Fs.filter fun F ↦ holder F = p)‖ = 1,
      ∃ C : OriginalCircuit (ProductInput.wholePartyLayout H)
          (familyPhysicalOutputLayout (physicalDimension L w q)
            (physicalOrder L w) (privateLayout L w q)),
        let X := ProductInput.ofAllParties H
          (fun p ↦ framesVec (Sheet.refFamily Ω) (Fs.filter fun F ↦ holder F = p)) hx
        let Ψ := C.eval X.vector
        let V := familyLabelledPhysicalReadout (physicalDimension L w q)
          (physicalOrder L w) (Finset.nodup_toList _) (by simp [physicalOrder])
          (privateLayout L w q) Ψ
        let Ψraw := (Layout.memCongr hT).symm (R.symm Ψ)
        let ε := (sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ))
        (∀ p, C.participationCount p ≤ 40) ∧
          C.nonprivateCount ≤ sweepOperationCount L w ∧
          C.IsSourceBounded 1 ∧ C.IsExpansionBounded 1 1 ∧ C.IsMonomialBounded 1 ∧
          ‖Ψ‖ ≤ 1 ∧ ‖auxiliaryReference L w q Ω‖ = 1 ∧
          ‖terminalStackReadout L w Ψraw -
            Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤ ε ∧
          Matrix.rectangularTraceNorm
            (Matrix.partialTraceRight (Matrix.euclideanOuterProduct V V) -
              Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
                (Matrix.euclideanOuterProduct Ω Ω)) ≤ 2 * ε ∧
          (∀ g : C.nonprivateLocations,
            ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
              (↑(C.participants g) : Set (Party L w)) ⊆ stageParticipants k j) ∧
          (∀ g : C.nonprivateLocations, (C.participants g).card ≤ 40) ∧
          (∀ (g : C.nonprivateLocations) (p t : Party L w),
            p ∈ C.participants g → t ∈ C.participants g →
              Nat.dist (partyLevel p) (partyLevel t) ≤ 2) := by
  classical
  let Fs := initialFrames L w
  let holder : Sheet (Fin L) (Party L w) → Party L w := fun F ↦ F.owner ⟨0, hL⟩
  let H := fun p ↦ framesSpace (Sheet.regs q) (Fs.filter fun F ↦ holder F = p)
  let rs := terminalRawOrder L w
  let hn := terminalRawOrder_nodup L w
  let hr := mem_terminalRawOrder (L := L) (w := w)
  let R := terminalRegrouping (q := q) rs hn hr
  let hT := stackRegs_terminalFrames (q := q) L w
  let A : Mem (privateLayout L w q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (AuxiliarySite L w → Fin q) :=
    groupIso (auxiliaryOwner L w) Finset.univ.toList
      (List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _) (by simp))
  let := A.symm.toLinearEquiv.finiteDimensional
  obtain ⟨hx, c₀, h₀count, _, h₀exp, h₀mono, h₀eval⟩ :=
    exists_initialization (w := w) (q := q) hL hΩ
  let X := ProductInput.ofAllParties H
    (fun p ↦ framesVec (Sheet.refFamily Ω) (Fs.filter fun F ↦ holder F = p)) hx
  let M := sweepMiddleCircuit c
  let Q := finalRegroupingCircuit (q := q) L w
  let C := (c₀.comp M).comp Q
  let y := M.eval (framesVec (Sheet.refFamily Ω) Fs)
  let Ψ := C.eval X.vector
  let V := familyLabelledPhysicalReadout (physicalDimension L w q)
    (physicalOrder L w) (Finset.nodup_toList _) (by simp [physicalOrder])
    (privateLayout L w q) Ψ
  let ε := (sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ))
  have hQ : Q.nonprivateCount = 0 := finalRegroupingCircuit_nonprivateCount
  have hM := sweepMiddleCircuit_norm_and_error c Ω hc hΩ
  have hMres := sweepMiddleCircuit_resource_bounds c Ω hc
  have hΨ : Ψ = R (Layout.memCongr hT y) := by
    change Q.eval (M.eval (c₀.eval X.vector)) = _
    rw [h₀eval]
    exact eval_finalRegroupingCircuit _
  have hback : (Layout.memCongr hT).symm (R.symm Ψ) = y := by
    rw [hΨ, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply]
  have hpart (p : Party L w) : C.participationCount p ≤ 40 := by
    change ((c₀.comp M).comp Q).participationCount p ≤ 40
    rw [OriginalCircuit.participationCount_comp, OriginalCircuit.participationCount_comp,
      participation_zero c₀ h₀count p, participation_zero Q hQ p, zero_add, add_zero]
    exact sweepMiddleCircuit_participation_le_forty c Ω hc p
  have hcount : C.nonprivateCount ≤ sweepOperationCount L w := by
    change c₀.nonprivateCount + M.nonprivateCount + Q.nonprivateCount ≤ _
    rw [h₀count, hQ, zero_add, add_zero]
    exact sweepMiddleCircuit_nonprivateCount_le c Ω hc
  have hsupport : ∀ g : C.nonprivateLocations,
      ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
        (↑(C.participants g) : Set (Party L w)) ⊆ stageParticipants k j := by
    rintro ((g | g) | g)
    · exact ((OriginalCircuit.isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero
        c₀ h₀count).false g).elim
    · exact sweepMiddleCircuit_participants_subset_stage c Ω hc g
    · exact ((OriginalCircuit.isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero
        Q hQ).false g).elim
  have harity (g : C.nonprivateLocations) : (C.participants g).card ≤ 40 := by
    obtain ⟨k, j, hsub⟩ := hsupport g
    exact (card_le_eight_of_subset_stageParticipants _ k j hsub).trans (by norm_num)
  have hlocality (g : C.nonprivateLocations) (p t : Party L w)
      (hp : p ∈ C.participants g) (ht : t ∈ C.participants g) :
      Nat.dist (partyLevel p) (partyLevel t) ≤ 2 := by
    obtain ⟨k, j, hsub⟩ := hsupport g
    exact stageParticipants_level_dist_le_two k j p t (hsub hp) (hsub ht)
  have hsource : C.IsSourceBounded 1 :=
    ⟨⟨OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero h₀count 1,
      hMres.1⟩, OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero hQ 1⟩
  have hexp : C.IsExpansionBounded 1 1 :=
    ⟨⟨h₀exp 1 1, hMres.2.1⟩,
      OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero 1 1 Q hQ⟩
  have hmono : C.IsMonomialBounded 1 :=
    ⟨⟨h₀mono 1, hMres.2.2⟩,
      OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero 1 Q hQ⟩
  have hnorm : ‖Ψ‖ ≤ 1 := (C.norm_eval_le_norm X.vector).trans X.norm_vector.le
  have hsplit :
      ‖terminalStackReadout L w
          ((Layout.memCongr hT).symm (R.symm Ψ)) -
        Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤ ε := by
    rw [hback, ← terminalStackReadout_framesVec Ω,
      ← map_sub, LinearIsometryEquiv.norm_map]
    exact hM.2
  have hρ : Matrix.partialTraceRight (Matrix.euclideanOuterProduct V V) =
      Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
        (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
          (terminalStackReadout L w y) (terminalStackReadout L w y))) := by
    dsimp only [V]
    rw [hΨ]
    exact physicalDensity_terminalRegrouping rs hn hr (Layout.memCongr hT y)
  have hdensity : Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct V V) -
        Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
          (Matrix.euclideanOuterProduct Ω Ω)) ≤ 2 * ε := by
    rw [hρ]
    change Matrix.rectangularTraceNorm
      (Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
        (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
          (terminalStackReadout L w y) (terminalStackReadout L w y)) -
            Matrix.euclideanOuterProduct Ω Ω)) ≤ 2 * ε
    rw [Matrix.rectangularTraceNorm_reindex]
    exact rectangularTraceNorm_terminalStackReadout_sub_le Ω hΩ y hM.1 hM.2
  exact ⟨hx, C, hpart, hcount, hsource, hexp, hmono, hnorm,
    norm_auxiliaryReference Ω hΩ, hsplit, hdensity, hsupport, harity, hlocality⟩

end TNLean.MPS.AreaLaw.ChainSweep
