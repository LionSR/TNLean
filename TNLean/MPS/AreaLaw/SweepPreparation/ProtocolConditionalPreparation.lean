/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepPlacement
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolTerminalWord
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra

/-!
# Conditional preparation from the actual local-stage circuits

The initial copies form a product of unit vectors across the parties, the
constructed private initialization. The circuit is the chronological composite of
the specified chronological middle and the actual terminal private regrouping.
The sole conditional construction input is the local circuit family with the
conclusion of the local-stage theorem.
The physical information estimates producing that family are not proved here.

Every nonprivate occurrence of the complete circuit retains the stage and
slot support of its middle occurrence. Its arity and the block distance
between its participants follow from that support. The private end
contributes no nonprivate occurrences.

The split-output coordinates are the existing terminal stack coordinates,
transported back through the actual terminal regrouping isometry. The physical
density uses the standard physical/private readout of the actual final system;
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

open Matrix QuantumCircuit QuantumCircuit.Party
open ManyBody (Config)

variable {L w q : ℕ}

variable (c : (k : Fin (stageCount L w)) → (j : Fin 18) → OriginalCircuit
  (stackSystem (Sheet.system q) (stageBoundaryFrames L w k j.val) fun _ ↦ Unit)
  (stackSystem (Sheet.system q) (stageBoundaryFrames L w k (j.val + 1)) fun _ ↦ Unit))

variable (Ω : EuclideanSpace ℂ (Fin L → Fin q))

variable (hc : ∀ k j, (c k j).IsBoundedChange (stageParticipants k j) 1 1
    (4 * (L : ℝ) ^ (-12 : ℤ))
    (framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k j.val))
    (framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k (j.val + 1))) ∧
  (c k j).IsSourceBounded 1 ∧ (c k j).nonprivateCount ≤ 1 ∧
  ((k.val = 0 ∧ 3 ≤ j.val ∧ j.val < 10) → (c k j).nonprivateCount = 0 ∧
    ‖toEuclideanLin (c k j).op
        (framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k j.val)) -
      framesVec (fun S ↦ S.refVec Ω) (stageBoundaryFrames L w k (j.val + 1))‖ = 0 ∧
    (c k j).toPartyCircuit.IsLocal))

include hc

/-- Construct the private preparation, the actual chronological middle and
its private terminal regrouping from the specified local circuit family.
The initial copies are a product of unit vectors across the parties.
All resources and errors are conclusions. Auxiliary normalization is derived
from the original unit vector, with no product-by-party assumption. Every
nonprivate occurrence has derived stage/slot support, arity at most 40 and
participant block distance at most two.
Source: Part II, `con:sweep`, `prop:sweep`, and Theorem B with its routing
argument, lines 330–384 and 575–603. -/
theorem exists_preparation_of_local_circuits (hL : 0 < L) (hΩ : ‖Ω‖ = 1) :
    ∃ φ : ∀ p, EuclideanSpace ℂ
        (stackSystem (Sheet.system q) (initialFrames L w) (fun _ ↦ Unit) p),
      (∀ p, ‖φ p‖ = 1) ∧
      (WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x) :
        EuclideanSpace ℂ (Config (stackSystem (Sheet.system q) (initialFrames L w)
          fun _ ↦ Unit))) = framesVec (fun S ↦ S.refVec Ω) (initialFrames L w) ∧
      ∃ C : OriginalCircuit (stackSystem (Sheet.system q) (initialFrames L w) fun _ ↦ Unit)
          (physicalSystem (physicalDimension L w q) (privateSystem L w q)),
        let Ψ := toEuclideanLin C.op (WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x))
        let V := toEuclideanLin
          (physicalReadout (physicalDimension L w q) (privateSystem L w q)) Ψ
        let Ψraw := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.piCongrRight (terminalPartyEquiv L w q))).symm
            ((terminalRegrouping L w q).symm Ψ)
        let ε := (sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ))
        (∀ p, C.participation p ≤ 40) ∧
          C.nonprivateCount ≤ sweepOperationCount L w ∧
          C.IsSourceBounded 1 ∧ C.IsExpansionBounded 1 1 ∧ C.IsMonomialBounded 1 ∧
          ‖Ψ‖ ≤ 1 ∧ ‖auxiliaryReference L w q Ω‖ = 1 ∧
          ‖terminalStackReadout L w Ψraw -
            euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤ ε ∧
          rectangularTraceNorm
            (partialTraceRight (euclideanOuterProduct V V) -
              reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
                (euclideanOuterProduct Ω Ω)) ≤ 2 * ε ∧
          (∀ g : C.nonprivateLocations,
            ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
              (↑(C.participants g) : Set (Party L w)) ⊆ stageParticipants k j) ∧
          (∀ g : C.nonprivateLocations, (C.participants g).card ≤ 40) ∧
          (∀ (g : C.nonprivateLocations) (p t : Party L w),
            p ∈ C.participants g → t ∈ C.participants g →
              Nat.dist (partyLevel p) (partyLevel t) ≤ 2) := by
  classical
  obtain ⟨φ, hφ, hφv⟩ := exists_initialization (w := w) (q := q) hL hΩ
  let M := sweepMiddleCircuit c
  let Q := terminalRegroupingCircuit L w q
  let C := M.comp Q
  let x : EuclideanSpace ℂ (Config (stackSystem (Sheet.system q) (initialFrames L w)
    fun _ ↦ Unit)) := WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x)
  let y := toEuclideanLin M.op (framesVec (fun S ↦ S.refVec Ω) (initialFrames L w))
  let Ψ := toEuclideanLin C.op x
  let V := toEuclideanLin (physicalReadout (physicalDimension L w q) (privateSystem L w q)) Ψ
  let T := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.piCongrRight (terminalPartyEquiv L w q))
  let ε := (sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ))
  have hx : x = framesVec (fun S ↦ S.refVec Ω) (initialFrames L w) := hφv
  have hQ : Q.nonprivateCount = 0 := nonprivateCount_terminalRegroupingCircuit
  have hM := sweepMiddleCircuit_norm_and_error c Ω hc hΩ
  have hMres := sweepMiddleCircuit_resource_bounds c Ω hc
  have hΨ : Ψ = terminalRegrouping L w q (T y) := by
    simp only [Ψ, C, OriginalCircuit.op_comp, Matrix.toEuclideanLin_mul_apply, hx]
    exact toEuclideanLin_op_terminalRegroupingCircuit _
  have hback : T.symm ((terminalRegrouping L w q).symm Ψ) = y := by
    rw [hΨ, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  have hpart (p : Party L w) : C.participation p ≤ 40 := by
    have hQp : Q.participation p = 0 := OriginalCircuit.participation_relabel _ p
    rw [OriginalCircuit.participation_comp, hQp, add_zero]
    exact sweepMiddleCircuit_participation_le_forty c Ω hc p
  have hcount : C.nonprivateCount ≤ sweepOperationCount L w := by
    rw [OriginalCircuit.nonprivateCount_comp, hQ, add_zero]
    exact sweepMiddleCircuit_nonprivateCount_le c Ω hc
  have hsupport : ∀ g : C.nonprivateLocations,
      ∃ k : Fin (stageCount L w), ∃ j : Fin 18,
        (↑(C.participants g) : Set (Party L w)) ⊆ stageParticipants k j := by
    rintro (g | g)
    · exact sweepMiddleCircuit_participants_subset_stage c Ω hc g
    · exact ((OriginalCircuit.isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero
        hQ).false g).elim
  have harity (g : C.nonprivateLocations) : (C.participants g).card ≤ 40 := by
    obtain ⟨k, j, hsub⟩ := hsupport g
    exact (card_le_eight_of_subset_stageParticipants _ k j hsub).trans (by norm_num)
  have hlocality (g : C.nonprivateLocations) (p t : Party L w)
      (hp : p ∈ C.participants g) (ht : t ∈ C.participants g) :
      Nat.dist (partyLevel p) (partyLevel t) ≤ 2 := by
    obtain ⟨k, j, hsub⟩ := hsupport g
    exact stageParticipants_level_dist_le_two k j p t (hsub hp) (hsub ht)
  have hsource : C.IsSourceBounded 1 :=
    (OriginalCircuit.isSourceBounded_comp _ _ _).mpr
      ⟨hMres.1, OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero hQ 1⟩
  have hexp : C.IsExpansionBounded 1 1 :=
    (OriginalCircuit.isExpansionBounded_comp _ _ _ _).mpr
      ⟨hMres.2.1, OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero hQ 1 1⟩
  have hmono : C.IsMonomialBounded 1 :=
    (OriginalCircuit.isMonomialBounded_comp _ _ _).mpr
      ⟨hMres.2.2, OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero hQ 1⟩
  have hnorm : ‖Ψ‖ ≤ 1 :=
    (C.norm_toEuclideanLin_op_le x).trans (norm_toLp_productVector_eq_one φ hφ).le
  have hsplit : ‖terminalStackReadout L w (T.symm ((terminalRegrouping L w q).symm Ψ)) -
      euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤ ε := by
    rw [hback, ← terminalStackReadout_framesVec Ω, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hM.2
  have hρ : partialTraceRight (euclideanOuterProduct V V) =
      reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
        (partialTraceRight (euclideanOuterProduct
          (terminalStackReadout L w y) (terminalStackReadout L w y))) := by
    simp only [V]
    rw [hΨ]
    exact physicalDensity_terminalRegrouping (T y)
  have hdensity : rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct V V) -
        reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
          (euclideanOuterProduct Ω Ω)) ≤ 2 * ε := by
    have hsub : reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
          (partialTraceRight (euclideanOuterProduct
            (terminalStackReadout L w y) (terminalStackReadout L w y))) -
          reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
            (euclideanOuterProduct Ω Ω) =
        reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
          (partialTraceRight (euclideanOuterProduct
            (terminalStackReadout L w y) (terminalStackReadout L w y)) -
              euclideanOuterProduct Ω Ω) := by
      ext i j
      simp [reindex_apply]
    rw [hρ, hsub, Matrix.rectangularTraceNorm_reindex]
    exact rectangularTraceNorm_terminalStackReadout_sub_le Ω hΩ y hM.1 hM.2
  exact ⟨φ, hφ, hφv, C, hpart, hcount, hsource, hexp, hmono, hnorm,
    norm_auxiliaryReference Ω hΩ, hsplit, hdensity, hsupport, harity, hlocality⟩

end TNLean.MPS.AreaLaw.ChainSweep
