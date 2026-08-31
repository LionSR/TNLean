/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTChannelComposition
import TNLean.MPS.MPDO.CPSVBlockingChannelEmbeddedCounterexample
import TNLean.MPS.MPDO.NeighboringTraceObstructionAmbientCounterexample

/-!
# A simple-biCF counterexample to the CPSV16 blocking channels

The five-letter ambient tensor of
`NeighboringTraceObstructionAmbientCounterexample` satisfies the complete
simple-biCF, MPDO, saturation-of-the-area-law, literal-zero-correlation-length,
and normalization hypotheses of CPSV16, Appendix C.2.  Its first virtual
sector is the physical embedding of the four-letter trace-norm obstruction.
One virtual boundary isolates that sector at every chain length.

It follows that the two-to-three-site channel asserted by CPSV16 Proposition
`prop2to5` does not exist.  The same argument from two to four sites shows that
the two-site blocking is not a renormalization fixed point in the sense of
CPSV16 Definition 4.1.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor.CPSVBlockingChannelCounterexample

open NeighboringTraceObstructionAmbientBlocks
open NeighboringTraceObstructionAmbientCounterexample

/-- No trace-preserving completely positive map sends every two-site closure
of the ambient tensor to the corresponding three-site closure.

The same ambient boundary is used at lengths two and three.  Thus this is a
universal obstruction to the refinement map asserted by CPSV16, Appendix C.2,
Proposition `prop2to5`, lines 1628--1665 and 1810--1817. -/
theorem not_exists_ambient_two_to_three_site_map
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    ¬ ∃ T : Matrix (Fin 2 → Fin 5) (Fin 2 → Fin 5) ℂ →ₗ[ℂ]
        Matrix (Fin 3 → Fin 5) (Fin 3 → Fin 5) ℂ,
      IsKrausCPTP T ∧
      ∀ Y : Matrix (Fin 3) (Fin 3) ℂ,
        T (physCloseN (ambient mu B hmu) 2 Y) =
          physCloseN (ambient mu B hmu) 3 Y := by
  rintro ⟨T, hT, hclose⟩
  apply not_exists_embedded_two_to_three_site_map
  refine ⟨T, hT, fun X ↦ ?_⟩
  obtain ⟨Y, hY⟩ :=
    exists_ambient_boundary_physCloseN_eq_embeddedObstruction
      mu B hmu hGauge X
  rw [← hY 2, ← hY 3]
  exact hclose Y

/-- No trace-preserving completely positive map sends every two-site closure
of the ambient tensor to the corresponding four-site closure.

This is the twice-applied refinement obstruction used in the logical
implication `(ii) ⇒ (v)` of CPSV16, Theorem 4.9.  Its closing proof prints the
cyclic label `(iii) ⇒ (v)` at lines 1821--1825. -/
theorem not_exists_ambient_two_to_four_site_map
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    ¬ ∃ T : Matrix (Fin 2 → Fin 5) (Fin 2 → Fin 5) ℂ →ₗ[ℂ]
        Matrix (Fin 4 → Fin 5) (Fin 4 → Fin 5) ℂ,
      IsKrausCPTP T ∧
      ∀ Y : Matrix (Fin 3) (Fin 3) ℂ,
        T (physCloseN (ambient mu B hmu) 2 Y) =
          physCloseN (ambient mu B hmu) 4 Y := by
  rintro ⟨T, hT, hclose⟩
  apply not_exists_embedded_two_to_four_site_map
  refine ⟨T, hT, fun X ↦ ?_⟩
  obtain ⟨Y, hY⟩ :=
    exists_ambient_boundary_physCloseN_eq_embeddedObstruction
      mu B hmu hGauge X
  rw [← hY 2, ← hY 4]
  exact hclose Y

/-- The two-site blocking of the ambient tensor is not a renormalization fixed
point in the trace-preserving completely positive map sense of CPSV16,
Definition 4.1.

Indeed, its refinement map would transport through the canonical blocked
coordinates to a two-to-four-site map for the unblocked tensor, contradicting
the preceding theorem.  This is the conclusion used in CPSV16, Theorem 4.9,
lines 851--893 and 1821--1825. -/
theorem ambient_blockTwo_not_isRFPViaTS
    (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0)
    (hGauge : MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B)) :
    ¬ IsRFPViaTS (blockTwo (ambient mu B hmu)) := by
  intro hRFP
  obtain ⟨_S, T, _hS, hT, _hSclose, hTclose⟩ := hRFP
  apply not_exists_ambient_two_to_four_site_map mu B hmu hGauge
  refine ⟨refinementMapInChainCoordinates T,
    refinementMapInChainCoordinates_isKrausCPTP hT, fun X ↦ ?_⟩
  exact refinementMapInChainCoordinates_physCloseN
    (ambient mu B hmu) T hTclose X

/-- **False source result:** CPSV16 Proposition `prop2to5` is false under its
complete standing hypotheses, and the same witness refutes the blocked
renormalization-fixed-point conclusion in the logical implication
`(ii) ⇒ (v)` of Theorem 4.9.

The witness is a five-letter tensor in simple block-injective canonical form.
It generates positive semidefinite periodic operators with positive trace,
saturates the area law, has literally idempotent physical-trace transfer, and
has the paper's global unit-weight normalization.  Both BNT representatives
are normal and their simultaneous one-letter word span is full.  Nevertheless,
there is no trace-preserving completely positive map carrying every two-site
closure to its three-site closure, nor one carrying every two-site closure to
its four-site closure.  Consequently the two-site blocking is not an
`IsRFPViaTS` fixed point.

Source: CPSV16, Theorem 4.9, lines 851--893, and Appendix C.2, standing
hypotheses and common-weight absorption at lines 1628--1665, Proposition
`prop2to5` at lines 1810--1817, and the twice-applied closing step at lines
1821--1825.  The false source statement and the explicit trace-norm
calculation are documented in
`docs/paper-gaps/cpsv16_prop_c15_blocking_channel_false.tex`. -/
theorem printed_propositionC15_and_theorem49_ii_to_v_are_false :
    ∃ (mu : ℂ) (B : MPSTensor (5 * 5) 2) (hmu : mu ≠ 0),
      0 < ‖mu‖ ∧ ‖mu‖ < 1 ∧
      Kraus.IsInjective B ∧
      MPSTensor.IsLeftCanonical B ∧
      MPSTensor.IsNormalTensor B ∧
      MPSTensor.GaugeEquiv embeddedObstruction.toMPSTensor (mu • B) ∧
      let S := sectors mu B hmu
      let K := ambient mu B hmu
      (IsMPDO K ∧
        (∀ N, 0 < N → 0 < Matrix.trace (mpo K N)) ∧
        IsSAL K ∧
        IsSimpleCanonicalForm K ∧
        IsSimple K ∧
        MPSTensor.IsBNTCanonicalForm S ∧
        MPSTensor.WordTupleSpanTop S.basis 1 ∧
        (∀ j, MPSTensor.IsNormalTensor (S.basis j)) ∧
        K.toMPSTensor = S.toTensor ∧
        (∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
          S.weight j q = S.weight j q') ∧
        S.basisCount = 2 ∧
        S.copies 0 = 1 ∧
        S.copies (Fin.succ 0) = 1 ∧
        S.basisDim 0 = 2 ∧
        S.basisDim (Fin.succ 0) = 1 ∧
        S.basis 0 = B ∧
        S.basis (Fin.succ 0) = terminalBlock.toMPSTensor ∧
        S.weight 0 0 = mu ∧
        S.weight (Fin.succ 0) 0 = 1 ∧
        physicalSupportProj embeddedObstruction = obstructionPhysicalSupport ∧
        physicalSupportProj terminalBlock = terminalPhysicalSupport ∧
        obstructionPhysicalSupport * terminalPhysicalSupport = 0 ∧
        terminalPhysicalSupport * obstructionPhysicalSupport = 0 ∧
        obstructionPhysicalSupport + terminalPhysicalSupport = 1 ∧
        physTraceTransfer K * physTraceTransfer K = physTraceTransfer K) ∧
      (¬ ∃ T : Matrix (Fin 2 → Fin 5) (Fin 2 → Fin 5) ℂ →ₗ[ℂ]
          Matrix (Fin 3 → Fin 5) (Fin 3 → Fin 5) ℂ,
        IsKrausCPTP T ∧
        ∀ Y : Matrix (Fin 3) (Fin 3) ℂ,
          T (physCloseN K 2 Y) = physCloseN K 3 Y) ∧
      (¬ ∃ T : Matrix (Fin 2 → Fin 5) (Fin 2 → Fin 5) ℂ →ₗ[ℂ]
          Matrix (Fin 4 → Fin 5) (Fin 4 → Fin 5) ℂ,
        IsKrausCPTP T ∧
        ∀ Y : Matrix (Fin 3) (Fin 3) ℂ,
          T (physCloseN K 2 Y) = physCloseN K 4 Y) ∧
      ¬ IsRFPViaTS (blockTwo K) := by
  obtain ⟨mu, B, hmu, hmuNormPos, hmuNorm, hBInj, hBLeft, hBNormal,
    hGauge, hStanding⟩ :=
    exists_ambient_simpleBiCF_neighboringTraceObstruction
  refine ⟨mu, B, hmu, hmuNormPos, hmuNorm, hBInj, hBLeft, hBNormal,
    hGauge, ?_⟩
  dsimp only at hStanding ⊢
  exact ⟨hStanding,
    not_exists_ambient_two_to_three_site_map mu B hmu hGauge,
    not_exists_ambient_two_to_four_site_map mu B hmu hGauge,
    ambient_blockTwo_not_isRFPViaTS mu B hmu hGauge⟩

end MPOTensor.CPSVBlockingChannelCounterexample
