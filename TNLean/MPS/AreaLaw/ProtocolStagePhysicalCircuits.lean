/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolStageInformation
import TNLean.MPS.AreaLaw.BandInformation
import TNLean.MPS.AreaLaw.ProtocolSweepLocalCircuits

/-!
# Physical local circuits for the chain sweep

A uniform logarithmic width supplies every primitive information estimate
needed by the existing eighteen-operation stage construction. The two
information constants and length cutoffs are enlarged before the chain,
Hamiltonian, ground state, position map, width and stage are introduced.
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

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.PairEffect TNLean.PEPS.EncodedFrame

/-- The physical assumptions imply the actual eighteen local circuits at
every stage, including the seven identity operations after the first direct
death. The constants precede all chain and state data. Neither information
bounds nor owner, circuit, endpoint or norm conclusions are assumed.
Source: Part II, `prop:sweep`, construction and geometric proof, lines 365–378,
using Part II, `lem:logsep`, lines 472–488. -/
theorem local_stage_circuits_of_logarithmic_separation
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    letI : NeZero q := ⟨by omega⟩
    ∃ (D₂₄ : ℝ) (L₀ : ℕ), 0 < D₂₄ ∧ 1 ≤ L₀ ∧
      ∀ (L : ℕ), L₀ ≤ L →
      ∀ (h : ChainHamiltonian L q R J)
        (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
        Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      ∀ (pos : Fin L → ℝ × ℝ) (w : ℕ), 1 ≤ w →
        D₂₄ * Real.log (L : ℝ) ≤ (w : ℝ) →
      ∀ k : Fin (stageCount L w),
        ∃ c : (j : Fin 18) → OriginalCircuit
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
  let : NeZero q := ⟨by omega⟩
  obtain ⟨Dstage, Nstage, hDstage, hNstage, hstage⟩ :=
    birth_death_information_of_logarithmic_separation q hq R J Δ hΔ
  obtain ⟨Dband, Nband, _, _, hband⟩ :=
    OneBand.primitive_information_of_logarithmic_separation q hq R J Δ hΔ
  refine ⟨max Dstage Dband, max Nstage Nband,
    hDstage.trans_le (le_max_left _ _), hNstage.trans (le_max_left _ _), ?_⟩
  intro L hL h Ω E₀ hgs pos w hw hwidth k
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
  have hmargin := stage_right_margin L w hgeometry k
  obtain ⟨hRem, hBlock, hBoundary⟩ :=
    hstage L hLs h Ω E₀ hgs pos w hw hwidthStage k
  have hleftOwners := left_band_owners (q := q) hw k
  have hleft (hk : 0 < k.val) :=
    hband L hLb h Ω E₀ hgs (Party L w) pos
      (afterBlockBirth L w k).owner
      (Sum.inl k.castSucc) (Sum.inr k)
      (Sum.inr (⟨k.val - 1, by omega⟩ : Fin (stageCount L w)))
      (k.val * (20 * w)) w (by simp)
      (by
        intro he
        have hv := congrArg Fin.val (Sum.inr.inj he)
        change k.val = k.val - 1 at hv
        omega)
      hw (stage_left_margin w k.val (by omega)) (by nlinarith [hmargin])
      (hleftOwners hk).1 (hleftOwners hk).2.1 (hleftOwners hk).2.2 hwidthBand
  have hrightOwners := right_band_owners (q := q) hw k
  rw [← leftBandMain_eq_afterLeftTransfer (q := q) hw hgeometry k]
    at hrightOwners
  have hright :=
    hband L hLb h Ω E₀ hgs (Party L w) pos
      (leftBandMain L w k).owner
      (Sum.inl k.castSucc) (Sum.inl k.succ) (Sum.inr k)
      ((k.val + 1) * (20 * w)) w (by simp) (by simp)
      hw (stage_left_margin w (k.val + 1) (by omega)) (by nlinarith [hmargin])
      hrightOwners.1 hrightOwners.2.1 hrightOwners.2.2 hwidthBand
  exact local_stage_circuits_of_primitive_information (q := q)
    hw hgeometry k Ω hgs.1 hRem hBlock hBoundary
    (fun hk ↦ (hleft hk).1) (fun hk ↦ (hleft hk).2.1)
    (fun hk ↦ (hleft hk).2.2.1) (fun hk ↦ (hleft hk).2.2.2.1)
    (fun hk ↦ (hleft hk).2.2.2.2.1) (fun hk ↦ (hleft hk).2.2.2.2.2.1)
    (fun hk ↦ (hleft hk).2.2.2.2.2.2.1) (fun hk ↦ (hleft hk).2.2.2.2.2.2.2)
    hright.1 hright.2.1 hright.2.2.1 hright.2.2.2.1
    hright.2.2.2.2.1 hright.2.2.2.2.2.1 hright.2.2.2.2.2.2.1 hright.2.2.2.2.2.2.2

end TNLean.MPS.AreaLaw.ChainSweep
