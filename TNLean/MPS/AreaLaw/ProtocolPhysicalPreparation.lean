/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolStagePhysicalCircuits
import TNLean.MPS.AreaLaw.ProtocolConditionalPreparation
import TNLean.MPS.AreaLaw.ProtocolStageArity
import TNLean.MPS.AreaLaw.ProtocolSweepGeometry
import TNLean.Algebra.ExplicitThresholds

/-!
# Physical preparation by a logarithmic-width chain sweep

The width constant, polynomial dimension bound and length cutoff are chosen
before the chain, Hamiltonian, ground state and register positions. The actual
local circuits are obtained from the physical information estimates and are
then composed with the constructed private initialization and terminal word.
No circuit family, information estimate, output or resource bound is supplied
by the physical caller. The complete constructed circuit retains its derived
stage support and the three-party bound of the prescribed participant table.

**Scope restriction (contiguous chains):** The sites are Fin L. See
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (retired auxiliary registers):** Main registers alone form the
physical blocks; auxiliary copies remain private at their actual retained
owners. Their reference is a product by original copy, not by final party.
See `docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Source: the one-dimensional note, Part II, logarithmic width at lines 245–250,
Construction `con:sweep` at lines 330–342, Proposition `prop:sweep` and proof
at lines 343–396, and the physical density estimate at lines 579–585. The
constant is selected for information exponent 24 before the physical data
and may be enlarged to satisfy the geometric width bounds.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.PairEffect TNLean.PEPS.EncodedFrame ContinuousLinearMap

/-- An explicit uniform length cutoff controls the rounded logarithmic width
and its physical dimensions. The prefactor retains the ceiling's additive one.
Source: Part II, width at lines 245–250 and dimension estimate at lines 579–585. -/
private theorem ceil_log_width_bounds (q : ℕ) (hq : 1 ≤ q) (D : ℝ) (hD : 1 ≤ D)
    {L : ℕ}
    (hcut : max 120 ⌈Real.logPowThreshold (60 * D) (1 / 2) 1 1⌉₊ ≤ L) :
    1 ≤ ⌈D * Real.log (L : ℝ)⌉₊ ∧
      3 * (20 * ⌈D * Real.log (L : ℝ)⌉₊) ≤ L ∧
      (q : ℝ) ^ (80 * ⌈D * Real.log (L : ℝ)⌉₊) ≤
        (q : ℝ) ^ 80 * (L : ℝ) ^ ⌈80 * D * Real.log (q : ℝ)⌉₊ := by
  have hL120 : 120 ≤ L := (le_max_left _ _).trans hcut
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hLpos : (0 : ℝ) < L := zero_lt_one.trans_le hL1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hlog := Real.one_le_log_natCast_of_three_le (by omega : 3 ≤ L)
  have hwidth1 : 1 ≤ D * Real.log (L : ℝ) :=
    one_le_mul_of_one_le_of_one_le hD hlog
  have hwidth0 : 0 ≤ D * Real.log (L : ℝ) := zero_le_one.trans hwidth1
  let w := ⌈D * Real.log (L : ℝ)⌉₊
  have hwidth : D * Real.log (L : ℝ) ≤ (w : ℝ) := Nat.le_ceil _
  have hw : 1 ≤ w := by exact_mod_cast hwidth1.trans hwidth
  have hceil : (w : ℝ) < D * Real.log (L : ℝ) + 1 := Nat.ceil_lt_add_one hwidth0
  have hsmall := Real.mul_log_pow_le_mul_rpow_of_ceil_logPowThreshold_le
    (C := 60 * D) (η := (1 / 2 : ℝ)) (a := 1) (k := 1) (n := L)
    (mul_nonneg (by norm_num) (zero_le_one.trans hD))
    (by norm_num) (by norm_num) ((le_max_right _ _).trans hcut)
  have hsmall' : 60 * D * Real.log (L : ℝ) ≤ (1 / 2 : ℝ) * L := by
    simpa only [pow_one, Real.rpow_one] using hsmall
  have hgeometry : 3 * (20 * w) ≤ L := by
    have h120 : (120 : ℝ) ≤ L := by exact_mod_cast hL120
    have hh : (3 : ℝ) * (20 * (w : ℝ)) ≤ L := by
      nlinarith only [hceil, hsmall', h120]
    exact_mod_cast hh
  have hpow : (q : ℝ) ^ (80 * w) ≤
      (q : ℝ) ^ ((80 : ℝ) * (D * Real.log (L : ℝ) + 1)) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    push_cast
    nlinarith
  have hexp : (q : ℝ) ^ ((80 : ℝ) * (D * Real.log (L : ℝ) + 1)) =
      (q : ℝ) ^ 80 * (L : ℝ) ^ (80 * D * Real.log (q : ℝ)) := by
    rw [Real.rpow_def_of_pos hqpos, ← Real.rpow_natCast,
      Real.rpow_def_of_pos hqpos, Real.rpow_def_of_pos hLpos, ← Real.exp_add]
    congr 1
    ring
  have hpoly : (q : ℝ) ^ (80 * w) ≤
      (q : ℝ) ^ 80 * (L : ℝ) ^ ⌈80 * D * Real.log (q : ℝ)⌉₊ := by
    calc
      _ ≤ (q : ℝ) ^ ((80 : ℝ) * (D * Real.log (L : ℝ) + 1)) := hpow
      _ = (q : ℝ) ^ 80 * (L : ℝ) ^ (80 * D * Real.log (q : ℝ)) := hexp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (Nat.le_ceil _)
  exact ⟨hw, hgeometry, hpoly⟩

/-- The local error exponent gives the source's total vector bound.
Source: Part II, `prop:sweep`, telescoping estimate at lines 390–396. -/
private theorem sweep_error_le {L w : ℕ} (hL : 1 ≤ L)
    (hcount : sweepOperationCount L w ≤ L) :
    (sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ)) ≤
      26 * (L : ℝ) ^ (-11 : ℤ) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans_le hL1)
  have hcount' : (sweepOperationCount L w : ℝ) ≤ L := by exact_mod_cast hcount
  calc
    _ ≤ (L : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ)) :=
      mul_le_mul_of_nonneg_right hcount' (by positivity)
    _ = 4 * (L : ℝ) ^ (-11 : ℤ) := by
      rw [show (-11 : ℤ) = 1 + (-12 : ℤ) by norm_num, zpow_one_add₀ hL0]
      ring
    _ ≤ 26 * (L : ℝ) ^ (-11 : ℤ) :=
      mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 26) (by positivity)

/-- The physical ground-state assumptions construct the complete chain sweep,
with uniform constants, actual standard physical marginal, all chronological
resource bounds and the source's three-party gate bound. The cutoff proof is
an existential output, so positive chain length is derived rather than assumed.
Source: Part II, `con:sweep`, `prop:sweep` and proof, lines 330–396, with the
physical density consequence at lines 579–585. -/
theorem exists_preparation_of_gappedGroundState
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    letI : NeZero q := ⟨by omega⟩
    ∃ (D K : ℝ) (s L₀ : ℕ) (hL₀ : 1 ≤ L₀), 1 ≤ D ∧ 0 < K ∧
      ∀ (L : ℕ) (hsize : L₀ ≤ L),
        let w := ⌈D * Real.log (L : ℝ)⌉₊
        let hL : 0 < L := Nat.lt_of_lt_of_le Nat.zero_lt_one (hL₀.trans hsize)
        ∀ (h : ChainHamiltonian L q R J)
          (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
          Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
        ∀ (pos : Fin L → ℝ × ℝ),
        let Fs := initialFrames L w q pos
        let holder : Frame pos q (Party L w) → Party L w := fun F ↦ F.owner ⟨0, hL⟩
        let H := fun p ↦ framesSpace (Fs.filter fun F ↦ holder F = p)
        let rs := terminalRawOrder L w
        let hn := terminalRawOrder_nodup L w
        let hr := mem_terminalRawOrder (L := L) (w := w)
        let R := terminalRegrouping (q := q) rs hn hr
        let hT := stackRegs_terminalFrames L w q pos
        let A : Mem (privateLayout L w q) ≃ₗᵢ[ℂ]
            EuclideanSpace ℂ (AuxiliarySite L w → Fin q) :=
          groupIso (auxiliaryOwner L w) Finset.univ.toList
            (List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _) (by simp))
        letI := A.symm.toLinearEquiv.finiteDimensional
        ∃ hx : ∀ p, ‖@framesVec (Fin L) (Fin.fintype L) (instDecidableEqFin L)
              q (Party L w) pos
              ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq)⟩
              Ω (Fs.filter fun F ↦ holder F = p)‖ = 1,
          ∃ C : OriginalCircuit (ProductInput.wholePartyLayout H)
              (familyPhysicalOutputLayout (physicalDimension L w q)
                (physicalOrder L w) (privateLayout L w q)),
            let X := ProductInput.ofAllParties H
              (fun p ↦ @framesVec (Fin L) (Fin.fintype L) (instDecidableEqFin L)
              q (Party L w) pos
              ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq)⟩
              Ω (Fs.filter fun F ↦ holder F = p)) hx
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
              ‖terminalStackReadout L w q pos Ψraw -
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
                  Nat.dist (partyLevel p) (partyLevel t) ≤ 2) ∧
              Fintype.card (Party L w) ≤ 2 * L ∧
              C.nonprivateCount ≤ 20 * stageCount L w ∧
              20 * stageCount L w ≤ 2 * L ∧
              (∀ p : Party L w, physicalDimension L w q p ≤ q ^ (80 * w)) ∧
              (∀ p : Party L w,
                (physicalDimension L w q p : ℝ) ≤ K * (L : ℝ) ^ s) ∧
              ‖terminalStackReadout L w q pos Ψraw -
                Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤
                  26 * (L : ℝ) ^ (-11 : ℤ) ∧
              Matrix.rectangularTraceNorm
                (Matrix.partialTraceRight (Matrix.euclideanOuterProduct V V) -
                  Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
                    (Matrix.euclideanOuterProduct Ω Ω)) ≤ 52 * (L : ℝ) ^ (-11 : ℤ) ∧
              (∀ g : C.nonprivateLocations, (C.participants g).card ≤ 3) ∧
              1 ≤ w ∧ 3 * (20 * w) ≤ L := by
  classical
  let : NeZero q := ⟨by omega⟩
  obtain ⟨D₂₄, Nphysical, _, hNphysical, hphysical⟩ :=
    local_stage_circuits_of_logarithmic_separation q hq R J Δ hΔ
  let D := max D₂₄ 1
  let Nwidth := max 120 ⌈Real.logPowThreshold (60 * D) (1 / 2) 1 1⌉₊
  let L₀ := max Nphysical Nwidth
  have hD : 1 ≤ D := le_max_right _ _
  have hL₀ : 1 ≤ L₀ := hNphysical.trans (le_max_left _ _)
  have hK : 0 < (q : ℝ) ^ 80 :=
    pow_pos (by exact_mod_cast (show 0 < q by omega)) 80
  refine ⟨D, (q : ℝ) ^ 80, ⌈80 * D * Real.log (q : ℝ)⌉₊, L₀, hL₀, hD, hK, ?_⟩
  intro L hsize
  dsimp only
  intro h Ω E₀ hgs pos
  let w := ⌈D * Real.log (L : ℝ)⌉₊
  have hL : 0 < L := Nat.lt_of_lt_of_le Nat.zero_lt_one (hL₀.trans hsize)
  have hwidthCut : max 120 ⌈Real.logPowThreshold (60 * D) (1 / 2) 1 1⌉₊ ≤ L :=
    (le_max_right _ _).trans hsize
  have hwidthData := ceil_log_width_bounds q hq D hD hwidthCut
  have hw : 1 ≤ w := hwidthData.1
  have hgeometry : 3 * (20 * w) ≤ L := hwidthData.2.1
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L by omega))
  have hwidth : D₂₄ * Real.log (L : ℝ) ≤ (w : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog).trans (Nat.le_ceil _)
  have hfamily := hphysical L ((le_max_left _ _).trans hsize)
    h Ω E₀ hgs pos w hw hwidth
  choose c hc using hfamily
  let Fs := initialFrames L w q pos
  let holder : Frame pos q (Party L w) → Party L w := fun F ↦ F.owner ⟨0, hL⟩
  let H := fun p ↦ framesSpace (Fs.filter fun F ↦ holder F = p)
  let rs := terminalRawOrder L w
  let hn := terminalRawOrder_nodup L w
  let hr := mem_terminalRawOrder (L := L) (w := w)
  let R := terminalRegrouping (q := q) rs hn hr
  let hT := stackRegs_terminalFrames L w q pos
  let A : Mem (privateLayout L w q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (AuxiliarySite L w → Fin q) :=
    groupIso (auxiliaryOwner L w) Finset.univ.toList
      (List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _) (by simp))
  let := A.symm.toLinearEquiv.finiteDimensional
  obtain ⟨hx, C, hpart, hcount, hsource, hexp, hmono, hnorm, hXi, hsplit,
      hdensity, hsupport, harity, hlocality⟩ :=
    exists_preparation_of_local_circuits c Ω hc hL hgs.1
  let X := ProductInput.ofAllParties H
    (fun p ↦ framesVec Ω (Fs.filter fun F ↦ holder F = p)) hx
  let Ψ := C.eval X.vector
  let V := familyLabelledPhysicalReadout (physicalDimension L w q)
    (physicalOrder L w) (Finset.nodup_toList _) (by simp [physicalOrder])
    (privateLayout L w q) Ψ
  let Ψraw := (Layout.memCongr hT).symm (R.symm Ψ)
  have hparty := card_party_le L w hw hgeometry
  have htwenty := twenty_mul_stageCount_le L w hw hgeometry
  have hoperation : sweepOperationCount L w ≤ 20 * stageCount L w := by
    unfold sweepOperationCount
    omega
  have hcount20 : C.nonprivateCount ≤ 20 * stageCount L w := hcount.trans hoperation
  have hcount2L : 20 * stageCount L w ≤ 2 * L := by omega
  have hdim (p : Party L w) : physicalDimension L w q p ≤ q ^ (80 * w) := by
    simpa only [show 4 * (20 * w) = 80 * w by omega] using
      physicalDimension_le L w q hw hq hgeometry p
  have hpoly (p : Party L w) :
      (physicalDimension L w q p : ℝ) ≤
        (q : ℝ) ^ 80 * (L : ℝ) ^ ⌈80 * D * Real.log (q : ℝ)⌉₊ := by
    calc
      _ ≤ ((q ^ (80 * w) : ℕ) : ℝ) := by exact_mod_cast hdim p
      _ = (q : ℝ) ^ (80 * w) := by simp only [Nat.cast_pow]
      _ ≤ _ := hwidthData.2.2
  have herror := sweep_error_le (by omega : 1 ≤ L) (hoperation.trans htwenty)
  have hsplit' :
      ‖terminalStackReadout L w q pos Ψraw -
        Matrix.euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤
          26 * (L : ℝ) ^ (-11 : ℤ) := hsplit.trans herror
  have hdensity' : Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct V V) -
        Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
          (Matrix.euclideanOuterProduct Ω Ω)) ≤ 52 * (L : ℝ) ^ (-11 : ℤ) := by
    calc
      _ ≤ 2 * ((sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ))) := hdensity
      _ ≤ 2 * (26 * (L : ℝ) ^ (-11 : ℤ)) :=
        mul_le_mul_of_nonneg_left herror (by norm_num)
      _ = _ := by ring
  have harity3 (g : C.nonprivateLocations) : (C.participants g).card ≤ 3 := by
    obtain ⟨k, j, hsub⟩ := hsupport g
    exact card_le_three_of_subset_stageParticipants _ k j hsub
  exact ⟨hx, C, hpart, hcount, hsource, hexp, hmono, hnorm, hXi, hsplit,
    hdensity, hsupport, harity, hlocality, hparty, hcount20, hcount2L, hdim,
    hpoly, hsplit', hdensity', harity3, hw, hgeometry⟩

end TNLean.MPS.AreaLaw.ChainSweep
