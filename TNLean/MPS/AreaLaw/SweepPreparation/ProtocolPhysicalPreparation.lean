/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepLocalCircuits
import TNLean.MPS.AreaLaw.SweepPreparation.ChainStageIncidence
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepGeometry
import QICLean.Analysis.Real.ExplicitThresholds
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolSweepPlacement
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolTerminalWord
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra
import QICLean.Circuit.Party.Compression.Construction

/-!
# Physical preparation by a logarithmic-width chain sweep

The width constant, polynomial dimension bound and length cutoff are chosen
before the chain, Hamiltonian and ground state. The actual
local circuits are obtained from the physical information estimates and are
then composed with the constructed private initialization and terminal regrouping.
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

It also contains the following results.

* `TNLean.MPS.AreaLaw.ChainSweep.exists_preparation_of_local_circuits`: conditional preparation from
  the actual local-stage circuits.
* `TNLean.MPS.AreaLaw.ChainSweep.preparationConstruction`,
  `TNLean.MPS.AreaLaw.ChainSweep.exists_uniform_preparation_family`: uniform physical families for
  chain compression.
-/

section ProtocolConditionalPreparation

/-!
## Conditional preparation from the actual local-stage circuits

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

end

end ProtocolConditionalPreparation

section ProtocolPhysicalPreparation

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open Matrix QuantumCircuit QuantumCircuit.Party
open ManyBody (Config)

open ManyBody (IsGapped groundSpace ChainInteraction)

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
    ∃ (D K : ℝ) (s L₀ : ℕ) (_ : 1 ≤ L₀), 1 ≤ D ∧ 0 < K ∧
      ∀ (L : ℕ), L₀ ≤ L →
        let w := ⌈D * Real.log (L : ℝ)⌉₊
        ∀ (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
          (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∃ φ : ∀ p, EuclideanSpace ℂ
            (stackSystem (Sheet.system q) (initialFrames L w) (fun _ ↦ Unit) p),
          (∀ p, ‖φ p‖ = 1) ∧
          (WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x) :
            EuclideanSpace ℂ (Config (stackSystem (Sheet.system q) (initialFrames L w)
              fun _ ↦ Unit))) = framesVec (fun S ↦ S.refVec Ω) (initialFrames L w) ∧
          ∃ C : OriginalCircuit (stackSystem (Sheet.system q) (initialFrames L w) fun _ ↦ Unit)
              (physicalSystem (physicalDimension L w q) (privateSystem L w q)),
            let Ψ := toEuclideanLin C.op
              (WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x))
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
                  Nat.dist (partyLevel p) (partyLevel t) ≤ 2) ∧
              Fintype.card (Party L w) ≤ 2 * L ∧
              C.nonprivateCount ≤ 20 * stageCount L w ∧
              20 * stageCount L w ≤ 2 * L ∧
              (∀ p : Party L w, physicalDimension L w q p ≤ q ^ (80 * w)) ∧
              (∀ p : Party L w,
                (physicalDimension L w q p : ℝ) ≤ K * (L : ℝ) ^ s) ∧
              ‖terminalStackReadout L w Ψraw -
                euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤
                  26 * (L : ℝ) ^ (-11 : ℤ) ∧
              rectangularTraceNorm
                (partialTraceRight (euclideanOuterProduct V V) -
                  reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
                    (euclideanOuterProduct Ω Ω)) ≤ 52 * (L : ℝ) ^ (-11 : ℤ) ∧
              (∀ g : C.nonprivateLocations, (C.participants g).card ≤ 3) ∧
              1 ≤ w ∧ 3 * (20 * w) ≤ L := by
  classical
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
  intro L hsize w h hh hhJ Ω E₀ hΩ hgap hspan
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
    h hh hhJ Ω E₀ hΩ hgap hspan w hw hwidth
  choose c hc using hfamily
  obtain ⟨φ, hφ, hφv, C, hpart, hcount, hsource, hexp, hmono, hnorm, hXi, hsplit,
      hdensity, hsupport, harity, hlocality⟩ :=
    exists_preparation_of_local_circuits c Ω hc hL hΩ
  let Ψ := toEuclideanLin C.op (WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x))
  let V := toEuclideanLin
    (physicalReadout (physicalDimension L w q) (privateSystem L w q)) Ψ
  let Ψraw := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.piCongrRight (terminalPartyEquiv L w q))).symm ((terminalRegrouping L w q).symm Ψ)
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
      ‖terminalStackReadout L w Ψraw -
        euclideanTensorVector Ω (auxiliaryReference L w q Ω)‖ ≤
          26 * (L : ℝ) ^ (-11 : ℤ) := hsplit.trans herror
  have hdensity' : rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct V V) -
        reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
          (euclideanOuterProduct Ω Ω)) ≤ 52 * (L : ℝ) ^ (-11 : ℤ) := by
    calc
      _ ≤ 2 * ((sweepOperationCount L w : ℝ) * (4 * (L : ℝ) ^ (-12 : ℤ))) := hdensity
      _ ≤ 2 * (26 * (L : ℝ) ^ (-11 : ℤ)) :=
        mul_le_mul_of_nonneg_left herror (by norm_num)
      _ = _ := by ring
  have harity3 (g : C.nonprivateLocations) : (C.participants g).card ≤ 3 := by
    obtain ⟨k, j, hsub⟩ := hsupport g
    exact card_le_three_of_subset_stageParticipants _ k j hsub
  refine ⟨φ, hφ, hφv, C, ?_⟩
  intro Ψ' V' Ψraw' ε'
  refine ⟨hpart, hcount, hsource, hexp, hmono, hnorm, hXi, ?_,
    ?_, hsupport, harity, hlocality, hparty, hcount20, hcount2L, hdim,
    hpoly, ?_, ?_, harity3, hw, hgeometry⟩
  · exact hsplit
  · exact hdensity
  · exact hsplit'
  · exact hdensity'

end TNLean.MPS.AreaLaw.ChainSweep

end

end ProtocolPhysicalPreparation

section ProtocolUniformPreparation

/-!
## Uniform physical families for chain compression

The constants are chosen before every physical instance. The family contains
all admissible sufficiently large chains, Hamiltonians, ground vectors,
and ground energies. The actual preparation circuits and
normalized product inputs are chosen from the physical preparation theorem; the
product input is the reference vector of the initial sheets.
They give the existing distributed constructions without changing the circuit
or the standard physical and private readout. The target vector is precisely
the original ground vector in the main-register block coordinates.

**Scope restriction (contiguous chains):** The sites are Fin L. See
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (retired auxiliary registers):** Only main registers form physical
blocks; all auxiliary copies remain private at their actual owners. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Source: the one-dimensional note, Part II, `prop:sweep`, lines 350–396 and
579–585, and the proof of Theorem B, lines 587–615; polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 137–175.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open Matrix QuantumCircuit QuantumCircuit.Party
open ManyBody (IsGapped groundSpace Config)

/-- The constructed chain sweep, with its normalized product input,
actual main physical dimensions and retained auxiliary registers.
Source: Part II, `prop:sweep`, lines 350–396 and 579–585. -/
def preparationConstruction {L w q : ℕ}
    (φ : ∀ p : Party L w, EuclideanSpace ℂ
      (stackSystem (Sheet.system q) (initialFrames L w) (fun _ ↦ Unit) p))
    (hφ : ∀ p, ‖φ p‖ = 1)
    (C : OriginalCircuit (stackSystem (Sheet.system q) (initialFrames L w) fun _ ↦ Unit)
      (physicalSystem (physicalDimension L w q) (privateSystem L w q))) :
    DistributedConstruction (Party L w)
      (stackSystem (Sheet.system q) (initialFrames L w) fun _ ↦ Unit)
      (physicalDimension L w q) (privateSystem L w q) where
  nonemptyParties := ⟨.inl (0 : Fin (stageCount L w + 1))⟩
  initialVector := φ
  norm_initialVector := hφ
  circuit := C

/-- The main-coordinate equivalence transports the literal pure density.
Source: Part II, main-block readout at lines 355–360 and 579–585. -/
private theorem outerProduct_mainCoordinates (L w q : ℕ)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    let target := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (mainConfigurationEquiv L w q) Ω
    euclideanOuterProduct target target =
      reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
        (euclideanOuterProduct Ω Ω) := by
  ext x y
  rfl

/-- One family indexed by every admissible sufficiently large physical
instance satisfies all hypotheses of uniform compression. Its circuit, input
and readout are exactly those of the constructed sweep; the input is the
reference vector of the initial sheets.
Source: Part II, `prop:sweep`, lines 350–396 and 579–585; Theorem B,
lines 587–615; polynomial-PEPS Theorem 5.2, `04-compression.tex:137–175`. -/
theorem exists_uniform_preparation_family
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (D K : ℝ) (s L₀ : ℕ) (_ : 2 ≤ L₀), 1 ≤ D ∧ 0 < K ∧
      let ι := {a : Σ L : ℕ, ManyBody.ChainInteraction L q R ×
          EuclideanSpace ℂ (Fin L → Fin q) × ℝ //
        L₀ ≤ a.1 ∧ (∀ X, (a.2.1.term X).IsHermitian) ∧ (∀ X, ‖a.2.1.term X‖ ≤ J) ∧ ‖a.2.2.1‖ = 1 ∧
            IsGapped a.2.1.hamiltonian a.2.2.2 Δ ∧
          groundSpace a.2.1.hamiltonian a.2.2.2 = Submodule.span ℂ {a.2.2.1}}
      let length := fun i : ι ↦ i.val.1
      let width := fun i : ι ↦ ⌈D * Real.log (length i : ℝ)⌉₊
      let ground := fun i : ι ↦ i.val.2.2.1
      let Fs := fun i : ι ↦ initialFrames (length i) (width i)
      ∃ (φ : ∀ (i : ι) (p : Party (length i) (width i)), EuclideanSpace ℂ
          (stackSystem (Sheet.system q) (Fs i) (fun _ ↦ Unit) p)) (hφ : ∀ i p, ‖φ i p‖ = 1),
        ∃ C : ∀ i : ι, OriginalCircuit (stackSystem (Sheet.system q) (Fs i) fun _ ↦ Unit)
            (physicalSystem (physicalDimension (length i) (width i) q)
              (privateSystem (length i) (width i) q)),
          let C₀ := fun i : ι ↦ preparationConstruction (φ i) (hφ i) (C i)
          let target := fun i : ι ↦
            LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
              (mainConfigurationEquiv (length i) (width i) q) (ground i)
          (∀ i : ι, (2 : ℝ) ≤ length i) ∧
            (∀ i : ι, (C₀ i).input = framesVec (fun S ↦ S.refVec (ground i)) (Fs i)) ∧
            (∀ i : ι, ((C₀ i).circuit.nonprivateCount : ℝ) ≤
              2 * (length i : ℝ) ^ (1 : ℕ)) ∧
            (∀ (i : ι) p, (physicalDimension (length i) (width i) q p : ℝ) ≤
              K * (length i : ℝ) ^ s) ∧
            (∀ (i : ι) g, ((C₀ i).circuit.participants g).card ≤ 3) ∧
            (∀ (i : ι) p, (C₀ i).circuit.participation p ≤ 40) ∧
            (∀ i : ι, ∃ M : ℕ, (C₀ i).circuit.IsMonomialBounded M ∧
              (M : ℝ) ≤ 1 * (length i : ℝ) ^ (0 : ℕ)) ∧
            (∀ i : ι, (C₀ i).circuit.IsExpansionBounded 1
              (1 * (length i : ℝ) ^ (0 : ℕ))) ∧
            (∀ i : ι, ‖target i‖ = 1) ∧
            (∀ i : ι, rectangularTraceNorm
              ((C₀ i).physicalDensity - euclideanOuterProduct (target i) (target i)) ≤
                  52 * (length i : ℝ) ^ (-11 : ℤ)) ∧
            (∀ (i : ι) (g : (C₀ i).circuit.nonprivateLocations)
                (p t : Party (length i) (width i)),
              p ∈ (C₀ i).circuit.participants g →
                t ∈ (C₀ i).circuit.participants g →
                  Nat.dist (partyLevel p) (partyLevel t) ≤ 2) ∧
            (∀ i : ι, euclideanOuterProduct (target i) (target i) =
              reindex (mainConfigurationEquiv (length i) (width i) q)
                (mainConfigurationEquiv (length i) (width i) q)
                  (euclideanOuterProduct (ground i) (ground i))) ∧
            (∀ i : ι, 1 ≤ width i ∧ 3 * (20 * width i) ≤ length i) := by
  classical
  obtain ⟨D, K, s, N, _, hD, hK, hprepare⟩ :=
    exists_preparation_of_gappedGroundState q hq R J Δ hΔ
  let L₀ := max N 2
  have hL₀ : 2 ≤ L₀ := le_max_right _ _
  refine ⟨D, K, s, L₀, hL₀, hD, hK, ?_⟩
  intro ι length width ground Fs
  have hfamily := fun i : ι ↦
    hprepare (length i) ((le_max_left N 2).trans i.property.1)
      i.val.2.1 i.property.2.1 i.property.2.2.1 (ground i) i.val.2.2.2 i.property.2.2.2.1
      i.property.2.2.2.2.1 i.property.2.2.2.2.2
  choose φ hφ hφv C hp using hfamily
  refine ⟨φ, hφ, C, ?_⟩
  dsimp only
  simp only [← forall_and]
  intro i
  obtain ⟨hpart, _, _, hexp, hmono, _, _, _, _, _, _harity, hgate,
      _, hcount20, htwenty, _, hpoly, _, hdensity, harityThree, hw, hmargin⟩ := hp i
  have hcount : (C i).nonprivateCount ≤ 2 * length i := hcount20.trans htwenty
  refine ⟨?_, hφv i, ?_, hpoly, harityThree, hpart, ?_, ?_, ?_, ?_, hgate, ?_, ⟨hw, hmargin⟩⟩
  · exact_mod_cast (hL₀.trans i.property.1)
  · change ((C i).nonprivateCount : ℝ) ≤ 2 * (length i : ℝ) ^ (1 : ℕ)
    simpa only [pow_one] using
      (show ((C i).nonprivateCount : ℝ) ≤ 2 * (length i : ℝ) by exact_mod_cast hcount)
  · exact ⟨1, hmono, by simp⟩
  · change (C i).IsExpansionBounded 1 (1 * (length i : ℝ) ^ (0 : ℕ))
    simpa only [pow_zero, mul_one] using hexp
  · exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (mainConfigurationEquiv (length i) (width i) q)).norm_map (ground i)).trans
        i.property.2.2.2.1
  · rw [outerProduct_mainCoordinates, DistributedConstruction.physicalDensity,
      OriginalCircuit.physicalDensity_eq]
    exact hdensity
  · exact outerProduct_mainCoordinates (length i) (width i) q (ground i)

end TNLean.MPS.AreaLaw.ChainSweep

end

end ProtocolUniformPreparation
