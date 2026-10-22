/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolPhysicalPreparation
import TNLean.Lattice.Compression.DistributedConstruction
import TNLean.Lattice.Compression.GateCoefficientBounds

/-!
# Uniform physical families for chain compression

The constants are chosen before every physical instance. The family contains
all admissible sufficiently large chains, Hamiltonians, ground vectors,
and ground energies. The actual preparation circuits and
normalized product inputs are chosen from the physical preparation theorem.
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

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice TNLean.Lattice.PartyCircuit TNLean.Lattice.Sheet

/-- The constructed chain sweep, with its original normalized product input,
actual main physical dimensions and retained auxiliary registers.
Source: Part II, `prop:sweep`, lines 350–396 and 579–585. -/
def preparationConstruction {L w q : ℕ}
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hL : 0 < L)
    (hx : ∀ p : Party L w,
      ‖framesVec (Sheet.refFamily Ω) ((initialFrames L w).filter
        fun F ↦ F.owner ⟨0, hL⟩ = p)‖ = 1)
    (C : OriginalCircuit
      (ProductInput.wholePartyLayout fun p : Party L w ↦
        framesSpace (Sheet.regs q) ((initialFrames L w).filter
          fun F ↦ F.owner ⟨0, hL⟩ = p))
      (familyPhysicalOutputLayout (physicalDimension L w q)
        (physicalOrder L w) (privateLayout L w q))) :
    DistributedConstruction (Party L w) where
  nonemptyParties := ⟨.inl (0 : Fin (stageCount L w + 1))⟩
  initialSpace := fun p ↦ framesSpace (Sheet.regs q) ((initialFrames L w).filter
    fun F ↦ F.owner ⟨0, hL⟩ = p)
  finite_initialSpace := fun p ↦ Layout.finiteDimensional_mem_of_registers _
    (Sheet.finiteDimensional_of_mem_stackRegs _)
  initialVector := fun p ↦ framesVec (Sheet.refFamily Ω) ((initialFrames L w).filter
    fun F ↦ F.owner ⟨0, hL⟩ = p)
  norm_initialVector := hx
  physicalDimension := physicalDimension L w q
  physicalOrder := physicalOrder L w
  physicalOrder_nodup := Finset.nodup_toList _
  mem_physicalOrder := by simp [physicalOrder]
  privateOutput := privateLayout L w q
  finite_privateOutput := by
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    change FiniteDimensional ℂ (EuclideanSpace ℂ (Fin q))
    infer_instance
  circuit := C

/-- The main-coordinate equivalence transports the literal pure density.
Source: Part II, main-block readout at lines 355–360 and 579–585. -/
private theorem outerProduct_mainCoordinates (L w q : ℕ)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    let target := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (mainConfigurationEquiv L w q) Ω
    Matrix.euclideanOuterProduct target target =
      Matrix.reindex (mainConfigurationEquiv L w q) (mainConfigurationEquiv L w q)
        (Matrix.euclideanOuterProduct Ω Ω) := by
  ext x y
  rfl

/-- One family indexed by every admissible sufficiently large physical
instance satisfies all hypotheses of uniform compression. Its circuit, input
and readout are exactly those of the constructed sweep.
Source: Part II, `prop:sweep`, lines 350–396 and 579–585; Theorem B,
lines 587–615; polynomial-PEPS Theorem 5.2, `04-compression.tex:137–175`. -/
theorem exists_uniform_preparation_family
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (D K : ℝ) (s L₀ : ℕ) (hL₀ : 2 ≤ L₀), 1 ≤ D ∧ 0 < K ∧
      let ι := {a : Σ L : ℕ, ChainHamiltonian L q R J ×
          EuclideanSpace ℂ (Fin L → Fin q) × ℝ //
        L₀ ≤ a.1 ∧ Matrix.IsGappedGroundState a.2.1.operator a.2.2.2 a.2.2.1 Δ}
      let length := fun i : ι ↦ i.val.1
      let width := fun i : ι ↦ ⌈D * Real.log (length i : ℝ)⌉₊
      let ground := fun i : ι ↦ i.val.2.2.1
      let hL := fun i : ι ↦
        Nat.lt_of_lt_of_le (by omega : 0 < L₀) i.property.1
      let Fs := fun i : ι ↦ initialFrames (length i) (width i)
      let holder := fun (i : ι) (F : Sheet (Fin (length i)) (Party (length i) (width i))) ↦
        F.owner ⟨0, hL i⟩
      let H := fun (i : ι) p ↦ framesSpace (Sheet.regs q) ((Fs i).filter fun F ↦ holder i F = p)
      ∃ hx : ∀ (i : ι) p,
          ‖framesVec (Sheet.refFamily (ground i)) ((Fs i).filter fun F ↦ holder i F = p)‖ = 1,
        ∃ C : ∀ i : ι, OriginalCircuit (ProductInput.wholePartyLayout (H i))
            (familyPhysicalOutputLayout (physicalDimension (length i) (width i) q)
              (physicalOrder (length i) (width i)) (privateLayout (length i) (width i) q)),
          let C₀ := fun i : ι ↦
            preparationConstruction (w := width i) (ground i) (hL i) (hx i) (C i)
          let target := fun i : ι ↦
            LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
              (mainConfigurationEquiv (length i) (width i) q) (ground i)
          (∀ i : ι, (2 : ℝ) ≤ length i) ∧
            (∀ i : ι, ((C₀ i).circuit.nonprivateCount : ℝ) ≤
              2 * (length i : ℝ) ^ (1 : ℕ)) ∧
            (∀ (i : ι) p, ((C₀ i).physicalDimension p : ℝ) ≤
              K * (length i : ℝ) ^ s) ∧
            (∀ (i : ι) g, ((C₀ i).circuit.participants g).card ≤ 3) ∧
            (∀ (i : ι) p, (C₀ i).circuit.participationCount p ≤ 40) ∧
            (∀ i : ι, ∃ M : ℕ, (C₀ i).circuit.IsMonomialBounded M ∧
              (M : ℝ) ≤ 1 * (length i : ℝ) ^ (0 : ℕ)) ∧
            (∀ i : ι, (C₀ i).circuit.IsExpansionBounded 1
              (1 * (length i : ℝ) ^ (0 : ℕ))) ∧
            (∀ i : ι, ‖target i‖ = 1) ∧
            (∀ i : ι, Matrix.rectangularTraceNorm
              ((show Matrix
                  ((p : Party (length i) (width i)) →
                    Fin (physicalDimension (length i) (width i) q p))
                  ((p : Party (length i) (width i)) →
                    Fin (physicalDimension (length i) (width i) q p)) ℂ
                from (C₀ i).physicalDensity) -
                Matrix.euclideanOuterProduct (target i) (target i)) ≤
                  52 * (length i : ℝ) ^ (-11 : ℤ)) ∧
            (∀ (i : ι) (g : (C₀ i).circuit.nonprivateLocations)
                (p t : Party (length i) (width i)),
              p ∈ (C₀ i).circuit.participants g →
                t ∈ (C₀ i).circuit.participants g →
                  Nat.dist (partyLevel p) (partyLevel t) ≤ 2) ∧
            (∀ i : ι, Matrix.euclideanOuterProduct (target i) (target i) =
              Matrix.reindex (mainConfigurationEquiv (length i) (width i) q)
                (mainConfigurationEquiv (length i) (width i) q)
                  (Matrix.euclideanOuterProduct (ground i) (ground i))) ∧
            (∀ i : ι, 1 ≤ width i ∧ 3 * (20 * width i) ≤ length i) := by
  classical
  obtain ⟨D, K, s, N, _, hD, hK, hprepare⟩ :=
    exists_preparation_of_gappedGroundState q hq R J Δ hΔ
  let L₀ := max N 2
  have hL₀ : 2 ≤ L₀ := le_max_right _ _
  refine ⟨D, K, s, L₀, hL₀, hD, hK, ?_⟩
  let ι := {a : Σ L : ℕ, ChainHamiltonian L q R J ×
      EuclideanSpace ℂ (Fin L → Fin q) × ℝ //
    L₀ ≤ a.1 ∧ Matrix.IsGappedGroundState a.2.1.operator a.2.2.2 a.2.2.1 Δ}
  let length := fun i : ι ↦ i.val.1
  let width := fun i : ι ↦ ⌈D * Real.log (length i : ℝ)⌉₊
  let ground := fun i : ι ↦ i.val.2.2.1
  have hfamily := fun i : ι ↦
    hprepare (length i) ((le_max_left N 2).trans i.property.1)
      i.val.2.1 (ground i) i.val.2.2.2 i.property.2
  choose hx C hp using hfamily
  refine ⟨hx, C, ?_⟩
  dsimp only
  simp only [← forall_and]
  intro i
  obtain ⟨hpart, _, _, hexp, hmono, _, _, _, _, _, _harity, hgate,
      _, hcount20, htwenty, _, hpoly, _, hdensity, harityThree, hw, hmargin⟩ := hp i
  have hcount : (C i).nonprivateCount ≤ 2 * length i := hcount20.trans htwenty
  refine ⟨?_, ?_, hpoly, harityThree, hpart, ?_, ?_, ?_, ?_, hgate, ?_, ⟨hw, hmargin⟩⟩
  · exact_mod_cast (hL₀.trans i.property.1)
  · change ((C i).nonprivateCount : ℝ) ≤ 2 * (length i : ℝ) ^ (1 : ℕ)
    simpa only [pow_one] using
      (show ((C i).nonprivateCount : ℝ) ≤ 2 * (length i : ℝ) by exact_mod_cast hcount)
  · exact ⟨1, hmono, by simp⟩
  · change (C i).IsExpansionBounded 1 (1 * (length i : ℝ) ^ (0 : ℕ))
    simpa only [pow_zero, mul_one] using hexp
  · exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (mainConfigurationEquiv (length i) (width i) q)).norm_map (ground i)).trans
        i.property.2.1
  · rw [outerProduct_mainCoordinates]
    exact hdensity
  · exact outerProduct_mainCoordinates (length i) (width i) q (ground i)

end TNLean.MPS.AreaLaw.ChainSweep
