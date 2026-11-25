/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SweepPreparation.ProtocolPhysicalPreparation
import QICLean.Circuit.Party.Compression.Construction
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Uniform physical families for chain compression

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
