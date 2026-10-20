/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolUniformPreparation
import TNLean.MPS.AreaLaw.SharpChainCompression

/-!
# The crossing estimate from physical chain data


**Local fix (retired auxiliary registers):** Only the main registers are
physical outputs; all auxiliary copies remain private at their actual owners.
See docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex.

All constants precede the Hamiltonian and ground state. The same chosen
physical preparation supplies all compression premises. The sampled density,
polynomial alphabets and crossing bounds concern one network at each index.

Source: one-dimensional note, Part II, proof of Theorem B,
part2b_mps_protocol.tex:587–614 and order of constants:626–632.
-/

noncomputable section
namespace TNLean.MPS.AreaLaw.ChainSweep
open QuantumCircuit TNLean.Lattice TNLean.PEPS TNLean.PEPS.PairEffect TNLean.PEPS.EncodedFrame
open TNLean.PEPS.Approximation

/-- The physical hypotheses alone give uniformly polynomial sampled networks
whose every block cut has at most 1280 crossing links, hence at most 1600.
All preparation resource bounds are retained for the same actual circuit.
Source: Part II, thm:B, part2b_mps_protocol.tex:587–614. -/
theorem exists_physical_sampled_network_with_prefixCrossingLinks_le_1600
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
          ((∀ i : ι, (2 : ℝ) ≤ length i) ∧
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
            (∀ i : ι, 1 ≤ width i ∧ 3 * (20 * width i) ≤ length i)) ∧
          ∃ (C_p : ℝ) (α : ℕ), 0 ≤ C_p ∧ 0 < α ∧ ∀ i,
              ∃ (Gate : Type) (_ : Fintype Gate) (_ : DecidableEq Gate)
                (participants : Gate → Finset (Party (length i) (width i)))
                (root : Gate → Party (length i) (width i))
                (hroot : ∀ g ∈ (Finset.univ : Finset Gate), root g ∈ participants g)
                (Label : Gate → Type) (_ : ∀ g, Fintype (Label g)) (k : ℕ)
                (c : (g : Gate) → Label g → ℂ)
                (T : (j : Party (length i) (width i)) → DistributedOperatorContraction.GateLabelsAt
                    (Finset.univ : Finset Gate) participants Label j →
                  (DistributedOperatorContraction.SampleAt (Finset.univ : Finset Gate)
                    participants j → Fin k) →
                  Matrix (Fin ((C₀ i).physicalDimension j)) (Fin ((C₀ i).physicalDimension j)) ℂ),
                Matrix.rectangularTraceNorm
                    ((show Matrix
                        ((p : Party (length i) (width i)) →
                          Fin (physicalDimension (length i) (width i) q p))
                        ((p : Party (length i) (width i)) →
                          Fin (physicalDimension (length i) (width i) q p)) ℂ
                      from DistributedOperatorContraction.contractedOperator
                        Finset.univ participants root hroot Label k c T) -
                      Matrix.euclideanOuterProduct (target i) (target i)) ≤
                    (length i : ℝ) ^ (-5 : ℝ) + (52 * (length i : ℝ) ^ (-11 : ℤ)) ∧
                  Matrix.rectangularTraceNorm
                    (DistributedOperatorContraction.contractedOperator Finset.univ participants root
                      hroot Label k c T - (C₀ i).physicalDensity) ≤ (length i : ℝ) ^ (-5 : ℝ) ∧
                  1 - (52 * (length i : ℝ) ^ (-11 : ℤ)) ≤ (C₀ i).physicalDensity.trace.re ∧
                  (C₀ i).physicalDensity.trace.re ≤ 1 ∧
                  (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
                    (Fintype.card (DistributedOperatorContraction.alphabet Finset.univ participants
                      root Label k e) : ℝ) ≤ C_p * (length i : ℝ) ^ α) ∧
                  (∀ j, (incidentDistributedLinks Finset.univ participants root j).card ≤
                    160) ∧
                  (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
                    ∀ j l, j ∈ distributedLinkParties root e.1 →
                      l ∈ distributedLinkParties root e.1 →
                      ∃ g : (C₀ i).circuit.nonprivateLocations,
                        j ∈ (C₀ i).circuit.participants g ∧ l ∈ (C₀ i).circuit.participants g) ∧
                  (∀ r', (prefixCrossingLinks Finset.univ participants root r').card ≤ 1280) ∧
                  (∀ r', (prefixCrossingLinks Finset.univ participants root r').card ≤ 1600) := by
  classical
  obtain ⟨D, K, s, L₀, hL₀, hD, hK, hfamily⟩ :=
    exists_uniform_preparation_family q hq R J Δ hΔ
  refine ⟨D, K, s, L₀, hL₀, hD, hK, ?_⟩
  intro ι length width ground hL Fs holder H
  obtain ⟨hx, C, hresources⟩ := hfamily
  refine ⟨hx, C, ?_⟩
  intro C₀ target
  refine ⟨hresources, ?_⟩
  obtain ⟨hsize, hcount, hphysical, harity, hlifetime, hmonomial, hexpansion,
    htarget, hdensity, hgate, _houter, _hwidth⟩ := hresources
  exact exists_uniform_sampled_network_with_prefixCrossingLinks_le_1600
    (fun i : ι ↦ (length i : ℝ)) hsize length width C₀
    1 s 1 0 0 2 K 1 1 hcount hphysical harity hlifetime hmonomial hexpansion
    target htarget (fun i : ι ↦ 52 * (length i : ℝ) ^ (-11 : ℤ))
    hdensity hgate 5 (by norm_num)

end TNLean.MPS.AreaLaw.ChainSweep
