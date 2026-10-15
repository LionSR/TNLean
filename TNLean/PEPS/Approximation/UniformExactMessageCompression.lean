/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.UniformMessageGateCompression

/-!
# Uniform compression of exact original message expansions

One exact expansion at each size satisfies every fixed local inverse-power
accuracy. The original operators, private maps, gate occurrences and physical
density are fixed before that accuracy is chosen. The uniform approximate
message theorem therefore supplies the exact-expansion clause without a
second sampling or contraction argument.

The conclusion is a literal operator tensor network.

**Local fix (nonempty parties):** The exterior scalar is absorbed using the
original nonempty-party convention recorded in
`docs/paper-gaps/polypeps_nonempty_parties.tex`; no output normalization or
numerical bound on private dimensions is introduced.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43,
137–175 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate NNReal
namespace TNLean.PEPS.PairEffect.GateMapConstruction
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable

/-- Exact original message-containing expansions yield uniform literal operator
networks for the original physical density. The resource constants and the
original exact expansions are fixed independently of the requested accuracy.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43,
137–175 and 565–588. -/
theorem exists_uniform_exact_message_sampled_network
    (P : {L : ℝ // 2 ≤ L} → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, GateMapConstruction (P L))
    (b n d : ℕ) (C_N C_D : ℝ) (hCN : 0 ≤ C_N) (hCD : 0 ≤ C_D)
    (hN₀ : ∀ L, ((C₀ L).circuit.expandedGateCount : ℝ) ≤ C_N * (L : ℝ) ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * (L : ℝ) ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j,
      Nat.card {g : (C₀ L).circuit.gateLocations //
        j ∈ (C₀ L).circuit.participants g} ≤ b)
    (r₀ m₀ : ℕ) (C_K C_C C_M : ℝ) (u v z : ℕ)
    (hCK : 0 ≤ C_K) (hCC : 0 ≤ C_C) (hCM : 0 ≤ C_M)
    (hExactMessageExpansion : ∀ L,
      ∃ (lists : (C₀ L).circuit.MessageGateLists) (K : ℕ),
        (C₀ L).circuit.IsMessageResourceBounded r₀ m₀ K
          (C_M * (L : ℝ) ^ z) (C_C * (L : ℝ) ^ v) lists ∧
        (K : ℝ) ≤ C_K * (L : ℝ) ^ u ∧
        (C₀ L).circuit.IsMessageGateApproximation 0 lists (C₀ L).gateMaps)
    (p : ℝ) (hp : 0 < p) :
    let countC := 1 + C_N
    let t := ⌈p⌉₊
    let q := n + t + ⌈16 * countC⌉₊
    ∃ (r : ℕ) (C_p : ℝ) (α : ℕ), 0 ≤ C_p ∧ 0 < α ∧ ∀ L,
      let C := C₀ L
      let H := C.initialSpace
      let hH := C.finite_initialSpace
      let physicalDim := C.physicalDimension
      let ps := C.physicalOrder
      let priv := C.privateOutput
      let hpriv := C.finite_privateOutput
      let ref := C.circuit
      let Goriginal := C.gateMaps
      let hL : 2 ≤ (L : ℝ) := L.property
      let D : ℝ≥0 := ⟨(1 + C_D) * (L : ℝ) ^ d, by positivity⟩
      ∃ lists : ref.GateLists,
        let w := ref.reexpand lists
        let G := ref.reexpandGateMaps lists Goriginal
        let hNre : (w.expandedGateCount : ℝ) ≤ countC * (L : ℝ) ^ n := by
          rw [ref.expandedGateCount_reexpand lists]
          exact (hN₀ L).trans (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left zero_le_one) (by positivity))
        ∃ (B : ℝ≥0) (_ : 1 ≤ B)
          (hb : w.IsExpansionBounded r (B : ℝ))
          (happrox : w.IsGateApproximation ((L : ℝ) ^ q)⁻¹ G),
        let ε := ((L : ℝ) ^ t)⁻¹
        let hε : 0 < ε := by positivity
        let hbudget : w.IsGateApproximation
            (sourceGateBudget (ε / 2) w.expandedGateCount) G := by
          have hprecision : w.IsGateApproximation
              ((L : ℝ) ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * countC⌉₊))⁻¹ G := by
            simpa only [Nat.ceil_natCast] using happrox
          simpa only [Real.rpow_neg (by linarith [L.property] : 0 ≤ (L : ℝ)),
            Real.rpow_natCast] using
            w.isGateApproximation_budget_of_power_bound G (L : ℝ) countC (t : ℝ)
              w.expandedGateCount n L.property (by dsimp [countC]; linarith) hNre hprecision
        let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) _).le G hbudget
        let hbW := w.isExpansionBounded_rescaledOriginal
          (sourceGateBudget_pos (half_pos hε) _).le G hbudget hb
        let R := W.produce.physicalFirstReplacement (sourceGateBudget_pos hε w.expandedGateCount)
          (familyPhysicalLayout physicalDim ps) priv W.isAllowed_produce
          ((W.isExpansionBounded_produce_iff r (B : ℝ)).mpr hbW)
        let k := sourceSamplingCount (Fintype.card R.sourceLocations)
          ((B : ℝ) ^ (4 * b) * (D : ℝ) ^ (4 : ℕ)) ε
        letI := ProductInput.finiteDimensional_wholePartyMem H hH
        letI := Layout.finiteDimensional_mem_of_registers priv hpriv
        ∃ T : (j : P L) → DistributedOperatorContraction.GateLabelsAt
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1)
            (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) j →
            (DistributedOperatorContraction.SampleAt
              (Finset.univ : Finset R.nonemptyGateLocations)
              (fun g ↦ R.participants g.1) j → Fin k) →
            Matrix (Fin (physicalDim j)) (Fin (physicalDim j)) ℂ,
          Matrix.rectangularTraceNorm
            (DistributedOperatorContraction.contractedOperator
                (Finset.univ : Finset R.nonemptyGateLocations)
                (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
                (fun g _ ↦ SourceCircuit.sourceGateRoot_mem R g)
                (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k
                (DistributedOperatorContraction.densityPairCoefficient
                  (Gate := R.nonemptyGateLocations)
                  (fun g ↦ R.branchLabels g.1) (fun g ↦ R.branchLabels g.1)
                  (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
                  (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card)) T -
              C.physicalDensity) ≤ (L : ℝ) ^ (-p) ∧
          (∀ e : DistributedOperatorContraction.Link
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
            (Fintype.card (DistributedOperatorContraction.alphabet
              (Finset.univ : Finset R.nonemptyGateLocations)
              (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
              (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k e) : ℝ) ≤ C_p * (L : ℝ) ^ α) ∧
          (∀ j, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) j).card ≤
              2 * b * (b - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
            ∀ j l, j ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
              l ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
              ∃ g : ref.gateLocations, j ∈ ref.participants g ∧ l ∈ ref.participants g) := by
  classical
  have hAvailability : ∀ q : ℕ,
      ∃ (r m : ℕ) (C_K C_C C_M : ℝ) (u v z : ℕ),
        0 ≤ C_K ∧ 0 ≤ C_C ∧ 0 ≤ C_M ∧ ∀ L,
          ∃ (lists : (C₀ L).circuit.MessageGateLists) (K : ℕ),
            (C₀ L).circuit.IsMessageResourceBounded r m K
              (C_M * (L : ℝ) ^ z) (C_C * (L : ℝ) ^ v) lists ∧
            (K : ℝ) ≤ C_K * (L : ℝ) ^ u ∧
            (C₀ L).circuit.IsMessageGateApproximation ((L : ℝ) ^ q)⁻¹
              lists (C₀ L).gateMaps := by
    intro q
    refine ⟨r₀, m₀, C_K, C_C, C_M, u, v, z, hCK, hCC, hCM, ?_⟩
    intro L
    obtain ⟨lists, K, hresources, hK, hExact⟩ := hExactMessageExpansion L
    have hL0 : 0 ≤ (L : ℝ) := (by norm_num : (0 : ℝ) ≤ 2).trans L.property
    exact ⟨lists, K, hresources, hK,
      hExact.mono (inv_nonneg.mpr (pow_nonneg hL0 q))⟩
  exact exists_uniform_message_sampled_network P C₀ b n d C_N C_D hCN hCD
    hN₀ hphysical₀ harity₀ hlifetime₀ hAvailability p hp

end TNLean.PEPS.PairEffect.GateMapConstruction
