/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GateMapConstruction
import TNLean.PEPS.Approximation.UniformApproximateNetworkBounds
import TNLean.PEPS.Approximation.EffectCircuitTermwiseCoefficientBounds
import TNLean.PEPS.Approximation.DistributedContractionScalar

/-!
# Uniform operator networks from approximate expansions of original gates

The original construction family is indexed only by sizes at least two.
At every fixed integer precision, the same original gate occurrences admit
allowed monomial expansions with uniform polynomial counts and individual
coefficient bounds. Absolute coefficient sums are derived from those bounds.
One fixed precision supplies a literal operator tensor network at every size,
with polynomial virtual alphabets and the original constant incidence bound.

The error concerns the full physical density of the original gate operators,
with the original finite private registers traced out and without normalization.
The same actual source circuit and sample count are used in the contraction
and its resource estimates. No numerical private-dimension or Schmidt-rank
bound is assumed.

**Local fix (nonempty parties):** The original input and output data retain
the existing nonempty-party convention in
`docs/paper-gaps/polypeps_nonempty_parties.tex`. It supplies the party at which
the exterior scalar is absorbed, with no division and no additional premise.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229, 565–588 and 590–600.
-/

noncomputable section
open scoped Matrix ComplexConjugate NNReal
namespace TNLean.PEPS.PairEffect.GateMapConstruction
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable

/-- Expansions available at each fixed inverse-power precision yield literal
operator tensor networks approximating the original density uniformly in size.
The precision, monomial source/effect bound, and polynomial constants are all
chosen before the size. The only coefficient hypothesis is termwise.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
565–588 and 590–600. -/
theorem exists_uniform_approximate_sampled_network
    (P : {L : ℝ // 2 ≤ L} → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, GateMapConstruction (P L))
    (b n d : ℕ) (C_N C_D : ℝ) (hCN : 0 ≤ C_N) (hCD : 0 ≤ C_D)
    (hN₀ : ∀ L, ((C₀ L).circuit.expandedGateCount : ℝ) ≤ C_N * (L : ℝ) ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * (L : ℝ) ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j,
      Nat.card {g : (C₀ L).circuit.gateLocations //
        j ∈ (C₀ L).circuit.participants g} ≤ b)
    (hExpansionAvailability : ∀ q : ℕ, ∃ (r : ℕ) (C_K C_C : ℝ) (u v : ℕ),
      0 ≤ C_K ∧ 0 ≤ C_C ∧ ∀ L,
        ∃ (lists : (C₀ L).circuit.GateLists) (K : ℕ),
          ((C₀ L).circuit.reexpand lists).IsTermwiseBounded r (C_C * (L : ℝ) ^ v) ∧
          (∀ g, ((C₀ L).circuit.reexpand lists).monomialCount g ≤ K) ∧
          (K : ℝ) ≤ C_K * (L : ℝ) ^ u ∧
          ((C₀ L).circuit.reexpand lists).IsGateApproximation ((L : ℝ) ^ q)⁻¹
            ((C₀ L).circuit.reexpandGateMaps lists (C₀ L).gateMaps))
    (p : ℝ) (hp : 0 < p) :
    let countC := 1 + C_N
    let t := ⌈p⌉₊
    let q := n + t + ⌈16 * countC⌉₊
    ∃ (r : ℕ) (C_p : ℝ) (α : ℕ), 0 ≤ C_p ∧ 0 < α ∧ ∀ L,
      let C := C₀ L
      let H := C.initialSpace
      let hH := C.finite_initialSpace
      let x := C.initialVector
      let hx := C.norm_initialVector
      let physicalDim := C.physicalDimension
      let ps := C.physicalOrder
      let hps := C.physicalOrder_nodup
      let hcover := C.mem_physicalOrder
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
        ∃ (B : ℝ≥0) (hB : 1 ≤ B)
          (hb : w.IsExpansionBounded r (B : ℝ))
          (happrox : w.IsGateApproximation ((L : ℝ) ^ q)⁻¹ G),
        let ε := ((L : ℝ) ^ t)⁻¹
        let hε : 0 < ε := by positivity
        let hεone : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
        let hbudget : w.IsGateApproximation
            (sourceGateBudget (ε / 2) w.expandedGateCount) G := by
          have hprecision : w.IsGateApproximation
              ((L : ℝ) ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * countC⌉₊))⁻¹ G := by
            simpa only [Nat.ceil_natCast] using happrox
          simpa only [Real.rpow_neg (by linarith : 0 ≤ (L : ℝ)), Real.rpow_natCast] using
            w.isGateApproximation_budget_of_power_bound G (L : ℝ) countC (t : ℝ)
              w.expandedGateCount n (by assumption) (by dsimp [countC]; linarith) hNre hprecision
        let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) _).le G hbudget
        let hbW := w.isExpansionBounded_rescaledOriginal
          (sourceGateBudget_pos (half_pos hε) _).le G hbudget hb
        let δ := sourceGateBudget ε w.expandedGateCount
        let R := W.produce.physicalFirstReplacement (sourceGateBudget_pos hε w.expandedGateCount)
          (familyPhysicalLayout physicalDim ps) priv W.isAllowed_produce
          ((W.isExpansionBounded_produce_iff r (B : ℝ)).mpr hbW)
        let k := sourceSamplingCount (Fintype.card R.sourceLocations)
          ((B : ℝ) ^ (4 * b) * (D : ℝ) ^ 4) ε
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
  intro countC t q
  obtain ⟨r, C_K, C_C, u, v, hCK, hCC, hLists⟩ := hExpansionAvailability q
  let C_B := 1 + C_K * C_C
  let s := u + v
  have hCB : 0 ≤ C_B := add_nonneg zero_le_one (mul_nonneg hCK hCC)
  obtain ⟨C_p, α, hC, hα, hfamily⟩ :=
    EffectCircuit.exists_uniform_sampled_approximate_network_bounds
      r b n d countC (1 + C_D) (by dsimp [countC]; linarith)
      (fun _ ↦ C_K) (fun _ ↦ C_B) (fun _ ↦ u) (fun _ ↦ s)
      (fun _ ↦ hCK) (fun _ ↦ hCB) p hp
  refine ⟨r, C_p, α, hC, hα, ?_⟩
  intro L C H hH x hx physicalDim ps hps hcover priv hpriv ref Goriginal hL D
  have hLone : 1 ≤ (L : ℝ) := le_trans (by norm_num) hL
  obtain ⟨lists, K, htermwise, hmonomial, hK, happrox⟩ := hLists L
  let w := ref.reexpand lists
  let G := ref.reexpandGateMaps lists Goriginal
  obtain ⟨B, hB, hb, hBB⟩ :=
    w.exists_one_le_isExpansionBounded_of_termwise_power_bounds
      (L : ℝ) C_K C_C u v hLone hCK hCC
      hmonomial htermwise hK
  have hNre : (w.expandedGateCount : ℝ) ≤ countC * (L : ℝ) ^ n := by
    rw [ref.expandedGateCount_reexpand lists]
    exact (hN₀ L).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (by positivity))
  have harity : ∀ g, (w.participants g).card ≤ b := by
    intro g
    rw [ref.participants_reexpand lists g]
    exact harity₀ L _
  have hlifetime : ∀ j, Nat.card {g : w.gateLocations // j ∈ w.participants g} ≤ b := by
    intro j
    rw [ref.participationCount_reexpand lists j]
    exact hlifetime₀ L j
  have hD : 1 ≤ D := by
    change (1 : ℝ) ≤ (1 + C_D) * (L : ℝ) ^ d
    exact one_le_mul_of_one_le_of_one_le
      (le_add_of_nonneg_right hCD) (one_le_pow₀ hLone)
  have hphysical : ∀ j, (physicalDim j : ℝ≥0) ≤ D := by
    intro j
    change (physicalDim j : ℝ) ≤ (D : ℝ)
    exact (hphysical₀ L j).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (by positivity))
  obtain ⟨T, herror, hdim, hinc, hlocal⟩ := hfamily (L : ℝ) hL (P L)
    H hH x hx physicalDim ps hps hcover priv w G K B D hB hD
    hb hmonomial harity hlifetime hphysical hpriv hK hNre hBB le_rfl happrox
  refine ⟨lists, B, hB, hb, happrox, ?_⟩
  intro ε hε hεone hbudget W hbW δ R k
  letI := Layout.finiteDimensional_mem_of_registers priv hpriv
  let p₀ := Classical.choice C.nonemptyParties
  let μ := R.emptyGateScalar * conj R.emptyGateScalar
  let c := DistributedOperatorContraction.densityPairCoefficient
    (fun g : R.nonemptyGateLocations ↦ R.branchLabels g.1)
    (fun g : R.nonemptyGateLocations ↦ R.branchLabels g.1)
    (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
    (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card)
  have hρ : w.physicalDensityWithGateMaps G
      (familyLabelledPhysicalReadout physicalDim ps hps hcover priv)
      (ProductInput.ofAllParties H x hx).vector = C.physicalDensity := by
    change w.physicalDensityWithGateMaps G
      (familyLabelledPhysicalReadout physicalDim ps hps hcover priv) C.input.vector =
        ref.physicalDensityWithGateMaps Goriginal
          (familyLabelledPhysicalReadout physicalDim ps hps hcover priv) C.input.vector
    simp only [EffectCircuit.physicalDensityWithGateMaps,
      ref.evalWithGateMaps_reexpand lists Goriginal]
  rw [hρ] at herror
  refine ⟨fun j ξ z ↦ (if j = p₀ then μ else 1) • T j ξ z, ?_, hdim, hinc, ?_⟩
  · have hscalar := DistributedOperatorContraction.contractedOperator_smul_at_party
      (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
      (fun g _ ↦ SourceCircuit.sourceGateRoot_mem R g)
      (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k c T p₀ μ
    rw [hscalar]
    exact herror
  · intro e j l hj hl
    obtain ⟨g, hjg, hlg⟩ := hlocal e j l hj hl
    refine ⟨ref.reexpandLocationsEquiv lists g, ?_⟩
    have hpart := ref.participants_reexpand lists g
    exact ⟨hpart ▸ hjg, hpart ▸ hlg⟩

end TNLean.PEPS.PairEffect.GateMapConstruction
