/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CeilScaling
import TNLean.PEPS.Approximation.UniformApproximateSampledNetwork
import TNLean.PEPS.Approximation.MessageGateLists

/-!
# Uniform compression of original gates containing bounded messages

The original gate operators and chronological occurrences are fixed before
any approximation precision. At every fixed precision, the original gates
have allowed message-containing monomial lists with polynomial counts,
individual coefficient bounds, and message dimensions. Their bounded messages
are expanded in finite orthonormal coordinates on the same original registers.

The expanded count and coefficient bounds are derived from these original
bounds. A fixed approximation precision then gives literal operator tensor
networks with uniform polynomial virtual dimensions and constant incidence,
approximating the full original physical density without normalization.
No private-dimension or Schmidt-rank bound is imposed.

**Local fix (nonempty parties):** The shared original construction data retain
the existing nonempty-party convention in
`docs/paper-gaps/polypeps_nonempty_parties.tex`. Scalar absorption uses that
existing party and introduces no further premise.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43,
137–175, 199–229, 565–588 and 590–600.
-/

noncomputable section
open scoped Matrix ComplexConjugate NNReal
namespace TNLean.PEPS.PairEffect.GateMapConstruction
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable

/-- Original message-containing expansions available at every fixed
inverse-power precision yield uniform literal operator networks for the
original physical density. Polynomial bounds on the expanded monomial counts
and coefficients are derived from the original counts, individual coefficients,
and bounded polynomial-dimensional messages.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43,
137–175, 565–588 and 590–600. -/
theorem exists_uniform_message_sampled_network
    (P : {L : ℝ // 2 ≤ L} → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, GateMapConstruction (P L))
    (b n d : ℕ) (C_N C_D : ℝ) (hCN : 0 ≤ C_N) (hCD : 0 ≤ C_D)
    (hN₀ : ∀ L, ((C₀ L).circuit.expandedGateCount : ℝ) ≤ C_N * (L : ℝ) ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * (L : ℝ) ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j,
      Nat.card {g : (C₀ L).circuit.gateLocations //
        j ∈ (C₀ L).circuit.participants g} ≤ b)
    (hMessageAvailability : ∀ q : ℕ,
      ∃ (r m : ℕ) (C_K C_C C_M : ℝ) (u v z : ℕ),
        0 ≤ C_K ∧ 0 ≤ C_C ∧ 0 ≤ C_M ∧ ∀ L,
          ∃ (lists : (C₀ L).circuit.MessageGateLists) (K : ℕ),
            (C₀ L).circuit.IsMessageResourceBounded r m K
              (C_M * (L : ℝ) ^ z) (C_C * (L : ℝ) ^ v) lists ∧
            (K : ℝ) ≤ C_K * (L : ℝ) ^ u ∧
            (C₀ L).circuit.IsMessageGateApproximation ((L : ℝ) ^ q)⁻¹
              lists (C₀ L).gateMaps)
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
            w.isGateApproximation_budget_of_power_bound (L : ℝ) countC (t : ℝ)
              w.expandedGateCount n (by assumption) (by dsimp [countC]; linarith) hNre hprecision
        let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) _).le G hbudget
        let hbW := w.isExpansionBounded_rescaledOriginal
          (sourceGateBudget_pos (half_pos hε) _).le G hbudget hb
        let δ := sourceGateBudget ε w.expandedGateCount
        let R := W.produce.physicalFirstReplacement (sourceGateBudget_pos hε _)
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
  have hExpandedAvailability : ∀ q : ℕ, ∃ (r : ℕ) (C_K C_C : ℝ) (u v : ℕ),
      0 ≤ C_K ∧ 0 ≤ C_C ∧ ∀ L,
        ∃ (lists : (C₀ L).circuit.GateLists) (K : ℕ),
          ((C₀ L).circuit.reexpand lists).IsTermwiseBounded r (C_C * (L : ℝ) ^ v) ∧
          (∀ g, ((C₀ L).circuit.reexpand lists).monomialCount g ≤ K) ∧
          (K : ℝ) ≤ C_K * (L : ℝ) ^ u ∧
          ((C₀ L).circuit.reexpand lists).IsGateApproximation ((L : ℝ) ^ q)⁻¹
            ((C₀ L).circuit.reexpandGateMaps lists (C₀ L).gateMaps) := by
    intro q
    obtain ⟨r, m, C_K, C_C, C_M, u, v, z, hCK, hCC, hCM, hLists⟩ :=
      hMessageAvailability q
    let A := C_K * (1 + C_M) ^ m
    let Ccoeff := C_K * C_C * (1 + C_M) ^ m
    refine ⟨r, 1 + A, Ccoeff, u + z * m, u + v + z * m,
      by dsimp [A]; positivity, by dsimp [Ccoeff]; positivity, ?_⟩
    intro L
    obtain ⟨lists, K, hresources, hK, happrox⟩ := hLists L
    let w := (C₀ L).circuit
    let D := (1 + C_M) * (L : ℝ) ^ z
    let C := C_C * (L : ℝ) ^ v
    let expanded := w.expandMessageGateLists lists
    let K' := ⌈(K : ℝ) * D ^ m⌉₊
    have hLone : 1 ≤ (L : ℝ) := le_trans (by norm_num) L.property
    have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
      (le_add_of_nonneg_right hCM) (one_le_pow₀ hLone)
    have hC : 0 ≤ C := mul_nonneg hCC (pow_nonneg (zero_le_one.trans hLone) _)
    have hresources' : w.IsMessageResourceBounded r m K D C lists :=
      hresources.mono_dimension (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one) (by positivity))
    have hcount := w.monomialCount_expandMessageGateLists_le hD lists hresources'
    have hterm := w.isTermwiseBounded_expandMessageGateLists hD hC lists (C₀ L).gateMaps
      happrox hresources'
    have hcountPower : (K : ℝ) * D ^ m ≤ A * (L : ℝ) ^ (u + z * m) := by
      calc
        _ ≤ (C_K * (L : ℝ) ^ u) * D ^ m :=
          mul_le_mul_of_nonneg_right hK (by positivity)
        _ = _ := by dsimp [D, A]; rw [mul_pow, pow_add, pow_mul]; ring
    have hceilPower : (K' : ℝ) ≤ (1 + A) * (L : ℝ) ^ (u + z * m) := by
      simpa only [add_comm A 1] using Nat.ceil_le_add_one_mul_of_le_mul
        (by positivity : 0 ≤ (K : ℝ) * D ^ m) hcountPower (one_le_pow₀ hLone)
    have hcoeffPower : (K : ℝ) * C * D ^ m ≤
        Ccoeff * (L : ℝ) ^ (u + v + z * m) := by
      calc
        _ ≤ ((C_K * (L : ℝ) ^ u) * C) * D ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hC) (by positivity)
        _ = _ := by dsimp [C, D, Ccoeff]; rw [mul_pow, pow_add, pow_add, pow_mul]; ring
    exact ⟨expanded, K', hterm.mono_coefficient hcoeffPower, hcount,
      hceilPower, w.isGateApproximation_expandMessageGateLists lists (C₀ L).gateMaps happrox⟩
  exact exists_uniform_approximate_sampled_network P C₀ b n d C_N C_D hCN hCD
    hN₀ hphysical₀ harity₀ hlifetime₀ hExpandedAvailability p hp

end TNLean.PEPS.PairEffect.GateMapConstruction
