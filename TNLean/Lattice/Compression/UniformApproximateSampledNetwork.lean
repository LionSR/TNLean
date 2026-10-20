/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.GateMapConstruction
import TNLean.Lattice.Compression.UniformApproximateNetworkBounds
import TNLean.Lattice.Compression.EffectCircuitTermwiseCoefficientBounds
import TNLean.Lattice.Compression.DistributedContractionScalar
import TNLean.Lattice.Compression.MessageGateLists

/-!
# Uniform operator networks from approximate expansions of original gates

The original construction family is indexed by an arbitrary type `ι`, with a
size `size i ≥ 2` at each index; several indices may share one size, so the
constants are uniform over every family member of a given size.
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

The exterior scalar is absorbed at an existing party: the construction data carry the
nonempty-party convention, a degenerate-case reading of the source recorded in
`docs/paper-gaps/polypeps_nonempty_parties.tex` and marked on `DistributedConstruction`.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229, 565–588 and 590–600.
-/

noncomputable section
open scoped Matrix ComplexConjugate NNReal

/-- A polynomial bound with a real constant `C` persists with the positive part
`max C 0`, at every nonnegative base. This removes sign conditions on the
polynomial constants of polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 133–175. -/
theorem TNLean.PEPS.Approximation.mul_pow_le_max_zero_mul_pow (C : ℝ) {x : ℝ}
    (hx : 0 ≤ x) (k : ℕ) : C * x ^ k ≤ max C 0 * x ^ k :=
  mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx _)

namespace TNLean.PEPS.Approximation

/-- The prefactor of Theorem 5.2 in terms of the constants of its hypotheses:
`sampledNetworkPrefactor` at gate-count constant `1 + max C_N 0`,
physical-dimension constant `1 + max C_D 0`, monomial-count constant
`max C_K 0` and coefficient-sum constant `1 + max C_K 0 * max C_C 0`, where
`C_C` is the termwise coefficient constant.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
202–204 and 565–585. -/
noncomputable def compressionPrefactor (r b : ℕ) (C_N C_D C_K C_C : ℝ) : ℝ :=
  sampledNetworkPrefactor r b (1 + max C_N 0) (1 + max C_D 0) (max C_K 0)
    (1 + max C_K 0 * max C_C 0)

/-- The link exponent of Theorem 5.2 in terms of the exponents of its
hypotheses: `sampledNetworkExponent` with coefficient-sum exponent `u + v`,
where `u` is the monomial-count exponent and `v` the termwise coefficient
exponent.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
202–204 and 565–585. -/
noncomputable def compressionExponent (r b n d u v : ℕ) (p : ℝ) : ℕ :=
  sampledNetworkExponent r b n d u (u + v) p

/-- The prefactor of Theorem 5.2 is positive (`04-compression.tex`,
lines 565–585). -/
theorem compressionPrefactor_pos (r b : ℕ) (C_N C_D C_K C_C : ℝ) :
    0 < compressionPrefactor r b C_N C_D C_K C_C :=
  sampledNetworkPrefactor_pos _ _ _ _ _ _

/-- The link exponent of Theorem 5.2 is positive for a positive accuracy
exponent (`04-compression.tex`, lines 565–585). -/
theorem compressionExponent_pos (r b n d u v : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < compressionExponent r b n d u v p :=
  sampledNetworkExponent_pos _ _ _ _ _ _ hp

/-- The prefactor of Theorem 5.2 from an absolute coefficient-sum bound:
`sampledNetworkPrefactor` at gate-count constant `1 + max C_N 0`,
physical-dimension constant `1 + max C_D 0`, monomial-count constant
`max C_K 0` and coefficient-sum constant `1 + max C_S 0`.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–208 and 565–585. -/
noncomputable def sumCompressionPrefactor (r b : ℕ) (C_N C_D C_K C_S : ℝ) : ℝ :=
  sampledNetworkPrefactor r b (1 + max C_N 0) (1 + max C_D 0) (max C_K 0) (1 + max C_S 0)

/-- The prefactor of Theorem 5.2 from termwise coefficient bounds is the prefactor from the
coefficient-sum bound `max C_K 0 * max C_C 0`, the product of the monomial-count and termwise
constants (`04-compression.tex`, lines 143–147 and 199–208). -/
theorem compressionPrefactor_eq_sumCompressionPrefactor (r b : ℕ) (C_N C_D C_K C_C : ℝ) :
    compressionPrefactor r b C_N C_D C_K C_C =
      sumCompressionPrefactor r b C_N C_D C_K (max C_K 0 * max C_C 0) := by
  rw [compressionPrefactor, sumCompressionPrefactor,
    max_eq_left (mul_nonneg (le_max_right C_K 0) (le_max_right C_C 0))]

/-- The termwise link exponent of Theorem 5.2 is the coefficient-sum exponent at
coefficient-sum degree `u + v` (`04-compression.tex`, lines 565–585). -/
theorem compressionExponent_eq_sampledNetworkExponent (r b n d u v : ℕ) (p : ℝ) :
    compressionExponent r b n d u v p = sampledNetworkExponent r b n d u (u + v) p :=
  rfl

end TNLean.PEPS.Approximation

namespace TNLean.PEPS.PairEffect.GateMapConstruction
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable

/-- **Theorem 5.2 from coefficient-sum bounds.** Expansions available at one fixed
inverse-power precision, with `r` pair effects per monomial, monomial-count bound `C_K L ^ u`
and absolute coefficient-sum bound `C_S L ^ s` at every gate, yield literal operator tensor
networks approximating the original density uniformly in size. The link alphabets are at most
`C_p * L ^ α` for every `C_p ≥ sumCompressionPrefactor r b C_N C_D C_K C_S` and every
`α ≥ sampledNetworkExponent r b n d u s p`. The termwise form
`uniform_approximate_sampled_network_of_le` is the case `s = u + v`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 143–147 and 199–208 (the
coefficient sums), 137–175, 565–588 and 590–600. -/
theorem uniform_approximate_sampled_network_of_sum_le
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, GateMapConstruction (P L))
    (b n d : ℕ) (C_N C_D : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.expandedGateCount : ℝ) ≤ C_N * (size L) ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * (size L) ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j,
      Nat.card {g : (C₀ L).circuit.gateLocations //
        j ∈ (C₀ L).circuit.participants g} ≤ b)
    (r : ℕ) (C_K₀ C_S₀ : ℝ) (u s : ℕ) (p : ℝ)
    (hLists : ∀ L, ∃ (lists : (C₀ L).circuit.GateLists) (K : ℕ),
      ((C₀ L).circuit.reexpand lists).IsExpansionBounded r (C_S₀ * (size L) ^ s) ∧
      (∀ g, ((C₀ L).circuit.reexpand lists).monomialCount g ≤ K) ∧
      (K : ℝ) ≤ C_K₀ * (size L) ^ u ∧
      ((C₀ L).circuit.reexpand lists).IsGateApproximation
        ((size L) ^ (n + ⌈p⌉₊ + ⌈16 * (1 + max C_N 0)⌉₊))⁻¹
        ((C₀ L).circuit.reexpandGateMaps lists (C₀ L).gateMaps))
    {C_p : ℝ} {α : ℕ} (hC : sumCompressionPrefactor r b C_N C_D C_K₀ C_S₀ ≤ C_p)
    (hα : sampledNetworkExponent r b n d u s p ≤ α) :
    let countC := 1 + max C_N 0
    let t := ⌈p⌉₊
    let q := n + t + ⌈16 * countC⌉₊
    ∀ L,
    let C := C₀ L
    let H := C.initialSpace
    let hH := C.finite_initialSpace
    let physicalDim := C.physicalDimension
    let ps := C.physicalOrder
    let priv := C.privateOutput
    let hpriv := C.finite_privateOutput
    let ref := C.circuit
    let Goriginal := C.gateMaps
    let hL : 2 ≤ (size L) := hsize L
    let D : ℝ≥0 := ⟨(1 + max C_D 0) * (size L) ^ d, by positivity⟩
    ∃ lists : ref.GateLists,
      let w := ref.reexpand lists
      let G := ref.reexpandGateMaps lists Goriginal
      let hNre : (w.expandedGateCount : ℝ) ≤ countC * (size L) ^ n := by
        rw [ref.expandedGateCount_reexpand lists]
        exact (hN₀ L).trans (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_add_of_nonneg_left zero_le_one)) (by positivity))
      ∃ (B : ℝ≥0) (_ : 1 ≤ B)
        (hb : w.IsExpansionBounded r (B : ℝ))
        (happrox : w.IsGateApproximation ((size L) ^ q)⁻¹ G),
      let ε := ((size L) ^ t)⁻¹
      let hε : 0 < ε := by positivity
      let hbudget : w.IsGateApproximation
          (sourceGateBudget (ε / 2) w.expandedGateCount) G := by
        have hprecision : w.IsGateApproximation
            ((size L) ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * countC⌉₊))⁻¹ G := by
          simpa only [Nat.ceil_natCast] using happrox
        simpa only [Real.rpow_neg (by linarith [hsize L] : 0 ≤ (size L)),
          Real.rpow_natCast] using
          w.isGateApproximation_budget_of_power_bound G (size L) countC (t : ℝ)
            w.expandedGateCount n (hsize L) (by dsimp [countC]; linarith [le_max_right C_N 0])
            hNre hprecision
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
            C.physicalDensity) ≤ (size L) ^ (-p) ∧
        (∀ e : DistributedOperatorContraction.Link
          (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
          (Fintype.card (DistributedOperatorContraction.alphabet
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
            (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k e) : ℝ) ≤ C_p * (size L) ^ α) ∧
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
  let C_K := max C_K₀ 0
  have hCK : 0 ≤ C_K := le_max_right _ _
  let C_B := 1 + max C_S₀ 0
  have hCB : 0 ≤ C_B := add_nonneg zero_le_one (le_max_right _ _)
  have hfamily :=
    EffectCircuit.uniform_sampled_approximate_network_bounds_of_le
      r b n d countC (1 + max C_D 0) (by dsimp [countC]; linarith [le_max_right C_N 0])
      C_K C_B u s hCK hCB p hC hα
  intro L C H hH physicalDim ps priv hpriv ref Goriginal hL D
  let x := C.initialVector
  let hx := C.norm_initialVector
  let hps := C.physicalOrder_nodup
  let hcover := C.mem_physicalOrder
  have hLone : 1 ≤ (size L) := le_trans (by norm_num) hL
  obtain ⟨lists, K, hsum₀, hmonomial, hK₀, happrox⟩ := hLists L
  have hL0 : 0 ≤ size L := zero_le_one.trans hLone
  have hK : (K : ℝ) ≤ C_K * (size L) ^ u :=
    hK₀.trans (mul_pow_le_max_zero_mul_pow C_K₀ hL0 u)
  let w := ref.reexpand lists
  let G := ref.reexpandGateMaps lists Goriginal
  have hB1 : (1 : ℝ) ≤ C_B * (size L) ^ s :=
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (le_max_right _ _))
      (one_le_pow₀ hLone)
  let B : ℝ≥0 := ⟨C_B * (size L) ^ s, zero_le_one.trans hB1⟩
  have hB : 1 ≤ B := by exact_mod_cast hB1
  have hb : w.IsExpansionBounded r (B : ℝ) :=
    hsum₀.mono le_rfl (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_add_of_nonneg_left zero_le_one)) (by positivity))
  have hBB : (B : ℝ) ≤ C_B * (size L) ^ s := le_rfl
  have hNre : (w.expandedGateCount : ℝ) ≤ countC * (size L) ^ n := by
    rw [ref.expandedGateCount_reexpand lists]
    exact (hN₀ L).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_add_of_nonneg_left zero_le_one)) (by positivity))
  have harity : ∀ g, (w.participants g).card ≤ b := by
    intro g
    rw [ref.participants_reexpand lists g]
    exact harity₀ L _
  have hlifetime : ∀ j, Nat.card {g : w.gateLocations // j ∈ w.participants g} ≤ b := by
    intro j
    rw [ref.participationCount_reexpand lists j]
    exact hlifetime₀ L j
  have hD : 1 ≤ D := by
    change (1 : ℝ) ≤ (1 + max C_D 0) * (size L) ^ d
    exact one_le_mul_of_one_le_of_one_le
      (le_add_of_nonneg_right (le_max_right _ _)) (one_le_pow₀ hLone)
  have hphysical : ∀ j, (physicalDim j : ℝ≥0) ≤ D := by
    intro j
    change (physicalDim j : ℝ) ≤ (D : ℝ)
    exact (hphysical₀ L j).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_add_of_nonneg_left zero_le_one)) (by positivity))
  obtain ⟨T, herror, hdim, hinc, hlocal⟩ := hfamily (size L) hL (P L)
    H hH x hx physicalDim ps hps hcover priv w G K B D hB hD
    hb hmonomial harity hlifetime hphysical hpriv hK hNre hBB le_rfl happrox
  refine ⟨lists, B, hB, hb, happrox, ?_⟩
  intro ε hε hbudget W hbW R k
  let := Layout.finiteDimensional_mem_of_registers priv hpriv
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
    simp only [EffectCircuit.physicalDensityWithGateMaps]
    rw [show w.evalWithGateMaps G = ref.evalWithGateMaps Goriginal from
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

/-- Expansions available at one fixed inverse-power precision, with `r` pair
effects per monomial, monomial-count bound `C_K L ^ u` and termwise coefficient
bound `C_C L ^ v`, yield literal operator tensor networks approximating the
original density uniformly in size. The link alphabets are at most
`C_p * L ^ α` for every `C_p ≥ compressionPrefactor r b C_N C_D C_K C_C` and
every `α ≥ compressionExponent r b n d u v p`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
565–588 and 590–600. -/
theorem uniform_approximate_sampled_network_of_le
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, GateMapConstruction (P L))
    (b n d : ℕ) (C_N C_D : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.expandedGateCount : ℝ) ≤ C_N * (size L) ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * (size L) ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j,
      Nat.card {g : (C₀ L).circuit.gateLocations //
        j ∈ (C₀ L).circuit.participants g} ≤ b)
    (r : ℕ) (C_K₀ C_C₀ : ℝ) (u v : ℕ) (p : ℝ)
    (hLists : ∀ L, ∃ (lists : (C₀ L).circuit.GateLists) (K : ℕ),
      ((C₀ L).circuit.reexpand lists).IsTermwiseBounded r (C_C₀ * (size L) ^ v) ∧
      (∀ g, ((C₀ L).circuit.reexpand lists).monomialCount g ≤ K) ∧
      (K : ℝ) ≤ C_K₀ * (size L) ^ u ∧
      ((C₀ L).circuit.reexpand lists).IsGateApproximation
        ((size L) ^ (n + ⌈p⌉₊ + ⌈16 * (1 + max C_N 0)⌉₊))⁻¹
        ((C₀ L).circuit.reexpandGateMaps lists (C₀ L).gateMaps))
    {C_p : ℝ} {α : ℕ} (hC : compressionPrefactor r b C_N C_D C_K₀ C_C₀ ≤ C_p)
    (hα : compressionExponent r b n d u v p ≤ α) :
    let countC := 1 + max C_N 0
    let t := ⌈p⌉₊
    let q := n + t + ⌈16 * countC⌉₊
    ∀ L,
    let C := C₀ L
    let H := C.initialSpace
    let hH := C.finite_initialSpace
    let physicalDim := C.physicalDimension
    let ps := C.physicalOrder
    let priv := C.privateOutput
    let hpriv := C.finite_privateOutput
    let ref := C.circuit
    let Goriginal := C.gateMaps
    let hL : 2 ≤ (size L) := hsize L
    let D : ℝ≥0 := ⟨(1 + max C_D 0) * (size L) ^ d, by positivity⟩
    ∃ lists : ref.GateLists,
      let w := ref.reexpand lists
      let G := ref.reexpandGateMaps lists Goriginal
      let hNre : (w.expandedGateCount : ℝ) ≤ countC * (size L) ^ n := by
        rw [ref.expandedGateCount_reexpand lists]
        exact (hN₀ L).trans (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_add_of_nonneg_left zero_le_one)) (by positivity))
      ∃ (B : ℝ≥0) (_ : 1 ≤ B)
        (hb : w.IsExpansionBounded r (B : ℝ))
        (happrox : w.IsGateApproximation ((size L) ^ q)⁻¹ G),
      let ε := ((size L) ^ t)⁻¹
      let hε : 0 < ε := by positivity
      let hbudget : w.IsGateApproximation
          (sourceGateBudget (ε / 2) w.expandedGateCount) G := by
        have hprecision : w.IsGateApproximation
            ((size L) ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * countC⌉₊))⁻¹ G := by
          simpa only [Nat.ceil_natCast] using happrox
        simpa only [Real.rpow_neg (by linarith [hsize L] : 0 ≤ (size L)),
          Real.rpow_natCast] using
          w.isGateApproximation_budget_of_power_bound G (size L) countC (t : ℝ)
            w.expandedGateCount n (hsize L) (by dsimp [countC]; linarith [le_max_right C_N 0])
            hNre hprecision
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
            C.physicalDensity) ≤ (size L) ^ (-p) ∧
        (∀ e : DistributedOperatorContraction.Link
          (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
          (Fintype.card (DistributedOperatorContraction.alphabet
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
            (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k e) : ℝ) ≤ C_p * (size L) ^ α) ∧
        (∀ j, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) j).card ≤
            2 * b * (b - 1)) ∧
        (∀ e : DistributedOperatorContraction.Link
          (Finset.univ : Finset R.nonemptyGateLocations)
          (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
          ∀ j l, j ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
            l ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
            ∃ g : ref.gateLocations, j ∈ ref.participants g ∧ l ∈ ref.participants g) := by
  refine uniform_approximate_sampled_network_of_sum_le size hsize P C₀ b n d C_N C_D hN₀
    hphysical₀ harity₀ hlifetime₀ r C_K₀ (max C_K₀ 0 * max C_C₀ 0) u (u + v) p (fun L ↦ ?_)
    (by rwa [compressionPrefactor_eq_sumCompressionPrefactor] at hC) hα
  obtain ⟨lists, K, ht, hm, hK, happrox⟩ := hLists L
  have hL0 : 0 ≤ size L := by linarith [hsize L]
  exact ⟨lists, K, EffectCircuit.isExpansionBounded_of_termwise_power_bounds _ (size L)
    (max C_K₀ 0) (max C_C₀ 0) u v hL0 (le_max_right _ _) hm
    (ht.mono_coefficient (mul_pow_le_max_zero_mul_pow C_C₀ hL0 v))
    (hK.trans (mul_pow_le_max_zero_mul_pow C_K₀ hL0 u)), hm, hK, happrox⟩

/-- Expansions available at each fixed inverse-power precision yield literal
operator tensor networks approximating the original density uniformly in size.
The precision, monomial source/effect bound, and polynomial constants are all
chosen before the size. The only coefficient hypothesis is termwise. The
constants are `compressionPrefactor` and `compressionExponent` at the expansion
data of the selected precision, as in
`uniform_approximate_sampled_network_of_le`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
565–588 and 590–600. -/
theorem exists_uniform_approximate_sampled_network
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, GateMapConstruction (P L))
    (b n d : ℕ) (C_N C_D : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.expandedGateCount : ℝ) ≤ C_N * (size L) ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * (size L) ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j,
      Nat.card {g : (C₀ L).circuit.gateLocations //
        j ∈ (C₀ L).circuit.participants g} ≤ b)
    (hExpansionAvailability : ∀ q : ℕ, ∃ (r : ℕ) (C_K C_C : ℝ) (u v : ℕ), ∀ L,
        ∃ (lists : (C₀ L).circuit.GateLists) (K : ℕ),
          ((C₀ L).circuit.reexpand lists).IsTermwiseBounded r (C_C * (size L) ^ v) ∧
          (∀ g, ((C₀ L).circuit.reexpand lists).monomialCount g ≤ K) ∧
          (K : ℝ) ≤ C_K * (size L) ^ u ∧
          ((C₀ L).circuit.reexpand lists).IsGateApproximation ((size L) ^ q)⁻¹
            ((C₀ L).circuit.reexpandGateMaps lists (C₀ L).gateMaps))
    (p : ℝ) (hp : 0 < p) :
    let countC := 1 + max C_N 0
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
      let hL : 2 ≤ (size L) := hsize L
      let D : ℝ≥0 := ⟨(1 + max C_D 0) * (size L) ^ d, by positivity⟩
      ∃ lists : ref.GateLists,
        let w := ref.reexpand lists
        let G := ref.reexpandGateMaps lists Goriginal
        let hNre : (w.expandedGateCount : ℝ) ≤ countC * (size L) ^ n := by
          rw [ref.expandedGateCount_reexpand lists]
          exact (hN₀ L).trans (mul_le_mul_of_nonneg_right
            ((le_max_left _ _).trans (le_add_of_nonneg_left zero_le_one)) (by positivity))
        ∃ (B : ℝ≥0) (_ : 1 ≤ B)
          (hb : w.IsExpansionBounded r (B : ℝ))
          (happrox : w.IsGateApproximation ((size L) ^ q)⁻¹ G),
        let ε := ((size L) ^ t)⁻¹
        let hε : 0 < ε := by positivity
        let hbudget : w.IsGateApproximation
            (sourceGateBudget (ε / 2) w.expandedGateCount) G := by
          have hprecision : w.IsGateApproximation
              ((size L) ^ (n + ⌈(t : ℝ)⌉₊ + ⌈16 * countC⌉₊))⁻¹ G := by
            simpa only [Nat.ceil_natCast] using happrox
          simpa only [Real.rpow_neg (by linarith [hsize L] : 0 ≤ (size L)),
            Real.rpow_natCast] using
            w.isGateApproximation_budget_of_power_bound G (size L) countC (t : ℝ)
              w.expandedGateCount n (hsize L) (by dsimp [countC]; linarith [le_max_right C_N 0])
              hNre hprecision
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
              C.physicalDensity) ≤ (size L) ^ (-p) ∧
          (∀ e : DistributedOperatorContraction.Link
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
            (Fintype.card (DistributedOperatorContraction.alphabet
              (Finset.univ : Finset R.nonemptyGateLocations)
              (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R)
              (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k e) : ℝ) ≤ C_p * (size L) ^ α) ∧
          (∀ j, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) j).card ≤
              2 * b * (b - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link
            (Finset.univ : Finset R.nonemptyGateLocations)
            (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R),
            ∀ j l, j ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
              l ∈ distributedLinkParties (SourceCircuit.sourceGateRoot R) e.1 →
              ∃ g : ref.gateLocations, j ∈ ref.participants g ∧ l ∈ ref.participants g) := by
  intro countC t q
  obtain ⟨r, C_K, C_C, u, v, hLists⟩ := hExpansionAvailability q
  exact ⟨r, compressionPrefactor r b C_N C_D C_K C_C, compressionExponent r b n d u v p,
    (compressionPrefactor_pos r b C_N C_D C_K C_C).le, compressionExponent_pos r b n d u v hp,
    uniform_approximate_sampled_network_of_le size hsize P C₀ b n d C_N C_D hN₀ hphysical₀
      harity₀ hlifetime₀ r C_K C_C u v p hLists le_rfl le_rfl⟩

end TNLean.PEPS.PairEffect.GateMapConstruction
