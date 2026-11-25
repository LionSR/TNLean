/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.Construction
import TNLean.Network.SampledApproximation.UniformApproximateSampledNetwork

/-!
# Compression of the actual density of a distributed construction

A distributed construction carries its gates together with their actual monomial expansions.
Its gate operators are the sums of those expansions. Reading each gate as that operator gives
a construction with prescribed gate operators, with the same input, local operations,
participating sets, physical outputs and physical density. Each expansion is exact, so it
serves at every inverse-power accuracy, and the compression theorem (Theorem 5.2) applies to
a family of distributed constructions with the uniform bounds of its statement. The expansions
of a distributed construction consist of allowed monomials and carry no messages, so this is
the case of Theorem 5.2 without messages; the case with messages is
`GateMapConstruction.exists_uniform_message_sampled_network`.

The output is a literal operator tensor network `σ`: one node per party, finite virtual
links with uniformly polynomial alphabets, a constant bound on the number of links at a party,
and every link joining two parties of a common original nonprivate gate. It satisfies
`‖σ - ρ‖₁ ≤ L⁻ᵖ` for the actual, possibly subnormalized, physical density `ρ`. Remark 5.3
then combines this absolute error with a separately proved bound `‖ρ - |Ω⟩⟨Ω|‖₁ ≤ η`:
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ L⁻ᵖ + η` and `1 - η ≤ Re Tr ρ ≤ 1`. Nothing is renormalized, `σ` need be
neither positive nor Hermitian, and no bound on discarded dimensions or Schmidt ranks enters.

The exterior scalar is absorbed at an existing party: the construction data carry the
nonempty-party convention, a degenerate-case reading of the source recorded in
`docs/paper-gaps/polypeps_nonempty_parties.tex` and marked on the QICLean structure
`DistributedConstructionData`.

## Main results

* `QuantumCircuit.Party.DistributedConstruction.toGateMapConstruction`: a distributed
  construction read with the operators of its own gate expansions.
* `QuantumCircuit.Party.DistributedConstruction.physicalDensity_toGateMapConstruction`:
  this reading keeps the physical density.
* `QuantumCircuit.Party.DistributedConstruction.exists_uniform_sampled_network`:
  the case of Theorem 5.2 without messages, for a family of distributed constructions with
  their actual expansions.
* `QuantumCircuit.Party.DistributedConstruction.exists_uniform_sampled_network_sub_pure_le`:
  Remark 5.3 for that family.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Theorem 5.2 (`thm:compression`),
  `04-compression.tex:137–175`, and Remark 5.3 (`rem:compression-retained-norm`),
  `04-compression.tex:602–611`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression and rem:compression-retained-norm; Theorem 5.2 and Remark 5.3.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
open scoped Matrix NNReal Matrix.Norms.L2Operator

namespace QuantumCircuit.Party
open TNLean.Network ManyBody

variable {P : Type} [DecidableEq P]

namespace EffectCircuit

/-- The operator of every recorded gate occurrence: the sum of its own monomial list.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43. -/
def expansionGateMaps : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : EffectCircuit X Y) → c.GateMaps
  | _, _, _, _, PartyCircuit.done _ => PUnit.unit
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g => WeightedGate.ev g ()
  | _, _, _, _, PartyCircuit.localOp _ _ _ => PUnit.unit
  | _, _, _, _, PartyCircuit.localOps _ => PUnit.unit
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => (expansionGateMaps c, expansionGateMaps c')

/-- The monomial list already recorded at every gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43 and 590–600. -/
def expansionGateLists : {X Y : P → Type} → (c : EffectCircuit X Y) → c.GateLists
  | _, _, PartyCircuit.done _ => PUnit.unit
  | _, _, PartyCircuit.gate _ _ g => g
  | _, _, PartyCircuit.localOp _ _ _ => PUnit.unit
  | _, _, PartyCircuit.localOps _ => PUnit.unit
  | _, _, PartyCircuit.comp c c' => (expansionGateLists c, expansionGateLists c')

/-- Reexpanding every gate by its own recorded list gives back the circuit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600. -/
theorem reexpand_expansionGateLists : {X Y : P → Type} → (c : EffectCircuit X Y) →
    reexpand c (expansionGateLists c) = c
  | _, _, PartyCircuit.done _ => rfl
  | _, _, PartyCircuit.gate _ _ _ => rfl
  | _, _, PartyCircuit.localOp _ _ _ => rfl
  | _, _, PartyCircuit.localOps _ => rfl
  | _, _, PartyCircuit.comp c c' => by
    change PartyCircuit.comp (reexpand c (expansionGateLists c))
      (reexpand c' (expansionGateLists c')) = _
    rw [reexpand_expansionGateLists c, reexpand_expansionGateLists c']

/-- Reexpanding every gate by its own recorded list keeps the effect-count and coefficient-sum
bounds. Source: polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149 and
199–208. -/
theorem isExpansionBounded_reexpand_expansionGateLists {X Y : P → Type} {r : ℕ} {S : ℝ}
    (c : EffectCircuit X Y) (h : IsExpansionBounded r S c) :
    IsExpansionBounded r S (reexpand c (expansionGateLists c)) := by
  rw [reexpand_expansionGateLists]
  exact h

/-- Reexpanding every gate by its own recorded list keeps the monomial counts.
Source: polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149. -/
theorem monomialCount_reexpand_expansionGateLists_le {X Y : P → Type} {K : ℕ}
    (c : EffectCircuit X Y) (h : ∀ g, c.monomialCount g ≤ K) :
    ∀ g, (reexpand c (expansionGateLists c)).monomialCount g ≤ K := by
  rw [reexpand_expansionGateLists]
  exact h

/-- Evaluation with the sums of the recorded expansions is the operator of the circuit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36. -/
theorem evalWithGateMaps_expansionGateMaps [Fintype P] : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) →
      c.evalWithGateMaps c.expansionGateMaps = c.op WeightedGate.ev
  | _, _, _, _, PartyCircuit.done _ => by
    simp [evalWithGateMaps]
  | _, _, _, _, PartyCircuit.gate _ _ _ => by
    simp [evalWithGateMaps, expansionGateMaps]
    rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _ => rfl
  | _, _, _, _, PartyCircuit.localOps _ => by
    simp [evalWithGateMaps]
  | _, _, _, _, PartyCircuit.comp c c' => by
    change evalWithGateMaps c' (expansionGateMaps c') * evalWithGateMaps c (expansionGateMaps c) = _
    rw [PartyCircuit.op_comp, evalWithGateMaps_expansionGateMaps c,
      evalWithGateMaps_expansionGateMaps c']

/-- Each allowed gate on a cell of not exactly one party is approximated, with any nonnegative
error, by its own recorded expansion, whose sum is its operator.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43 and 590–600. -/
theorem isGateApproximation_reexpand_expansionGateLists {δ : ℝ} (hδ : 0 ≤ δ) :
    {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : EffectCircuit X Y) → c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed →
    c.ForallGate (fun D _ _ _ ↦ D.card ≠ 1) →
      IsGateApproximation δ (reexpand c (expansionGateLists c))
        (reexpandGateMaps c (expansionGateLists c) (expansionGateMaps c))
  | _, _, _, _, PartyCircuit.done _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, hc, hD => ⟨hD, hc.2, hc.1, by
    simp only [expansionGateLists, expansionGateMaps, reexpandGateMaps, sub_self, norm_zero]
    exact hδ⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, hc, _ => hc
  | _, _, _, _, PartyCircuit.localOps _, hc, _ => hc
  | _, _, _, _, PartyCircuit.comp c c', hc, hD =>
    ⟨isGateApproximation_reexpand_expansionGateLists hδ c hc.1 hD.1,
      isGateApproximation_reexpand_expansionGateLists hδ c' hc.2 hD.2⟩

end EffectCircuit

namespace DistributedConstruction

variable [Fintype P] {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  {d : P → ℕ} {V : P → Type} [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)]

/-- A distributed construction read with prescribed gate operators: each nonprivate gate
is the sum of its own recorded monomial expansion. The input, local operations,
participating sets and physical outputs are unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43, 137–151 and
590–600. -/
def toGateMapConstruction (C : DistributedConstruction P X d V) : GateMapConstruction P X d V :=
  { C.toDistributedConstructionData with
    circuit := C.circuit.toEffectCircuit
    gateMaps := C.circuit.toEffectCircuit.expansionGateMaps }

/-- Reading the gates as the sums of their expansions keeps the physical density.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 150–153 and 590–600. -/
theorem physicalDensity_toGateMapConstruction (C : DistributedConstruction P X d V) :
    C.toGateMapConstruction.physicalDensity = C.physicalDensity := by
  rw [DistributedConstruction.physicalDensity, OriginalCircuit.physicalDensity_eq,
    GateMapConstruction.physicalDensity, EffectCircuit.physicalDensityWithGateMaps]
  rw [show C.toGateMapConstruction.circuit.evalWithGateMaps C.toGateMapConstruction.gateMaps =
      C.circuit.op from
    (EffectCircuit.evalWithGateMaps_expansionGateMaps _).trans C.circuit.op_toEffectCircuit]
  rfl

attribute [local instance] Classical.propDecidable

/-- **Theorem 5.2 without messages, from coefficient-sum bounds.** Under the hypotheses of
`exists_uniform_sampled_network`, with the termwise coefficient bound replaced by the absolute
coefficient-sum bound `C_S * size L ^ s` at every nonprivate gate, every member of the family
admits a literal operator tensor network within `size L ^ (-p)` of its physical density, whose
link alphabets are at most `C_p * size L ^ α` for every
`C_p ≥ sumCompressionPrefactor r b C_N C_D C_K C_S` and every
`α ≥ sampledNetworkExponent r b n d u s p`. The incidence and link-locality bounds are those of
the compression theorem.
Source: polynomial-PEPS Theorem 5.2 (`thm:compression`), `04-compression.tex`, lines
137–175, 199–208 and 565–588. -/
theorem uniform_sampled_network_of_sum_le
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)] [∀ L, DecidableEq (P L)]
    (X : ∀ L, P L → Type) [∀ L j, Fintype (X L j)] [∀ L j, DecidableEq (X L j)]
    (physicalDim : ∀ L, P L → ℕ)
    (V : ∀ L, P L → Type) [∀ L j, Fintype (V L j)] [∀ L j, DecidableEq (V L j)]
    (C₀ : ∀ L, DistributedConstruction (P L) (X L) (physicalDim L) (V L))
    (b n d r u s : ℕ) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, (physicalDim L j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participation j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (hexpansion₀ : ∀ L, (C₀ L).circuit.IsExpansionBounded r (C_S * size L ^ s))
    (p : ℝ) {C_p : ℝ} {α : ℕ}
    (hC : sumCompressionPrefactor r b C_N C_D C_K C_S ≤ C_p)
    (hα : sampledNetworkExponent r b n d u s p ≤ α) :
    ∀ L,
    ∃ (Gate : Type) (_ : Fintype Gate) (_ : DecidableEq Gate)
      (participants : Gate → Finset (P L)) (root : Gate → P L)
      (hroot : ∀ g ∈ (Finset.univ : Finset Gate), root g ∈ participants g)
      (Label : Gate → Type) (_ : ∀ g, Fintype (Label g)) (k : ℕ)
      (c : (g : Gate) → Label g → ℂ)
      (T : (j : P L) → DistributedOperatorContraction.GateLabelsAt
          (Finset.univ : Finset Gate) participants Label j →
        (DistributedOperatorContraction.SampleAt (Finset.univ : Finset Gate)
          participants j → Fin k) →
        Matrix (Fin (physicalDim L j)) (Fin (physicalDim L j)) ℂ),
      Matrix.rectangularTraceNorm
          (DistributedOperatorContraction.contractedOperator Finset.univ participants root
            hroot Label k c T - (C₀ L).physicalDensity) ≤ size L ^ (-p) ∧
        (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
          (Fintype.card (DistributedOperatorContraction.alphabet Finset.univ participants
            root Label k e) : ℝ) ≤ C_p * size L ^ α) ∧
        (∀ j, (incidentDistributedLinks Finset.univ participants root j).card ≤
          2 * b * (b - 1)) ∧
        (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
          ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
            ∃ g : (C₀ L).circuit.nonprivateLocations,
              j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) := by
  have hsize0 : ∀ L, 0 ≤ size L := fun L ↦ (by norm_num : (0 : ℝ) ≤ 2).trans (hsize L)
  have hfamily :=
    GateMapConstruction.uniform_approximate_sampled_network_of_sum_le size hsize P X physicalDim
      V (fun L ↦ (C₀ L).toGateMapConstruction) b n d C_N C_D
      (fun L ↦ by
        change ((C₀ L).circuit.toEffectCircuit.numGates : ℝ) ≤ _
        rw [OriginalCircuit.numGates_toEffectCircuit]
        exact hN₀ L)
      hphysical₀
      (fun L g ↦ by
        change ((C₀ L).circuit.toEffectCircuit.participants g).card ≤ b
        rw [← (C₀ L).circuit.toEffectCircuitLocationsEquiv.apply_symm_apply g,
          OriginalCircuit.participants_toEffectCircuitLocationsEquiv]
        exact harity₀ L _)
      (fun L j ↦ by
        change (C₀ L).circuit.toEffectCircuit.participationCount j ≤ b
        rw [← PartyCircuit.participation_eq_participationCount j (C₀ L).circuit.toEffectCircuit
          (PartyCircuit.forallGate_card_ne_one_mapGates _),
          OriginalCircuit.participation_toEffectCircuit]
        exact hlifetime₀ L j)
      r C_K C_S u s p
      (fun L ↦ by
        obtain ⟨K, hK, hKb⟩ := hmonomial₀ L
        exact ⟨(C₀ L).circuit.toEffectCircuit.expansionGateLists, K,
          EffectCircuit.isExpansionBounded_reexpand_expansionGateLists _ (hexpansion₀ L),
          EffectCircuit.monomialCount_reexpand_expansionGateLists_le _
            ((C₀ L).circuit.monomialCount_toEffectCircuit_le_of_isMonomialBounded hK),
          hKb,
          (C₀ L).circuit.toEffectCircuit.isGateApproximation_reexpand_expansionGateLists
            (inv_nonneg.mpr (pow_nonneg (hsize0 L) _))
            (C₀ L).circuit.isAllowed_toEffectCircuit
            (PartyCircuit.forallGate_card_ne_one_mapGates _)⟩)
      hC hα
  intro L
  obtain ⟨lists, B, hB, hb, happrox, T, herror, hdim, hinc, hlocal⟩ := hfamily L
  rw [physicalDensity_toGateMapConstruction] at herror
  refine ⟨_, _, _, _, _, _, _, _, _, _, T, herror, hdim, hinc, ?_⟩
  intro e j l hj hl
  obtain ⟨g, hjg, hlg⟩ := hlocal e j l hj hl
  change (C₀ L).circuit.toEffectCircuit.gateLocations at g
  change j ∈ (C₀ L).circuit.toEffectCircuit.participants g at hjg
  change l ∈ (C₀ L).circuit.toEffectCircuit.participants g at hlg
  refine ⟨(C₀ L).circuit.toEffectCircuitLocationsEquiv.symm g, ?_⟩
  rw [← OriginalCircuit.participants_toEffectCircuitLocationsEquiv, Equiv.apply_symm_apply]
  exact ⟨hjg, hlg⟩

/-- **Theorem 5.2 without messages, with explicit constants.** Under the hypotheses of
`exists_uniform_sampled_network`, every member of the family admits a literal operator tensor
network within `size L ^ (-p)` of its physical density, whose link alphabets are at most
`C_p * size L ^ α` for every `C_p ≥ compressionPrefactor r b C_N C_D C_K C_C` and every
`α ≥ compressionExponent r b n d u v p`. The incidence and link-locality bounds are those of
the compression theorem.
Source: polynomial-PEPS Theorem 5.2 (`thm:compression`), `04-compression.tex`, lines
137–175 and 565–588. -/
theorem uniform_sampled_network_of_le
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)] [∀ L, DecidableEq (P L)]
    (X : ∀ L, P L → Type) [∀ L j, Fintype (X L j)] [∀ L j, DecidableEq (X L j)]
    (physicalDim : ∀ L, P L → ℕ)
    (V : ∀ L, P L → Type) [∀ L j, Fintype (V L j)] [∀ L j, DecidableEq (V L j)]
    (C₀ : ∀ L, DistributedConstruction (P L) (X L) (physicalDim L) (V L))
    (b n d r u v : ℕ) (C_N C_D C_K C_C : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, (physicalDim L j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participation j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (htermwise₀ : ∀ L, (C₀ L).circuit.IsTermwiseBounded r (C_C * size L ^ v))
    (p : ℝ) {C_p : ℝ} {α : ℕ}
    (hC : compressionPrefactor r b C_N C_D C_K C_C ≤ C_p)
    (hα : compressionExponent r b n d u v p ≤ α) :
    ∀ L,
    ∃ (Gate : Type) (_ : Fintype Gate) (_ : DecidableEq Gate)
      (participants : Gate → Finset (P L)) (root : Gate → P L)
      (hroot : ∀ g ∈ (Finset.univ : Finset Gate), root g ∈ participants g)
      (Label : Gate → Type) (_ : ∀ g, Fintype (Label g)) (k : ℕ)
      (c : (g : Gate) → Label g → ℂ)
      (T : (j : P L) → DistributedOperatorContraction.GateLabelsAt
          (Finset.univ : Finset Gate) participants Label j →
        (DistributedOperatorContraction.SampleAt (Finset.univ : Finset Gate)
          participants j → Fin k) →
        Matrix (Fin (physicalDim L j)) (Fin (physicalDim L j)) ℂ),
      Matrix.rectangularTraceNorm
          (DistributedOperatorContraction.contractedOperator Finset.univ participants root
            hroot Label k c T - (C₀ L).physicalDensity) ≤ size L ^ (-p) ∧
        (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
          (Fintype.card (DistributedOperatorContraction.alphabet Finset.univ participants
            root Label k e) : ℝ) ≤ C_p * size L ^ α) ∧
        (∀ j, (incidentDistributedLinks Finset.univ participants root j).card ≤
          2 * b * (b - 1)) ∧
        (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
          ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
            ∃ g : (C₀ L).circuit.nonprivateLocations,
              j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) :=
  uniform_sampled_network_of_sum_le size hsize P X physicalDim V C₀ b n d r u (u + v) C_N C_D
    C_K (max C_K 0 * max C_C 0) hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀
    (fun L ↦ by
      obtain ⟨K, hK, hKb⟩ := hmonomial₀ L
      have hL0 : 0 ≤ size L := by linarith [hsize L]
      exact (C₀ L).circuit.isExpansionBounded_of_termwise_power_bounds (size L) (max C_K 0)
        (max C_C 0) u v hL0 (le_max_right _ _) hK
        (EffectCircuit.IsTermwiseBounded.mono_coefficient (htermwise₀ L)
          (mul_pow_le_max_zero_mul_pow C_C hL0 v))
        (hKb.trans (mul_pow_le_max_zero_mul_pow C_K hL0 u)))
    p (by rwa [compressionPrefactor_eq_sumCompressionPrefactor] at hC) hα

/-- **Theorem 5.2 without messages, for distributed constructions.** Consider a
family of distributed constructions, indexed by `ι` with sizes `size L ≥ 2`, whose nonprivate
gate count and physical dimensions are uniformly polynomial, whose nonprivate gates have at
most `b` participants, whose parties participate in at most `b` nonprivate gates over the
whole construction, and whose gate expansions have uniformly polynomially many monomials,
at most `r` pair effects per monomial and uniformly polynomially bounded coefficients. Then
for every `p > 0` there are constants, chosen before the family member, such that every
member admits a literal operator tensor network `σ`, with one node per party and the physical
ket and bra legs of that party, satisfying `‖σ - ρ‖₁ ≤ size L ^ (-p)` for the actual physical
density `ρ`. Its link alphabets are uniformly polynomial, each party meets at most
`2 b (b - 1)` links, and each link joins two parties of a common original nonprivate gate.

The actual expansions are exact, so they serve at every inverse-power accuracy. The constants
are `compressionPrefactor r b C_N C_D C_K C_C` and `compressionExponent r b n d u v p`, as in
`uniform_sampled_network_of_le`.
Source: polynomial-PEPS Theorem 5.2 (`thm:compression`), `04-compression.tex`, lines
137–175. -/
theorem exists_uniform_sampled_network
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)] [∀ L, DecidableEq (P L)]
    (X : ∀ L, P L → Type) [∀ L j, Fintype (X L j)] [∀ L j, DecidableEq (X L j)]
    (physicalDim : ∀ L, P L → ℕ)
    (V : ∀ L, P L → Type) [∀ L j, Fintype (V L j)] [∀ L j, DecidableEq (V L j)]
    (C₀ : ∀ L, DistributedConstruction (P L) (X L) (physicalDim L) (V L))
    (b n d r u v : ℕ) (C_N C_D C_K C_C : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, (physicalDim L j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participation j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (htermwise₀ : ∀ L, (C₀ L).circuit.IsTermwiseBounded r (C_C * size L ^ v))
    (p : ℝ) (hp : 0 < p) :
    ∃ (C_p : ℝ) (α : ℕ), 0 ≤ C_p ∧ 0 < α ∧ ∀ L,
      ∃ (Gate : Type) (_ : Fintype Gate) (_ : DecidableEq Gate)
        (participants : Gate → Finset (P L)) (root : Gate → P L)
        (hroot : ∀ g ∈ (Finset.univ : Finset Gate), root g ∈ participants g)
        (Label : Gate → Type) (_ : ∀ g, Fintype (Label g)) (k : ℕ)
        (c : (g : Gate) → Label g → ℂ)
        (T : (j : P L) → DistributedOperatorContraction.GateLabelsAt
            (Finset.univ : Finset Gate) participants Label j →
          (DistributedOperatorContraction.SampleAt (Finset.univ : Finset Gate)
            participants j → Fin k) →
          Matrix (Fin (physicalDim L j)) (Fin (physicalDim L j)) ℂ),
        Matrix.rectangularTraceNorm
            (DistributedOperatorContraction.contractedOperator Finset.univ participants root
              hroot Label k c T - (C₀ L).physicalDensity) ≤ size L ^ (-p) ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            (Fintype.card (DistributedOperatorContraction.alphabet Finset.univ participants
              root Label k e) : ℝ) ≤ C_p * size L ^ α) ∧
          (∀ j, (incidentDistributedLinks Finset.univ participants root j).card ≤
            2 * b * (b - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
              ∃ g : (C₀ L).circuit.nonprivateLocations,
                j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) :=
  ⟨compressionPrefactor r b C_N C_D C_K C_C, compressionExponent r b n d u v p,
    (compressionPrefactor_pos r b C_N C_D C_K C_C).le, compressionExponent_pos r b n d u v hp,
    uniform_sampled_network_of_le size hsize P X physicalDim V C₀ b n d r u v C_N C_D C_K C_C hN₀
      hphysical₀
      harity₀ hlifetime₀ hmonomial₀ htermwise₀ p le_rfl le_rfl⟩

/-- **Remark 5.3 for a family of distributed constructions.** Under the hypotheses of the
compression theorem, suppose that the actual physical density `ρ_L` of every member lies within
`η_L` in trace norm of the pure state of a unit vector `Ω_L`. Then for every `p > 0` there are
constants, chosen before the family member, such that every member admits a literal operator
tensor network `σ_L` with the resource bounds of the compression theorem and
`‖σ_L - |Ω_L⟩⟨Ω_L|‖₁ ≤ size L ^ (-p) + η_L`, while the retained norm satisfies
`1 - η_L ≤ Re Tr ρ_L ≤ 1`. The density `ρ_L` is not renormalized, and `σ_L` need be neither
positive nor Hermitian. No bound on private dimensions or Schmidt ranks is assumed.
Source: polynomial-PEPS Remark 5.3 (`rem:compression-retained-norm`), `04-compression.tex`,
lines 602–611, with Theorem 5.2, lines 137–175. -/
theorem exists_uniform_sampled_network_sub_pure_le
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)] [∀ L, DecidableEq (P L)]
    (X : ∀ L, P L → Type) [∀ L j, Fintype (X L j)] [∀ L j, DecidableEq (X L j)]
    (physicalDim : ∀ L, P L → ℕ)
    (V : ∀ L, P L → Type) [∀ L j, Fintype (V L j)] [∀ L j, DecidableEq (V L j)]
    (C₀ : ∀ L, DistributedConstruction (P L) (X L) (physicalDim L) (V L))
    (b n d r u v : ℕ) (C_N C_D C_K C_C : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, (physicalDim L j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participation j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (htermwise₀ : ∀ L, (C₀ L).circuit.IsTermwiseBounded r (C_C * size L ^ v))
    (Ω : ∀ L, EuclideanSpace ℂ ((j : P L) → Fin (physicalDim L j)))
    (hΩ : ∀ L, ‖Ω L‖ = 1) (η : ι → ℝ)
    (hpure : ∀ L, Matrix.rectangularTraceNorm
      ((C₀ L).physicalDensity - Matrix.euclideanOuterProduct (Ω L) (Ω L)) ≤ η L)
    (p : ℝ) (hp : 0 < p) :
    ∃ (C_p : ℝ) (α : ℕ), 0 ≤ C_p ∧ 0 < α ∧ ∀ L,
      ∃ (Gate : Type) (_ : Fintype Gate) (_ : DecidableEq Gate)
        (participants : Gate → Finset (P L)) (root : Gate → P L)
        (hroot : ∀ g ∈ (Finset.univ : Finset Gate), root g ∈ participants g)
        (Label : Gate → Type) (_ : ∀ g, Fintype (Label g)) (k : ℕ)
        (c : (g : Gate) → Label g → ℂ)
        (T : (j : P L) → DistributedOperatorContraction.GateLabelsAt
            (Finset.univ : Finset Gate) participants Label j →
          (DistributedOperatorContraction.SampleAt (Finset.univ : Finset Gate)
            participants j → Fin k) →
          Matrix (Fin (physicalDim L j)) (Fin (physicalDim L j)) ℂ),
        Matrix.rectangularTraceNorm
            (DistributedOperatorContraction.contractedOperator Finset.univ participants root
              hroot Label k c T - Matrix.euclideanOuterProduct (Ω L) (Ω L)) ≤
            size L ^ (-p) + η L ∧
          Matrix.rectangularTraceNorm
            (DistributedOperatorContraction.contractedOperator Finset.univ participants root
              hroot Label k c T - (C₀ L).physicalDensity) ≤ size L ^ (-p) ∧
          1 - η L ≤ (C₀ L).physicalDensity.trace.re ∧
          (C₀ L).physicalDensity.trace.re ≤ 1 ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            (Fintype.card (DistributedOperatorContraction.alphabet Finset.univ participants
              root Label k e) : ℝ) ≤ C_p * size L ^ α) ∧
          (∀ j, (incidentDistributedLinks Finset.univ participants root j).card ≤
            2 * b * (b - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
              ∃ g : (C₀ L).circuit.nonprivateLocations,
                j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) := by
  obtain ⟨C_p, α, hC, hα, hfamily⟩ := exists_uniform_sampled_network size hsize P X physicalDim V C₀
    b n d r u v C_N C_D C_K C_C hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀ htermwise₀ p hp
  refine ⟨C_p, α, hC, hα, fun L ↦ ?_⟩
  obtain ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    herror, hdim, hinc, hlocal⟩ := hfamily L
  obtain ⟨hσ, hlow, hhigh⟩ := (C₀ L).rectangularTraceNorm_compression_sub_pure_le
    _ (Ω L) (hΩ L) herror (hpure L)
  exact ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    hσ, herror, hlow, hhigh, hdim, hinc, hlocal⟩

end DistributedConstruction

end QuantumCircuit.Party
