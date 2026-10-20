/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.CompressionRetainedNorm
import TNLean.Lattice.Compression.UniformApproximateSampledNetwork

/-!
# Compression of the actual density of a distributed construction

A distributed construction carries its gates together with their actual monomial expansions.
Its gate operators are the sums of those expansions. Reading each gate as that operator gives
a construction with prescribed gate operators, with the same input, private operations,
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
neither positive nor Hermitian, and no bound on private dimensions or Schmidt ranks enters.

The exterior scalar is absorbed at an existing party: the construction data carry the
nonempty-party convention, a degenerate-case reading of the source recorded in
`docs/paper-gaps/polypeps_nonempty_parties.tex` and marked on `DistributedConstruction`.

## Main results

* `TNLean.PEPS.PairEffect.DistributedConstruction.toGateMapConstruction`: a distributed
  construction read with the operators of its own gate expansions.
* `TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity_toGateMapConstruction`:
  this reading keeps the physical density.
* `TNLean.PEPS.PairEffect.DistributedConstruction.exists_uniform_sampled_network`:
  the case of Theorem 5.2 without messages, for a family of distributed constructions with
  their actual expansions.
* `TNLean.PEPS.PairEffect.DistributedConstruction.exists_uniform_sampled_network_sub_pure_le`:
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
open scoped Matrix NNReal

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace EffectCircuit

/-- The operator of every recorded gate occurrence: the sum of its own monomial list.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43. -/
def expansionGateMaps : {a b : Layout P} → (w : EffectCircuit a b) → w.GateMaps
  | _, _, .id _ => PUnit.unit
  | _, _, .comp w v => (expansionGateMaps w, expansionGateMaps v)
  | _, _, .localMap .. => PUnit.unit
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ L _ => PairEffect.gate (toGate L)
  | _, _, .swap .. => PUnit.unit
  | _, _, .frame _ w => expansionGateMaps w

/-- The monomial list already recorded at every gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43 and 590–600. -/
def expansionGateLists : {a b : Layout P} → (w : EffectCircuit a b) → w.GateLists
  | _, _, .id _ => PUnit.unit
  | _, _, .comp w v => (expansionGateLists w, expansionGateLists v)
  | _, _, .localMap .. => PUnit.unit
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ L _ => L
  | _, _, .swap .. => PUnit.unit
  | _, _, .frame _ w => expansionGateLists w

/-- Evaluation with the sums of the recorded expansions is the evaluation of the circuit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36. -/
theorem evalWithGateMaps_expansionGateMaps {a b : Layout P} (w : EffectCircuit a b) :
    w.evalWithGateMaps w.expansionGateMaps = w.eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv => exact congrArg₂ ContinuousLinearMap.comp ihv ihw
  | localMap => rfl
  | gate => rfl
  | swap => rfl
  | frame r w ih => exact congrArg (fun A ↦ A.lTensor r.space) ih

end EffectCircuit

namespace OriginalCircuit

variable {a b : Layout P}

/-- Termwise bounds are monotone in the coefficient bound.
Source: polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149. -/
theorem IsTermwiseBounded.mono {w : OriginalCircuit a b} {r : ℕ} {C C' : ℝ}
    (h : w.IsTermwiseBounded r C) (hC : C ≤ C') : w.IsTermwiseBounded r C' := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate => exact fun term hterm ↦ ⟨(h term hterm).1, (h term hterm).2.trans hC⟩
  | swap => trivial
  | frame r w ih => exact ih h

/-- Each original gate is approximated, with any nonnegative error, by its own recorded
expansion, whose sum is its operator.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43 and 590–600. -/
theorem isGateApproximation_reexpand_expansionGateLists (w : OriginalCircuit a b) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (w.produce.reexpand w.produce.expansionGateLists).IsGateApproximation δ
      (w.produce.reexpandGateMaps w.produce.expansionGateLists
        w.produce.expansionGateMaps) := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw, ihv⟩
  | privateMap p ha hb A hA tail => exact hA
  | nonprivateGate owner hC L hL hG tail =>
      refine ⟨hC, hL, hG, ?_⟩
      change ‖PairEffect.gate (toGate L) - PairEffect.gate (toGate L)‖ ≤ δ
      simpa only [sub_self, norm_zero] using hδ
  | swap => trivial
  | frame r w ih => exact ih

/-- The recorded expansions keep the original termwise bounds.
Source: polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149. -/
theorem isTermwiseBounded_reexpand_expansionGateLists (w : OriginalCircuit a b) {r : ℕ}
    {C : ℝ} (h : w.IsTermwiseBounded r C) :
    (w.produce.reexpand w.produce.expansionGateLists).IsTermwiseBounded r C := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate => exact h
  | swap => trivial
  | frame r w ih => exact ih h

/-- The recorded expansions keep the original effect-count and coefficient-sum bounds.
Source: polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149 and 199–208. -/
theorem isExpansionBounded_reexpand_expansionGateLists (w : OriginalCircuit a b) {r : ℕ}
    {S : ℝ} (h : w.IsExpansionBounded r S) :
    (w.produce.reexpand w.produce.expansionGateLists).IsExpansionBounded r S := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate => exact h
  | swap => trivial
  | frame r w ih => exact ih h

/-- The recorded expansions keep the original monomial counts.
Source: polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149. -/
theorem monomialCount_reexpand_expansionGateLists_le (w : OriginalCircuit a b) {K : ℕ}
    (h : w.IsMonomialBounded K) :
    ∀ g, (w.produce.reexpand w.produce.expansionGateLists).monomialCount g ≤ K := by
  induction w with
  | id => intro g; exact nomatch g
  | comp w v ihw ihv =>
      rintro (g | g)
      · exact ihw h.1 g
      · exact ihv h.2 g
  | privateMap => intro g; exact nomatch g
  | nonprivateGate => intro _; exact h
  | swap => intro g; exact nomatch g
  | frame r w ih => exact ih h

/-- The produced chronology has the whole-lifetime participation counts of the original one.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 140–142 and 229. -/
theorem natCard_participation_produce (w : OriginalCircuit a b) (p : P) :
    Nat.card {g : w.produce.gateLocations // p ∈ w.produce.participants g} =
      w.participationCount p :=
  (Nat.card_congr (w.produceLocationsEquiv.subtypeEquiv fun g ↦ by
    rw [w.participants_produce])).symm

end OriginalCircuit

namespace DistributedConstruction

variable [Fintype P]

/-- A distributed construction read with prescribed gate operators: each nonprivate gate
is the sum of its own recorded monomial expansion. The input, private operations,
participating sets and physical outputs are unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43, 137–151 and
590–600. -/
def toGateMapConstruction (C : DistributedConstruction P) : GateMapConstruction P :=
  { C.toDistributedConstructionData with
    circuit := C.circuit.produce
    gateMaps := C.circuit.produce.expansionGateMaps }

/-- Reading the gates as the sums of their expansions keeps the physical density.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 150–153 and 590–600. -/
theorem physicalDensity_toGateMapConstruction (C : DistributedConstruction P) :
    C.toGateMapConstruction.physicalDensity = C.physicalDensity := by
  have h : C.toGateMapConstruction.circuit.evalWithGateMaps C.toGateMapConstruction.gateMaps =
      C.circuit.eval := by
    change C.circuit.produce.evalWithGateMaps C.circuit.produce.expansionGateMaps = _
    rw [EffectCircuit.evalWithGateMaps_expansionGateMaps, OriginalCircuit.eval_produce]
  unfold GateMapConstruction.physicalDensity physicalDensity
    EffectCircuit.physicalDensityWithGateMaps
  rw [h]
  rfl

end DistributedConstruction

end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect.DistributedConstruction
open TNLean.PEPS.Approximation
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
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, DistributedConstruction (P L))
    (b n d r u s : ℕ) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ b)
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
        Matrix (Fin ((C₀ L).physicalDimension j)) (Fin ((C₀ L).physicalDimension j)) ℂ),
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
    GateMapConstruction.uniform_approximate_sampled_network_of_sum_le size hsize P
      (fun L ↦ (C₀ L).toGateMapConstruction) b n d C_N C_D
      (fun L ↦ by
        change ((C₀ L).circuit.produce.expandedGateCount : ℝ) ≤ _
        rw [OriginalCircuit.expandedGateCount_produce]
        exact hN₀ L)
      hphysical₀
      (fun L g ↦ by
        change ((C₀ L).circuit.produce.participants g).card ≤ b
        rw [← (C₀ L).circuit.produceLocationsEquiv.apply_symm_apply g,
          OriginalCircuit.participants_produce]
        exact harity₀ L _)
      (fun L j ↦ by
        change Nat.card {g : (C₀ L).circuit.produce.gateLocations //
          j ∈ (C₀ L).circuit.produce.participants g} ≤ b
        rw [OriginalCircuit.natCard_participation_produce]
        exact hlifetime₀ L j)
      r C_K C_S u s p
      (fun L ↦ by
        obtain ⟨K, hK, hKb⟩ := hmonomial₀ L
        exact ⟨(C₀ L).circuit.produce.expansionGateLists, K,
          (C₀ L).circuit.isExpansionBounded_reexpand_expansionGateLists (hexpansion₀ L),
          (C₀ L).circuit.monomialCount_reexpand_expansionGateLists_le hK, hKb,
          (C₀ L).circuit.isGateApproximation_reexpand_expansionGateLists
            (inv_nonneg.mpr (pow_nonneg (hsize0 L) _))⟩)
      hC hα
  intro L
  obtain ⟨lists, B, hB, hb, happrox, T, herror, hdim, hinc, hlocal⟩ := hfamily L
  rw [physicalDensity_toGateMapConstruction] at herror
  refine ⟨_, _, _, _, _, _, _, _, _, _, T, herror, hdim, hinc, ?_⟩
  intro e j l hj hl
  obtain ⟨g, hjg, hlg⟩ := hlocal e j l hj hl
  change (C₀ L).circuit.produce.gateLocations at g
  change j ∈ (C₀ L).circuit.produce.participants g at hjg
  change l ∈ (C₀ L).circuit.produce.participants g at hlg
  refine ⟨(C₀ L).circuit.produceLocationsEquiv.symm g, ?_⟩
  rw [← OriginalCircuit.participants_produce, Equiv.apply_symm_apply]
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
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, DistributedConstruction (P L))
    (b n d r u v : ℕ) (C_N C_D C_K C_C : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ b)
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
        Matrix (Fin ((C₀ L).physicalDimension j)) (Fin ((C₀ L).physicalDimension j)) ℂ),
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
  uniform_sampled_network_of_sum_le size hsize P C₀ b n d r u (u + v) C_N C_D C_K
    (max C_K 0 * max C_C 0) hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀
    (fun L ↦ by
      obtain ⟨K, hK, hKb⟩ := hmonomial₀ L
      have hL0 : 0 ≤ size L := by linarith [hsize L]
      exact (C₀ L).circuit.isExpansionBounded_of_termwise_power_bounds (size L) (max C_K 0)
        (max C_C 0) u v hL0 (le_max_right _ _) hK
        ((htermwise₀ L).mono (mul_pow_le_max_zero_mul_pow C_C hL0 v))
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
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, DistributedConstruction (P L))
    (b n d r u v : ℕ) (C_N C_D C_K C_C : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ b)
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
          Matrix (Fin ((C₀ L).physicalDimension j)) (Fin ((C₀ L).physicalDimension j)) ℂ),
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
    uniform_sampled_network_of_le size hsize P C₀ b n d r u v C_N C_D C_K C_C hN₀ hphysical₀
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
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, DistributedConstruction (P L))
    (b n d r u v : ℕ) (C_N C_D C_K C_C : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ b)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (htermwise₀ : ∀ L, (C₀ L).circuit.IsTermwiseBounded r (C_C * size L ^ v))
    (Ω : ∀ L, EuclideanSpace ℂ ((j : P L) → Fin ((C₀ L).physicalDimension j)))
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
          Matrix (Fin ((C₀ L).physicalDimension j)) (Fin ((C₀ L).physicalDimension j)) ℂ),
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
  obtain ⟨C_p, α, hC, hα, hfamily⟩ := exists_uniform_sampled_network size hsize P C₀
    b n d r u v C_N C_D C_K C_C hN₀ hphysical₀ harity₀ hlifetime₀ hmonomial₀ htermwise₀ p hp
  refine ⟨C_p, α, hC, hα, fun L ↦ ?_⟩
  obtain ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    herror, hdim, hinc, hlocal⟩ := hfamily L
  obtain ⟨hσ, hlow, hhigh⟩ := (C₀ L).rectangularTraceNorm_compression_sub_pure_le
    _ (Ω L) (hΩ L) herror (hpure L)
  exact ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    hσ, herror, hlow, hhigh, hdim, hinc, hlocal⟩

end TNLean.PEPS.PairEffect.DistributedConstruction
