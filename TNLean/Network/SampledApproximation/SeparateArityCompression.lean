/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.SampledApproximation.DistributedGateMapConstruction

/-!
# Separate participant and participation bounds for sampled density networks

A gate with at most a participants contributes at most 2(a-1) incident
star and pair-sample links at each party. If a party occurs in at most b
gates, its degree is at most 2b(a-1). The occurrence correspondences used
in compression preserve these two bounds separately.

Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:565–588;
one-dimensional note, Part II, proof of Theorem B,
part2b_mps_protocol.tex:594–614.

-/

noncomputable section
open scoped Matrix NNReal

namespace QuantumCircuit.Party
open TNLean.Network ManyBody GateIncidence

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

variable {X Y : P → Type}

open Classical in
/-- The actual source-density network inherits separate participant and
participation bounds from its nonempty gate occurrences.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:140–142,581–588. -/
theorem card_incidentSourceDensityLinks_le_of_arity_lifetime
    (w : SourceCircuit X Y) (arity lifetime : ℕ)
    (harity : ∀ g : w.nonemptyGateLocations, (w.participants g.1).card ≤ arity)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime) (p : P) :
    (incidentDistributedLinks (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w) p).card ≤
        2 * lifetime * (arity - 1) := by
  apply card_incidentDistributedLinks_le_of_arity_lifetime
    (Finset.univ : Finset w.nonemptyGateLocations)
    (fun g ↦ w.participants g.1) (sourceGateRoot w) arity lifetime
    (fun g _ ↦ sourceGateRoot_mem w g) (fun g _ ↦ harity g) p
  rw [card_incidentNonemptyGates_eq_participationCount]
  exact hlifetime p

end SourceCircuit

namespace OriginalCircuit

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

open Classical in
/-- The actual replacement used for the physical density has the original
participant bound and lifetime bound, independently of its precision.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:199–229,581–588. -/
theorem card_incidentPhysicalFirstDensityLinks_le_of_arity_lifetime (w : OriginalCircuit X Y)
    {r arity lifetime : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    (hb : w.IsExpansionBounded r S)
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity)
    (hlifetime : ∀ p, w.participation p ≤ lifetime) :
    let R := w.replacement hδ hb
    ∀ p, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) p).card ≤
        2 * lifetime * (arity - 1) := by
  intro R p
  apply R.card_incidentSourceDensityLinks_le_of_arity_lifetime arity lifetime
  · intro g
    have hpart := w.participants_replacementLocationsEquiv hδ hb
      ((w.replacementLocationsEquiv hδ hb).symm g.1)
    rw [Equiv.apply_symm_apply] at hpart
    exact (congrArg Finset.card hpart).trans_le (harity _)
  · exact w.participationCount_replacement_le hδ hb hlifetime

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Reading an original circuit as its effect circuit keeps the bound
on the number of participants at each gate.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:21–43,590–600. -/
theorem card_participants_toEffectCircuit_le_of_arity
    (w : OriginalCircuit X Y) {arity : ℕ}
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity)
    (g : w.toEffectCircuit.gateLocations) : (w.toEffectCircuit.participants g).card ≤ arity := by
  rw [← w.toEffectCircuitLocationsEquiv.apply_symm_apply g,
    participants_toEffectCircuitLocationsEquiv]
  exact harity _

end OriginalCircuit

namespace DistributedConstruction

attribute [local instance] Classical.propDecidable

/-- Uniform compression with separate participant and lifetime bounds, from an absolute
coefficient-sum bound at every nonprivate gate.
The larger bound b is used for sampling; the same actual sampled network
has incidence at most 2b(a-1). No numerical degree is supplied as a premise.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:137–175,565–600;
one-dimensional note, Part II, thm:B, part2b_mps_protocol.tex:594–614. -/
theorem exists_uniform_sampled_network_of_arity_lifetime
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)] [∀ L, DecidableEq (P L)]
    (X : ∀ L, P L → Type) [∀ L j, Fintype (X L j)] [∀ L j, DecidableEq (X L j)]
    (physicalDim : ∀ L, P L → ℕ)
    (V : ∀ L, P L → Type) [∀ L j, Fintype (V L j)] [∀ L j, DecidableEq (V L j)]
    (C₀ : ∀ L, DistributedConstruction (P L) (X L) (physicalDim L) (V L))
    (a b n d r u s : ℕ) (hab : a ≤ b) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, (physicalDim L j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ a)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participation j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (hexpansion₀ : ∀ L, (C₀ L).circuit.IsExpansionBounded r (C_S * size L ^ s))
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
            2 * b * (a - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
              ∃ g : (C₀ L).circuit.nonprivateLocations,
                j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) := by
  have hsize0 : ∀ L, 0 ≤ size L := fun L ↦ (by norm_num : (0 : ℝ) ≤ 2).trans (hsize L)
  have hlifetime : ∀ L j, (C₀ L).circuit.toEffectCircuit.participationCount j ≤ b := by
    intro L j
    rw [← PartyCircuit.participation_eq_participationCount j (C₀ L).circuit.toEffectCircuit
      (PartyCircuit.forallGate_card_ne_one_mapGates _),
      OriginalCircuit.participation_toEffectCircuit]
    exact hlifetime₀ L j
  have hfamily :=
    GateMapConstruction.uniform_approximate_sampled_network_of_sum_le size hsize P X physicalDim
      V (fun L ↦ (C₀ L).toGateMapConstruction) b n d C_N C_D
      (fun L ↦ by
        change ((C₀ L).circuit.toEffectCircuit.numGates : ℝ) ≤ _
        rw [OriginalCircuit.numGates_toEffectCircuit]
        exact hN₀ L)
      hphysical₀
      (fun L g ↦ ((C₀ L).circuit.card_participants_toEffectCircuit_le_of_arity (harity₀ L)
        g).trans hab)
      hlifetime
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
      le_rfl le_rfl
  refine ⟨sumCompressionPrefactor r b C_N C_D C_K C_S, sampledNetworkExponent r b n d u s p,
    by rw [sumCompressionPrefactor]; exact (sampledNetworkPrefactor_pos _ _ _ _ _ _).le,
    sampledNetworkExponent_pos _ _ _ _ _ _ hp, fun L ↦ ?_⟩
  obtain ⟨lists, B, hB, hb, happrox, T, herror, hdim, _hinc, hlocal⟩ := hfamily L
  rw [physicalDensity_toGateMapConstruction] at herror
  refine ⟨_, _, _, _, _, _, _, _, _, _, T, herror, hdim, ?_, ?_⟩
  · intro j
    apply OriginalCircuit.card_incidentPhysicalFirstDensityLinks_le_of_arity_lifetime
      (arity := a) (lifetime := b)
    · intro g
      rw [EffectCircuit.participants_rescaledOriginal, EffectCircuit.participants_reexpand]
      exact (C₀ L).circuit.card_participants_toEffectCircuit_le_of_arity (harity₀ L) _
    · intro j
      rw [EffectCircuit.participation_rescaledOriginal, PartyCircuit.natCard_participants_mem,
        EffectCircuit.participationCount_reexpand]
      exact hlifetime L j
  · intro e j l hj hl
    obtain ⟨g, hjg, hlg⟩ := hlocal e j l hj hl
    change (C₀ L).circuit.toEffectCircuit.gateLocations at g
    change j ∈ (C₀ L).circuit.toEffectCircuit.participants g at hjg
    change l ∈ (C₀ L).circuit.toEffectCircuit.participants g at hlg
    refine ⟨(C₀ L).circuit.toEffectCircuitLocationsEquiv.symm g, ?_⟩
    rw [← OriginalCircuit.participants_toEffectCircuitLocationsEquiv, Equiv.apply_symm_apply]
    exact ⟨hjg, hlg⟩

/-- The same sampled network approximates a nearby pure state, retaining the
actual separate participant and lifetime incidence bound.
Source: polynomial-PEPS Remark 5.3, 04-compression.tex:602–611, and
one-dimensional note, Part II, thm:B, part2b_mps_protocol.tex:587–614. -/
theorem exists_uniform_sampled_network_sub_pure_le_of_arity_lifetime
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)] [∀ L, DecidableEq (P L)]
    (X : ∀ L, P L → Type) [∀ L j, Fintype (X L j)] [∀ L j, DecidableEq (X L j)]
    (physicalDim : ∀ L, P L → ℕ)
    (V : ∀ L, P L → Type) [∀ L j, Fintype (V L j)] [∀ L j, DecidableEq (V L j)]
    (C₀ : ∀ L, DistributedConstruction (P L) (X L) (physicalDim L) (V L))
    (a b n d r u s : ℕ) (hab : a ≤ b) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, (physicalDim L j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ a)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participation j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (hexpansion₀ : ∀ L, (C₀ L).circuit.IsExpansionBounded r (C_S * size L ^ s))
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
            2 * b * (a - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
              ∃ g : (C₀ L).circuit.nonprivateLocations,
                j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) := by
  obtain ⟨C_p, α, hC, hα, hfamily⟩ :=
    exists_uniform_sampled_network_of_arity_lifetime size hsize P X physicalDim V C₀
      a b n d r u s hab C_N C_D C_K C_S hN₀ hphysical₀ harity₀ hlifetime₀
      hmonomial₀ hexpansion₀ p hp
  refine ⟨C_p, α, hC, hα, fun L ↦ ?_⟩
  obtain ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    herror, hdim, hinc, hlocal⟩ := hfamily L
  obtain ⟨hσ, hlow, hhigh⟩ := (C₀ L).rectangularTraceNorm_compression_sub_pure_le
    _ (Ω L) (hΩ L) herror (hpure L)
  exact ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    hσ, herror, hlow, hhigh, hdim, hinc, hlocal⟩

end DistributedConstruction

end QuantumCircuit.Party
