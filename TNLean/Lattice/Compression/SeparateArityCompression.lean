/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedGateMapConstruction

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

namespace TNLean.PEPS.PairEffect
open TNLean.PEPS.Approximation
variable {P : Type} {input output : Layout P}

namespace SourceCircuit

open Classical in
/-- The actual source-density network inherits separate participant and
participation bounds from its nonempty gate occurrences.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:140–142,581–588. -/
theorem card_incidentSourceDensityLinks_le_of_arity_lifetime
    (w : SourceCircuit input output) (arity lifetime : ℕ)
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

open Classical in
/-- The actual replacement used for the physical density has the original
participant bound and lifetime bound, independently of its precision.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:199–229,581–588. -/
theorem card_incidentPhysicalFirstDensityLinks_le_of_arity_lifetime
    (physical priv : Layout P) (w : OriginalCircuit input (physical ++ priv))
    {r arity lifetime : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    (hb : w.IsExpansionBounded r S)
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)
    ∀ p, (incidentDistributedLinks (Finset.univ : Finset R.nonemptyGateLocations)
      (fun g ↦ R.participants g.1) (SourceCircuit.sourceGateRoot R) p).card ≤
        2 * lifetime * (arity - 1) := by
  intro R p
  apply R.card_incidentSourceDensityLinks_le_of_arity_lifetime arity lifetime
  · intro g
    let E := w.physicalFirstReplacementLocationsEquiv physical priv hδ hb
    have hpart := w.participants_physicalFirstReplacementLocationsEquiv
      physical priv hδ hb (E.symm g.1)
    change R.participants (E (E.symm g.1)) = _ at hpart
    rw [E.apply_symm_apply] at hpart
    exact (congrArg Finset.card hpart).trans_le (harity _)
  · intro q
    exact (SourceCircuit.participationCount_physicalFirstOutput
      (w.produce.auxiliary (stackLength r S δ)) physical priv _ q).trans_le
        (w.participationCount_replacement_le hδ hb hlifetime q)

/-- Reading an original circuit as its recorded expansion keeps the bound
on the number of participants at each gate.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:21–43,590–600. -/
theorem card_participants_produce_le_of_arity
    (w : OriginalCircuit input output) {arity : ℕ}
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity)
    (g : w.produce.gateLocations) : (w.produce.participants g).card ≤ arity := by
  rw [← w.produceLocationsEquiv.apply_symm_apply g, participants_produce]
  exact harity _

end OriginalCircuit
end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect.DistributedConstruction
open TNLean.PEPS.Approximation
attribute [local instance] Classical.propDecidable

/-- Uniform compression with separate participant and lifetime bounds, from an absolute
coefficient-sum bound at every nonprivate gate.
The larger bound b is used for sampling; the same actual sampled network
has incidence at most 2b(a-1). No numerical degree is supplied as a premise.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex:137–175,565–600;
one-dimensional note, Part II, thm:B, part2b_mps_protocol.tex:594–614. -/
theorem exists_uniform_sampled_network_of_arity_lifetime
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, DistributedConstruction (P L))
    (a b n d r u s : ℕ) (hab : a ≤ b) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ a)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ b)
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
          Matrix (Fin ((C₀ L).physicalDimension j)) (Fin ((C₀ L).physicalDimension j)) ℂ),
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
        exact (harity₀ L _).trans hab)
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
    · exact EffectCircuit.isExpansionBounded_rescaledOriginal _ _ _ _ hb
    · intro g
      rw [EffectCircuit.participants_rescaledOriginal, EffectCircuit.participants_reexpand]
      exact OriginalCircuit.card_participants_produce_le_of_arity
        (C₀ L).circuit (harity₀ L) _
    · intro j
      rw [EffectCircuit.participationCount_rescaledOriginal,
        EffectCircuit.participationCount_reexpand]
      change Nat.card {g : (C₀ L).circuit.produce.gateLocations //
        j ∈ (C₀ L).circuit.produce.participants g} ≤ b
      rw [OriginalCircuit.natCard_participation_produce]
      exact hlifetime₀ L j
  · intro e j l hj hl
    obtain ⟨g, hjg, hlg⟩ := hlocal e j l hj hl
    change (C₀ L).circuit.produce.gateLocations at g
    change j ∈ (C₀ L).circuit.produce.participants g at hjg
    change l ∈ (C₀ L).circuit.produce.participants g at hlg
    refine ⟨(C₀ L).circuit.produceLocationsEquiv.symm g, ?_⟩
    rw [← OriginalCircuit.participants_produce, Equiv.apply_symm_apply]
    exact ⟨hjg, hlg⟩

/-- The same sampled network approximates a nearby pure state, retaining the
actual separate participant and lifetime incidence bound.
Source: polynomial-PEPS Remark 5.3, 04-compression.tex:602–611, and
one-dimensional note, Part II, thm:B, part2b_mps_protocol.tex:587–614. -/
theorem exists_uniform_sampled_network_sub_pure_le_of_arity_lifetime
    {ι : Type*} (size : ι → ℝ) (hsize : ∀ i, 2 ≤ size i)
    (P : ι → Type) [∀ L, Fintype (P L)]
    (C₀ : ∀ L, DistributedConstruction (P L))
    (a b n d r u s : ℕ) (hab : a ≤ b) (C_N C_D C_K C_S : ℝ)
    (hN₀ : ∀ L, ((C₀ L).circuit.nonprivateCount : ℝ) ≤ C_N * size L ^ n)
    (hphysical₀ : ∀ L j, ((C₀ L).physicalDimension j : ℝ) ≤ C_D * size L ^ d)
    (harity₀ : ∀ L g, ((C₀ L).circuit.participants g).card ≤ a)
    (hlifetime₀ : ∀ L j, (C₀ L).circuit.participationCount j ≤ b)
    (hmonomial₀ : ∀ L, ∃ K : ℕ, (C₀ L).circuit.IsMonomialBounded K ∧
      (K : ℝ) ≤ C_K * size L ^ u)
    (hexpansion₀ : ∀ L, (C₀ L).circuit.IsExpansionBounded r (C_S * size L ^ s))
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
            2 * b * (a - 1)) ∧
          (∀ e : DistributedOperatorContraction.Link Finset.univ participants root,
            ∀ j l, j ∈ distributedLinkParties root e.1 → l ∈ distributedLinkParties root e.1 →
              ∃ g : (C₀ L).circuit.nonprivateLocations,
                j ∈ (C₀ L).circuit.participants g ∧ l ∈ (C₀ L).circuit.participants g) := by
  obtain ⟨C_p, α, hC, hα, hfamily⟩ :=
    exists_uniform_sampled_network_of_arity_lifetime size hsize P C₀
      a b n d r u s hab C_N C_D C_K C_S hN₀ hphysical₀ harity₀ hlifetime₀
      hmonomial₀ hexpansion₀ p hp
  refine ⟨C_p, α, hC, hα, fun L ↦ ?_⟩
  obtain ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    herror, hdim, hinc, hlocal⟩ := hfamily L
  obtain ⟨hσ, hlow, hhigh⟩ := (C₀ L).rectangularTraceNorm_compression_sub_pure_le
    _ (Ω L) (hΩ L) herror (hpure L)
  exact ⟨Gate, _, _, participants, root, hroot, Label, _, k, c, T,
    hσ, herror, hlow, hhigh, hdim, hinc, hlocal⟩

end TNLean.PEPS.PairEffect.DistributedConstruction
