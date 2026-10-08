/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PhysicalFirstReadout
import TNLean.PEPS.Approximation.SourceCircuitResourceBounds
import TNLean.PEPS.Approximation.DistributedLinks

/-!
# Original incidence bounds for the physical-first network

The source replacement and output exchange retain the original nonprivate gate
occurrences and their participating parties. The actual star and sample links
therefore have bounded incidence and join participants of one original gate.
The statements apply to any retained collection of gate occurrences, including
the collection obtained by excluding gates with no participating party.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 140–142,
199–229 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-message-resources-physicalfirstnetworkresources-01
TNLean.PEPS.PairEffect.OriginalCircuit.card_incidentPhysicalFirstLinks_le
Provenance-ID: 8769-message-resources-physicalfirstnetworkresources-02
TNLean.PEPS.PairEffect.OriginalCircuit.exists_original_gate_of_physicalFirst_link
Provenance-ID: 8769-message-resources-physicalfirstnetworkresources-03
TNLean.PEPS.PairEffect.OriginalCircuit.participants_physicalFirstReplacementLocationsEquiv
Provenance-ID: 8769-message-resources-physicalfirstnetworkresources-04
TNLean.PEPS.PairEffect.OriginalCircuit.physicalFirstReplacementLocationsEquiv
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.OriginalCircuit
open TNLean.PEPS.Approximation
variable {P : Type} {a : Layout P}

/-- The actual gate correspondence from the original chronology to its
physical-first source replacement. -/
def physicalFirstReplacementLocationsEquiv
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) :
    w.nonprivateLocations ≃
      (w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
        ((w.isExpansionBounded_produce_iff r S).mpr hb)).gateLocations :=
  (w.replacementLocationsEquiv hδ hb).trans
    (SourceCircuit.physicalFirstLocationsEquiv (w.produce.auxiliary (stackLength r S δ))
      physical priv _)

/-- The gate correspondence preserves the exact original participating set. -/
theorem participants_physicalFirstReplacementLocationsEquiv
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (g : w.nonprivateLocations) :
    (w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).participants
      (w.physicalFirstReplacementLocationsEquiv physical priv hδ hb g) = w.participants g := by
  exact (SourceCircuit.participants_physicalFirstLocationsEquiv
    (w.produce.auxiliary (stackLength r S δ)) physical priv _ _).trans
      (w.participants_replacementLocationsEquiv hδ hb g)

open Classical in
/-- Each link of the actual replacement network joins two parties that belong
to a single gate occurrence of the original circuit. -/
theorem exists_original_gate_of_physicalFirst_link
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)
    ∀ (gates : Finset R.gateLocations) (root : R.gateLocations → P),
      (∀ g ∈ gates, root g ∈ R.participants g) →
      ∀ e ∈ distributedLinks gates R.participants root, ∀ p q,
        p ∈ distributedLinkParties root e → q ∈ distributedLinkParties root e →
        ∃ g : w.nonprivateLocations, p ∈ w.participants g ∧ q ∈ w.participants g := by
  intro R gates root hroot e he p q hp hq
  obtain ⟨g, _, hp, hq⟩ :=
    exists_common_gate_of_mem_distributedLinkParties gates R.participants root hroot he hp hq
  let E := w.physicalFirstReplacementLocationsEquiv physical priv hδ hb
  refine ⟨E.symm g, ?_⟩
  have hpart := w.participants_physicalFirstReplacementLocationsEquiv
    physical priv hδ hb (E.symm g)
  have heq : R.participants g = w.participants (E.symm g) := by
    change R.participants (E (E.symm g)) = _ at hpart
    rw [E.apply_symm_apply] at hpart
    exact hpart
  exact ⟨heq ▸ hp, heq ▸ hq⟩

open Classical in
/-- Original arity and whole-lifetime participation at most `b` imply the
constant incidence bound `2*b*(b-1)` for the actual replacement links. -/
theorem card_incidentPhysicalFirstLinks_le
    (physical priv : Layout P) (w : OriginalCircuit a (physical ++ priv))
    {r b : ℕ} {S δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (harity : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ b)
    (hlifetime : ∀ p, w.participationCount p ≤ b) :
    let R := w.produce.physicalFirstReplacement hδ physical priv w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)
    ∀ (gates : Finset R.gateLocations) (root : R.gateLocations → P),
      (∀ g ∈ gates, root g ∈ R.participants g) → ∀ p,
      (incidentDistributedLinks gates R.participants root p).card ≤ 2 * b * (b - 1) := by
  intro R gates root hroot p
  apply card_incidentDistributedLinks_le gates R.participants root b hroot
  · intro g _
    obtain ⟨g, rfl⟩ :=
      (w.physicalFirstReplacementLocationsEquiv physical priv hδ hb).surjective g
    exact (congrArg Finset.card
      (w.participants_physicalFirstReplacementLocationsEquiv physical priv hδ hb g)).trans_le
        (harity g)
  · have hsub : incidentGates gates R.participants p ⊆
        incidentGates Finset.univ R.participants p :=
      Finset.filter_subset_filter _ (Finset.subset_univ gates)
    have hl : R.participationCount p ≤ b :=
      (SourceCircuit.participationCount_physicalFirstOutput
        (w.produce.auxiliary (stackLength r S δ)) physical priv _ p).trans_le
          (w.participationCount_replacement_le hδ hb hlifetime p)
    exact (Finset.card_le_card hsub).trans
      ((R.participationCount_eq_card_incidentGates p).symm.trans_le hl)

end TNLean.PEPS.PairEffect.OriginalCircuit
