/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateGateRescaling
import TNLean.PEPS.Approximation.EffectReplacementExpansion
import TNLean.PEPS.Approximation.EffectCircuitResources

/-!
# Preservation of gate resources under coefficient rescaling

The approximation step changes only numerical coefficients. The original
nonprivate occurrences, prescribed participating sets, monomial lists and
numbers of pair effects retain their original meanings.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-approximatecircuitresources-01
TNLean.PEPS.PairEffect.EffectCircuit.isExpansionBounded_rescaledOriginal
Provenance-ID: 8769-approximate-physical-approximatecircuitresources-02
TNLean.PEPS.PairEffect.EffectCircuit.isMonomialBounded_rescaledOriginal
Provenance-ID: 8769-approximate-physical-approximatecircuitresources-03
TNLean.PEPS.PairEffect.EffectCircuit.monomialCount
Provenance-ID: 8769-approximate-physical-approximatecircuitresources-04
TNLean.PEPS.PairEffect.EffectCircuit.nonprivateCount_rescaledOriginal
Provenance-ID: 8769-approximate-physical-approximatecircuitresources-05
TNLean.PEPS.PairEffect.EffectCircuit.participants_rescaledOriginal
Provenance-ID: 8769-approximate-physical-approximatecircuitresources-06
TNLean.PEPS.PairEffect.EffectCircuit.participationCount_rescaledOriginal
Provenance-ID: 8769-approximate-physical-approximatecircuitresources-07
TNLean.PEPS.PairEffect.EffectCircuit.rescaledLocationsEquiv
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.EffectCircuit
variable {P : Type}

/-- The rescaled original circuit has exactly the recorded gate occurrences. -/
def rescaledLocationsEquiv {δ : ℝ} (hδ : 0 ≤ δ) :
    {a b : Layout P} → (w : EffectCircuit a b) → (G : w.GateMaps) →
      (h : w.IsGateApproximation δ G) →
      (w.rescaledOriginal hδ G h).nonprivateLocations ≃ w.gateLocations
  | _, _, .id _, _, _ => Equiv.refl _
  | _, _, .comp w v, G, h => Equiv.sumCongr
      (w.rescaledLocationsEquiv hδ G.1 h.1) (v.rescaledLocationsEquiv hδ G.2 h.2)
  | _, _, .localMap .., _, _ => Equiv.refl _
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ _ _, _, _ => Equiv.refl _
  | _, _, .swap .., _, _ => Equiv.refl _
  | _, _, .frame _ w, G, h => w.rescaledLocationsEquiv hδ G h

/-- No gate occurrence is added or removed by coefficient rescaling. -/
theorem nonprivateCount_rescaledOriginal {δ : ℝ} (hδ : 0 ≤ δ)
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (h : w.IsGateApproximation δ G) :
    (w.rescaledOriginal hδ G h).nonprivateCount = w.expandedGateCount := by
  induction w with
  | id => rfl
  | comp w v ihw ihv => exact congrArg₂ (· + ·) (ihw G.1 h.1) (ihv G.2 h.2)
  | localMap => rfl
  | gate => rfl
  | swap => rfl
  | frame r w ih => exact ih G h

/-- Every rescaled gate retains its exact prescribed participating set. -/
theorem participants_rescaledOriginal {δ : ℝ} (hδ : 0 ≤ δ)
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (h : w.IsGateApproximation δ G)
    (g : (w.rescaledOriginal hδ G h).nonprivateLocations) :
    (w.rescaledOriginal hδ G h).participants g =
      w.participants (w.rescaledLocationsEquiv hδ G h g) := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv =>
      cases g with
      | inl g => exact ihw G.1 h.1 g
      | inr g => exact ihv G.2 h.2 g
  | localMap => exact nomatch g
  | gate => rfl
  | swap => exact nomatch g
  | frame r w ih => exact ih G h g

/-- A party participates in exactly the same gate occurrences after rescaling. -/
theorem participationCount_rescaledOriginal {δ : ℝ} (hδ : 0 ≤ δ)
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (h : w.IsGateApproximation δ G) (p : P) :
    (w.rescaledOriginal hδ G h).participationCount p =
      Nat.card {g : w.gateLocations // p ∈ w.participants g} := by
  apply Nat.card_congr
  exact (w.rescaledLocationsEquiv hδ G h).subtypeEquiv (fun g ↦ by
    rw [w.participants_rescaledOriginal hδ G h g])

/-- The original pair-effect bound and coefficient-sum bound remain valid. -/
theorem isExpansionBounded_rescaledOriginal {δ : ℝ} (hδ : 0 ≤ δ)
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (h : w.IsGateApproximation δ G) {r : ℕ} {S : ℝ}
    (hb : w.IsExpansionBounded r S) :
    (w.rescaledOriginal hδ G h).IsExpansionBounded r S := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw G.1 h.1 hb.1, ihv G.2 h.2 hb.2⟩
  | localMap => trivial
  | gate owner L tail =>
      refine ⟨?_, (sum_norm_rescalePartyGate_le hδ L).trans hb.2⟩
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact hb.1 r hr
  | swap => trivial
  | frame r w ih => exact ih G h hb

/-- The number of monomials at a recorded original gate occurrence. -/
def monomialCount : {a b : Layout P} → (w : EffectCircuit a b) → w.gateLocations → ℕ
  | _, _, .id _ => Empty.elim
  | _, _, .comp w v => Sum.elim w.monomialCount v.monomialCount
  | _, _, .localMap .. => Empty.elim
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ L _ => fun _ ↦ L.length
  | _, _, .swap .. => Empty.elim
  | _, _, .frame _ w => w.monomialCount

/-- The rescaled expansion has the original monomial bound, without adding
labels or changing the monomial assigned to any label. -/
theorem isMonomialBounded_rescaledOriginal {δ : ℝ} (hδ : 0 ≤ δ)
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (h : w.IsGateApproximation δ G) {K : ℕ}
    (hK : ∀ g, w.monomialCount g ≤ K) :
    (w.rescaledOriginal hδ G h).IsMonomialBounded K := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact
      ⟨ihw G.1 h.1 (fun g ↦ hK (.inl g)), ihv G.2 h.2 (fun g ↦ hK (.inr g))⟩
  | localMap => trivial
  | gate owner L tail =>
      simpa only [rescaledOriginal, OriginalCircuit.IsMonomialBounded,
        rescalePartyGate, List.length_map, monomialCount] using hK ()
  | swap => trivial
  | frame r w ih => exact ih G h hK

end TNLean.PEPS.PairEffect.EffectCircuit
