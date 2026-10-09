/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SupportClassification
import TNLean.PEPS.AreaLaw.Scan.PhysicalBandCommutation

/-!
# Actual charge supports satisfy finite-tree transport compatibility

Physical designated supports are embedded in the augmented tensor-factor set;
they contain neither auxiliary factor. The actual support classification then
supplies the transport compatibility condition for every old and new leaf of
a charge round. History and conditional-choice tree shapes are unchanged.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 336–352, and `08-scanner.tex`, Lemma 9.1(1),
at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower.ReplicaTransport

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

omit [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- A support contained in a physical part stays contained after adjoining the
fixed auxiliary factors C and R. Neither auxiliary factor is added to the support. -/
theorem augmentedPartition_contains_of_constant (σ : PhysicalPartition V) (B : Finset V)
    (h : ∃ part : Option Bool, ∀ x ∈ B, σ x = part) :
    (augmentedPartition σ).Contains (B.map ⟨Sum.inl, Sum.inl_injective⟩) := by
  obtain ⟨part, hp⟩ := h
  have hm : ∀ y ∈ B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool),
      augmentedState σ y = part := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact hp x hx
  cases part with
  | none => exact Or.inr (Or.inl fun y hy ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm y hy⟩)
  | some side =>
    cases side with
    | false => exact Or.inl fun y hy ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm y hy⟩
    | true => exact Or.inr (Or.inr fun y hy ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm y hy⟩)

omit [Fintype I] [LinearOrder I] in
private theorem augmented_inter_nonempty (σ : PhysicalPartition V) (B : Finset V)
    (part : Option Bool) (h : (B ∩ Finset.univ.filter (fun x ↦ σ x = part)).Nonempty) :
    (B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
      Finset.univ.filter (fun x ↦ augmentedState σ x = part)).Nonempty := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨hxB, hxp⟩ := Finset.mem_inter.mp hx
  exact ⟨Sum.inl x, Finset.mem_inter.mpr
    ⟨Finset.mem_map.mpr ⟨x, hxB, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxp).2⟩⟩⟩

omit [DecidableEq V] [Fintype I] [LinearOrder I] in
private theorem augmented_disjoint (σ : PhysicalPartition V) (B : Finset V)
    (part : Option Bool) (h : Disjoint B (Finset.univ.filter fun x ↦ σ x = part)) :
    Disjoint (B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool))
      (Finset.univ.filter fun x ↦ augmentedState σ x = part) := by
  apply Finset.disjoint_left.mpr
  intro y hyB hyp
  obtain ⟨x, hxB, rfl⟩ := Finset.mem_map.mp hyB
  exact Finset.disjoint_left.mp h hxB
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hyp).2⟩)

omit [Fintype I] [LinearOrder I] in
/-- A physical terminal split is a split of the augmented partition, and all
other augmented bands contain the support in a single part. -/
theorem IsTerminalSplit.augmented {K : ℕ} {σ : Fin K → PhysicalPartition V}
    {B : Finset V} {g : Fin K} {side : Bool} (h : IsTerminalSplit σ B g side) :
    (((augmentedPartition (σ g)).SplitsToP (B.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (augmentedPartition (σ g)).SplitsToF (B.map ⟨Sum.inl, Sum.inl_injective⟩)) ∧
      ∀ g' ≠ g, (augmentedPartition (σ g')).Contains (B.map ⟨Sum.inl, Sum.inl_injective⟩)) := by
  refine ⟨?_, fun g' hgg ↦ augmentedPartition_contains_of_constant _ _ (h.2.2.2 g' hgg)⟩
  cases side with
  | false => exact Or.inl ⟨augmented_inter_nonempty _ _ none h.1,
      augmented_inter_nonempty _ _ (some false) h.2.1,
      augmented_disjoint _ _ (some true) h.2.2.1⟩
  | true => exact Or.inr ⟨augmented_inter_nonempty _ _ none h.1,
      augmented_inter_nonempty _ _ (some true) h.2.1,
      augmented_disjoint _ _ (some false) h.2.2.1⟩

namespace CollarScan

/-- Every terminal support of an actual charge round satisfies the transport
compatibility condition. The only support identification is its physical
embedding; compatibility is derived from the source geometric margins. -/
theorem chargeTransportData_supportCompatible_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (n : Site Λ ⊕ Bool → ℕ) (E : EnergyTerms (Site Λ ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩) :
    (S.chargeTransportData histTree choiceTree).SupportCompatible E := by
  rintro ⟨h, c⟩ i g
  simp only [hsupport]
  cases c with
  | none =>
    change (augmentedPartition (S.oldChargeState h g)).Contains _ ∨ _
    rcases old_designatedSupport_classification_domainGraph hT S hgraph hdepth h
      hn hk hr hDpos hD hL hrows hclear g i with hc | ⟨side, hs⟩
    · exact Or.inl (augmentedPartition_contains_of_constant _ _ hc)
    · exact Or.inr hs.augmented
  | some c =>
    simp only [TransportData.leafPart, chargeTransportData_new]
    rcases state_designatedSupport_classification_domainGraph hT S hgraph hdepth
      (extendHistory h c) hn hk hr hDpos hD hL hrows hclear g i with hc | ⟨side, hs⟩
    · exact Or.inl (augmentedPartition_contains_of_constant _ _ hc)
    · exact Or.inr hs.augmented

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
