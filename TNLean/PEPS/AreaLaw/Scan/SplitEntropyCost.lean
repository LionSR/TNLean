/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargeEntropyCost

/-!
# Designated incidence costs and old-leaf split entropy

For compatible designated supports, the actual side-labelled incidence sum
equals the transport definition of split entropy at the old leaf. All sums
retain interaction labels, including distinct labels sharing an anchor.
The assertion is algebraic; the actual geometric compatibility theorem is
supplied separately before specializing this identity to the scanner.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 336–347, and `08-scanner.tex`, lines 331–337,
at `openai/math@adc7f124`.
-/

open scoped BigOperators
open TensorPower TensorPower.ReplicaTransport
open Entropy (SiteConfig)

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem not_middle_side_of_contains (π : PYF V) (hπ : π.IsPartition)
    (B : Finset V) (hc : π.Contains B) :
    ¬ ((B ∩ π.Y).Nonempty ∧ ((B ∩ π.P).Nonempty ∨ (B ∩ π.F).Nonempty)) := by
  rintro ⟨⟨x, hx⟩, hs⟩
  obtain ⟨hxB, hxY⟩ := Finset.mem_inter.mp hx
  rcases hc with hP | hY | hF
  · exact Finset.disjoint_left.mp hπ.1 (hP hxB) hxY
  · rcases hs with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Finset.disjoint_left.mp hπ.1 (Finset.mem_inter.mp hy).2
        (hY (Finset.mem_inter.mp hy).1)
    · exact Finset.disjoint_left.mp hπ.2.2.1 (hY (Finset.mem_inter.mp hy).1)
        (Finset.mem_inter.mp hy).2
  · exact Finset.disjoint_left.mp hπ.2.2.1 hxY (hF hxB)

open Classical in
/-- A contained support has no receiving-middle incidence. Otherwise its
unique receiving side contributes precisely the split entropy. -/
theorem incidence_sum_eq_splitBandEta (n : V → ℕ) (π : PYF V) (hπ : π.IsPartition)
    (B : Finset V) (hcase : π.Contains B ∨ π.SplitsToP B ∨ π.SplitsToF B)
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    (if (B ∩ π.F).Nonempty ∧ (B ∩ π.Y).Nonempty then
        moveEta n π (.toF (B ∩ π.Y)) θ else 0) +
      (if (B ∩ π.P).Nonempty ∧ (B ∩ π.Y).Nonempty then
        moveEta n π (.toP (B ∩ π.Y)) θ else 0) =
      if π.Contains B then 0 else splitBandEta n π B θ := by
  classical
  by_cases hc : π.Contains B
  · have hn := not_middle_side_of_contains π hπ B hc
    have hP : ¬ ((B ∩ π.P).Nonempty ∧ (B ∩ π.Y).Nonempty) :=
      fun h => hn ⟨h.2, Or.inl h.1⟩
    have hF : ¬ ((B ∩ π.F).Nonempty ∧ (B ∩ π.Y).Nonempty) :=
      fun h => hn ⟨h.2, Or.inr h.1⟩
    simp only [hP, hF, hc, ↓reduceIte, add_zero]
  · rcases hcase with hc' | hP | hF
    · exact (hc hc').elim
    · have hnF : ¬ (B ∩ π.F).Nonempty := by
        rw [Finset.disjoint_iff_inter_eq_empty.mp hP.2.2]
        simp
      simp only [hc, hP.1, hP.2.1, hnF, false_and, and_self, ↓reduceIte,
        zero_add, splitBandEta, hP, moveEta]
    · have hnP : ¬ (B ∩ π.P).Nonempty := by
        rw [Finset.disjoint_iff_inter_eq_empty.mp hF.2.2]
        simp
      have hnSplitP : ¬ π.SplitsToP B := fun hP => hnP hP.2.1
      simp only [hc, hF.1, hF.2.1, hnP, false_and, and_self, ↓reduceIte,
        add_zero, splitBandEta, hnSplitP, moveEta]

end TensorPower.ReplicaTransport

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
private theorem lifted_inter_part (σ : PhysicalPartition V) (B : Finset V)
    (part : Option Bool) :
    B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
        Finset.univ.filter (fun x => augmentedState σ x = part) =
      (B ∩ Finset.univ.filter (fun x => σ x = part)).map
        (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyB, hyp⟩ := Finset.mem_inter.mp hy
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_map.mp hyB
    exact Finset.mem_map.mpr ⟨x, Finset.mem_inter.mpr
      ⟨hxB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hyp).2⟩⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨hxB, hxp⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_map.mpr ⟨x, hxB, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxp).2⟩⟩

omit [Fintype I] [LinearOrder I] in
open Classical in
private theorem physical_incidence_sum (n : V ⊕ Bool → ℕ)
    (σ : PhysicalPartition V) (B : Finset V)
    (hcase : (augmentedPartition σ).Contains (B.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (augmentedPartition σ).SplitsToP (B.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (augmentedPartition σ).SplitsToF (B.map ⟨Sum.inl, Sum.inl_injective⟩))
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    (∑ side : Bool, if (B ∩ receiving σ side).Nonempty ∧ (B ∩ middle σ).Nonempty then
      moveEta n (augmentedPartition σ) (augmentedMove σ side (B ∩ middle σ)) θ else 0) =
      if (augmentedPartition σ).Contains (B.map ⟨Sum.inl, Sum.inl_injective⟩) then 0 else
        splitBandEta n (augmentedPartition σ) (B.map ⟨Sum.inl, Sum.inl_injective⟩) θ := by
  classical
  have hY : B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
      (augmentedPartition σ).Y = (B ∩ middle σ).map ⟨Sum.inl, Sum.inl_injective⟩ :=
    lifted_inter_part σ B none
  have hP : B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
      (augmentedPartition σ).P = (B ∩ receiving σ false).map ⟨Sum.inl, Sum.inl_injective⟩ :=
    lifted_inter_part σ B (some false)
  have hF : B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∩
      (augmentedPartition σ).F = (B ∩ receiving σ true).map ⟨Sum.inl, Sum.inl_injective⟩ :=
    lifted_inter_part σ B (some true)
  have heq := incidence_sum_eq_splitBandEta n (augmentedPartition σ)
    (augmentedPartition_isPartition σ) (B.map ⟨Sum.inl, Sum.inl_injective⟩) hcase θ
  rw [Fintype.sum_bool]
  simpa only [hY, hP, hF, Finset.map_nonempty, augmentedMove,
    Finset.inter_assoc, Finset.inter_self, Bool.false_eq_true, ↓reduceIte] using heq

namespace CollarScan

variable (S : CollarScan V I) (n : V ⊕ Bool → ℕ)

/-- Compatible physically embedded supports identify the labelled incidence
cost with the actual old-leaf split entropy. Compatibility is a generic
premise here; the physical specialization derives it from scanner geometry. -/
theorem designatedSplitIncidenceCost_eq_sum_splitEta {k L : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (E : EnergyTerms (V ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (hcompat : (S.chargeTransportData histTree choiceTree).SupportCompatible E)
    (h : History S.K S.m S.M k) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    S.designatedSplitIncidenceCost L h (S.chargeEntropyCost n h θ) =
      ∑ i, (S.chargeTransportData histTree choiceTree).splitEta E i ⟨h, none⟩ θ := by
  classical
  unfold designatedSplitIncidenceCost TransportData.splitEta
  simp only [designatedSplitIncidences, Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro i _
  have hcase := hcompat ⟨h, none⟩ i g
  have hcase' : ((S.chargeTransportData histTree choiceTree).old h g).Contains (E.support i) ∨
      ((S.chargeTransportData histTree choiceTree).old h g).SplitsToP (E.support i) ∨
      ((S.chargeTransportData histTree choiceTree).old h g).SplitsToF (E.support i) :=
    hcase.imp_right And.left
  rw [hsupport i] at hcase' ⊢
  simpa only [chargeEntropyCost, TransportData.leafPart, chargeTransportData,
    ite_not] using physical_incidence_sum n (S.oldChargeState h g)
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) hcase' θ

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
