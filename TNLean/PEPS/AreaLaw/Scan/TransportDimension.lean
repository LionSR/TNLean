/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimension
import TNLean.PEPS.AreaLaw.Scan.FillTransport
import TNLean.PEPS.AreaLaw.Scan.SupportCompatibility

/-!
# Actual transport dimensions with unrestricted auxiliary factors

The transferred subsystem is the physical middle difference embedded by
`Sum.inl`. Its logarithmic dimension therefore depends only on the physical
local dimension `q`, even when the two auxiliary factors have arbitrary
sizes. Both fill and charge rounds satisfy the explicit cap
`1 + (2r₀+1)² log q`. A designated support satisfies the same cap only when
its actual set of split leaves is nonempty.

The split-support bound uses initial far-side persistence and the crossing
radius reduction, not support compatibility or a supplied dimension bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 331–352, and `08-scanner.tex`, lines 125–137 and
225–233, at `openai/math@adc7f124`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower.ReplicaTransport

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The augmented move contains exactly the embedded physical middle intersection. -/
theorem augmentedMove_subsystem (σ : PhysicalPartition V) (side : Bool) (B : Finset V) :
    (augmentedMove σ side B).subsystem =
      (B ∩ middle σ).map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) := by
  cases side <;> rfl

omit [Fintype V] [DecidableEq V] in
/-- A physical-only support has the same logarithmic dimension after augmentation.
Neither auxiliary dimension is constrained by this identity. -/
theorem logDim_physical_eq (B : Finset V) (n : V ⊕ Bool → ℕ) (q : ℕ)
    (hphysical : ∀ x, n (Sum.inl x) = q) :
    logDim n (B.map ⟨Sum.inl, Sum.inl_injective⟩) =
      Real.log (Real.exp 1 * (q : ℝ) ^ B.card) := by
  rw [logDim, prod_physical_subsystem_dimension B n q hphysical]

namespace CollarScan

variable [Fintype I] [LinearOrder I] (S : CollarScan V I)

/-- Quantum charge bookkeeping records precisely the sites actually removed
from the old physical middle, including blank and disabled choices. -/
theorem quantumChargeMove_subsystem (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) :
    (S.quantumChargeMove g r k c σ).subsystem =
      (middle σ \ middle (S.chargeStep g r k c σ)).map
        (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) := by
  cases he : S.selected g r k c with
  | none => simp [quantumChargeMove, chargeStep, he, Move.subsystem]
  | some i =>
    simp only [quantumChargeMove, chargeStep, he, charge]
    split_ifs
    · rw [augmentedMove_subsystem, middle_sdiff_middle_assign]
    · simp [Move.subsystem]

omit [Fintype I] [LinearOrder I] in
/-- A fill's quantum subsystem is its actual physical middle difference. -/
theorem quantumFillMove_subsystem (g r k : ℕ) (σ : PhysicalPartition V) :
    (S.quantumFillMove g r k σ).subsystem =
      (middle σ \ middle (fill S.A S.depth S.n (S.lower g r) (S.upper g r) k σ)).map
        (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) := by
  cases he : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) with
  | none => simp [quantumFillMove, fill, he, Move.subsystem]
  | some x =>
    simp only [quantumFillMove, fill, he, augmentedMove_subsystem, middle_sdiff_middle_assign]

omit [Fintype I] [LinearOrder I] in
/-- A fill moves at most one physical factor, irrespective of auxiliary sizes. -/
theorem logDim_quantumFillMove_le (g r k : ℕ) (σ : PhysicalPartition V)
    (n : V ⊕ Bool → ℕ) {q : ℕ} (hq : 1 ≤ q)
    (hphysical : ∀ x, n (Sum.inl x) = q) :
    logDim n (S.quantumFillMove g r k σ).subsystem ≤ 1 + Real.log q := by
  rw [quantumFillMove_subsystem, logDim_physical_eq _ n q hphysical]
  exact log_fill_moved_dimension_le S.A S.depth S.n _ _ k σ hq

/-- Each actual charge move has the explicit physical transport cap. -/
theorem logDim_quantumChargeMove_le_domainGraph {Λ : Finset (ℤ × ℤ)}
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (g r k : ℕ) (c : Bool × Fin S.M) (σ : PhysicalPartition (Site Λ))
    (n : Site Λ ⊕ Bool → ℕ) {q : ℕ} (hq : 1 ≤ q)
    (hphysical : ∀ x, n (Sum.inl x) = q) :
    logDim n (S.quantumChargeMove g r k c σ).subsystem ≤ transportLogDimBound q S.r₀ := by
  rw [quantumChargeMove_subsystem, logDim_physical_eq _ n q hphysical]
  exact S.log_chargeStep_moved_dimension_le_domainGraph hgraph g r k c σ hq

/-- Every move of an actual fill round satisfies the same cap as its charges. -/
theorem fillTransportData_logDim_move_le {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (n : V ⊕ Bool → ℕ) {q : ℕ} (hq : 1 ≤ q)
    (hphysical : ∀ x, n (Sum.inl x) = q)
    (h : History S.K S.m S.M k) (c : Unit) (g : Fin S.K) :
    logDim n ((S.fillTransportData histTree).move h c g).subsystem ≤
      transportLogDimBound q S.r₀ := by
  change logDim n (S.quantumFillMove g (h.1 g) k (S.state h g)).subsystem ≤ _
  rw [quantumFillMove_subsystem, logDim_physical_eq _ n q hphysical]
  apply log_physicalDimension_le_of_card_le _ hq
  exact (card_fill_moved_le_one S.A S.depth S.n _ _ k _).trans (by
    have : 1 ≤ 2 * S.r₀ + 1 := by omega
    exact Nat.one_le_pow _ _ this)

/-- Every move of an actual charge round satisfies the physical cap. -/
theorem chargeTransportData_logDim_move_le_domainGraph {Λ : Finset (ℤ × ℤ)}
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ) {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (n : Site Λ ⊕ Bool → ℕ) {q : ℕ} (hq : 1 ≤ q)
    (hphysical : ∀ x, n (Sum.inl x) = q)
    (h : History S.K S.m S.M k) (c : ChargeChoices S.K S.M) (g : Fin S.K) :
    logDim n ((S.chargeTransportData histTree choiceTree).move h c g).subsystem ≤
      transportLogDimBound q S.r₀ :=
  S.logDim_quantumChargeMove_le_domainGraph hgraph g (h.1 g) (k + 1) (c g)
    (S.oldChargeState h g) n hq hphysical

/-- A designated support with any split leaf in an actual charge round has the
physical cap. No cap is asserted when its split-leaf set is empty. -/
theorem chargeTransportData_logDim_support_le_domainGraph {Λ : Finset (ℤ × ℤ)}
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ) {k L q : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (n : Site Λ ⊕ Bool → ℕ) (hq : 1 ≤ q) (hphysical : ∀ x, n (Sum.inl x) = q)
    (hL : 8 * S.K * S.m ≤ L) (E : EnergyTerms (Site Λ ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩) (i : I)
    (hsplit : ((S.chargeTransportData histTree choiceTree).splitLeaves E i).Nonempty) :
    logDim n (E.support i) ≤ transportLogDimBound q S.r₀ := by
  classical
  obtain ⟨⟨h, c⟩, hj⟩ := hsplit
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hj).2
  rw [hsupport] at hg ⊢
  rw [logDim_physical_eq _ n q hphysical]
  cases c with
  | none =>
    apply S.log_designatedSupport_dimension_le_of_old_not_constant_domainGraph
      hgraph h g i hq hL
    exact fun hc ↦ hg (augmentedPartition_contains_of_constant _ _ hc)
  | some c =>
    simp only [TransportData.leafPart, chargeTransportData_new] at hg
    apply S.log_designatedSupport_dimension_le_of_state_not_constant_domainGraph
      hgraph (extendHistory h c) g i hq hL
    exact fun hc ↦ hg (augmentedPartition_contains_of_constant _ _ hc)

/-- Nonempty actual fill split-leaf sets satisfy the same designated-support cap. -/
theorem fillTransportData_logDim_support_le_domainGraph {Λ : Finset (ℤ × ℤ)}
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ) {k L q : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (n : Site Λ ⊕ Bool → ℕ) (hq : 1 ≤ q) (hphysical : ∀ x, n (Sum.inl x) = q)
    (hL : 8 * S.K * S.m ≤ L) (E : EnergyTerms (Site Λ ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩) (i : I)
    (hsplit : ((S.fillTransportData histTree).splitLeaves E i).Nonempty) :
    logDim n (E.support i) ≤ transportLogDimBound q S.r₀ := by
  classical
  obtain ⟨⟨h, c⟩, hj⟩ := hsplit
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hj).2
  rw [hsupport] at hg ⊢
  rw [logDim_physical_eq _ n q hphysical]
  cases c with
  | none =>
    apply S.log_designatedSupport_dimension_le_of_state_not_constant_domainGraph
      hgraph h g i hq hL
    exact fun hc ↦ hg (augmentedPartition_contains_of_constant _ _ hc)
  | some c =>
    simp only [TransportData.leafPart, fillTransportData_new] at hg
    apply S.log_designatedSupport_dimension_le_of_old_not_constant_domainGraph
      hgraph h g i hq hL
    exact fun hc ↦ hg (augmentedPartition_contains_of_constant _ _ hc)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
