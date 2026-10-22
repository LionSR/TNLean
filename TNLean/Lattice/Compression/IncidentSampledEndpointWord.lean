/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedPartialSourceSlots
import TNLean.Lattice.Compression.ActualSampledEndpointInputWord
import TNLean.Lattice.Compression.EndpointRegisterRestriction

/-!
# Sampled endpoint operations determined by incident labels

Two independent assignments of original incident gate labels determine the
sampled endpoint word at one party. The singleton source slots retain their
original occurrence indices and Euclidean dimensions. At both endpoints of
each retained slot, the word uses the same local sample index and the
same Gaussian array indexed by the ordered pair of incident labels.

The endpoint register data are filtered before their chronological word is
formed. The construction requires samples only at the singleton source slots,
without extending incident labels or sample indices to other gates.
Its input and output are the actual selected all-party source registers,
including the canonical identification with their terminal empty layout.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
279–355, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.SourceCircuit
open TNLean.PEPS.PairEffect
variable {P : Type} {a b : Layout P}

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- Construct the selected sampled endpoint word from two independent incident
label assignments and a sample assignment on the singleton source slots. Each
slot uses its shared local sample index and original ordered-pair Gaussian
array at both endpoints. The selected register data are formed before their
word. No full branch choice or sample extension is supplied.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
279–355, 409–434 and 565–588. -/
def incidentSampledEndpointWord (p : P) (η θ : OriginalGateLabelsAt w p)
    (j : Fin (partialSlots
      (fun t : P ↦ partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P ↦ true) t)) w).length → Fin k)
    (ω : SourceGaussianSamples w k) :
    Word (Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ []))
      (Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ [])) := by
  classical
  let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
    (affectedOwner (fun _ : P ↦ true) t)
  let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
    (decide_eq_true rfl)
  let q : Option {t : P // A t = true} := some ⟨p, hp⟩
  let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
    fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
  let R := partialSlots A w
  let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  let S := SourceInventory.slotLayout R U V
  let χη := choicesOfOriginalGateLabelsAt w p η
  let χθ := choicesOfOriginalGateLabelsAt w p θ
  let M : ∀ i, U i →L[ℂ] U i := fun i ↦
    basisMatrixOperator (EuclideanSpace.basisFun _ ℂ)
      (sampledEndpointLeft w k lam E (partialSlotEquiv A w i).1
        (partialSlotChoice A w χη i, partialSlotChoice A w χθ i)
        (j i) ω)
  let N : ∀ i, V i →L[ℂ] V i := fun i ↦
    basisMatrixOperator (EuclideanSpace.basisFun _ ℂ)
      (sampledEndpointRight w k lam F (partialSlotEquiv A w i).1
        (partialSlotChoice A w χη i, partialSlotChoice A w χθ i)
        (j i) ω)
  let D := SourceInventory.endpointRegisterData R U V M N
  let Dp := D.filter (fun z ↦ partySelector q z.1.owner)
  let Z := SourceInventory.endpointRegisterWord Dp
  have hDp : Dp.map Sigma.fst = Layout.restrict (partySelector q) S :=
    SourceInventory.endpointRegisterData_filter_layout (partySelector q) R U V M N
  have hselected : Layout.mapOwner lift (Layout.restrict (partySelector q) S) =
      Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ []) := by
    rw [List.append_nil]
    exact mapOwner_atParty_partialSlots_eq_allResidualSourceLayout w p
  have hin : Layout.mapOwner lift (Dp.map Sigma.fst) =
      Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ []) :=
    (congrArg (Layout.mapOwner lift) hDp).trans hselected
  exact (Z.mapOwner lift).castLayouts hin hin

/-- The incident sampled endpoint word introduces no source preparation.
Empty source inventories and sample index sets and zero-dimensional endpoint
spaces are included without positivity or normalization assumptions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355
and 565–588. -/
theorem sources_incidentSampledEndpointWord (p : P) (η θ : OriginalGateLabelsAt w p)
    (j : Fin (partialSlots
      (fun t : P ↦ partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P ↦ true) t)) w).length → Fin k)
    (ω : SourceGaussianSamples w k) :
    (incidentSampledEndpointWord w k lam E F p η θ j ω).sources = [] := by
  classical
  unfold incidentSampledEndpointWord
  simp only [Word.sources_castLayouts, Word.sources_mapOwner,
    SourceInventory.sources_endpointRegisterWord, SourceInventory.mapOwner_nil]

end TNLean.Lattice.PartyCircuit.SourceCircuit
