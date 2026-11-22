/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.EndpointWordRestriction
import TNLean.Lattice.Compression.ActualSampledEndpointInputWord

/-!
# Pointwise congruence of restricted endpoint words

Fix the source inventory, the endpoint spaces, and a selector of owners.
Changing an endpoint map at an unselected owner leaves the restricted word
unchanged. At selected owners the corresponding maps must agree. This is a
congruence statement for the actual endpoint operators; no local factorization
or equality of sampled averages is assumed.

The register order and spectator memories are fixed throughout. The maps and
spaces are arbitrary, including zero-dimensional spaces and an empty inventory.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588, pointwise endpoint locality.

## Local dependence of the actual endpoint samples

Fix independent ket and bra choices. Restriction to selected owners uses only
the sample indices and Gaussian arrays at sources with a selected endpoint.
Changing the remaining sample data leaves the restricted operator unchanged.
The same sample and ordered ket–bra array are used at both endpoints of each
source throughout this comparison.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588.
-/

section

noncomputable section
namespace TNLean.Lattice.PartyCircuit.SourceInventory
variable {P : Type}

private theorem restrict_castLayouts_congr (f : P → Bool)
    {a b a' b' : Layout P} (u v : Word a b) (hu : u.sources = []) (hv : v.sources = [])
    (ha : a = a') (hb : b = b') (h : u.restrict f hu = v.restrict f hv) :
    Word.restrict f (u.castLayouts ha hb) ((Word.sources_castLayouts u ha hb).trans hu) =
      Word.restrict f (v.castLayouts ha hb) ((Word.sources_castLayouts v ha hb).trans hv) := by
  rw [Word.restrict_castLayouts f u ha hb hu,
    Word.restrict_castLayouts f v ha hb hv, h]

private theorem restrict_comp_congr (f : P → Bool) {a b c : Layout P}
    (u u' : Word a b) (v v' : Word b c)
    (hu : u.sources = []) (hu' : u'.sources = [])
    (hv : v.sources = []) (hv' : v'.sources = [])
    (h : u.restrict f hu = u'.restrict f hu')
    (h' : v.restrict f hv = v'.restrict f hv') :
    (u.comp v).restrict f (by simp only [Word.sources, hu, hv, List.nil_append]) =
      (u'.comp v').restrict f (by simp only [Word.sources, hu', hv', List.nil_append]) := by
  change (u.restrict f hu).comp (v.restrict f hv) =
    (u'.restrict f hu').comp (v'.restrict f hv')
  exact congrArg₂ Word.comp h h'

private theorem restrict_frame_congr (f : P → Bool) (r : Reg P) {a b : Layout P}
    (u v : Word a b) (hu : u.sources = []) (hv : v.sources = [])
    (h : u.restrict f hu = v.restrict f hv) :
    (Word.frame r u).restrict f hu = (Word.frame r v).restrict f hv := by
  simp only [Word.restrict]
  split <;> rw [h]

private theorem restrict_localEndpoint_congr (f : P → Bool) (r : Reg P)
    (A A' : r.space →L[ℂ] r.space) (tail : Layout P)
    (h : f r.owner = true → A = A') :
    (Word.localEndpoint r A tail).restrict f (Word.sources_localEndpoint r A tail) =
      (Word.localEndpoint r A' tail).restrict f (Word.sources_localEndpoint r A' tail) := by
  by_cases hr : f r.owner = true
  · rw [h hr]
  · simp only [Word.localEndpoint, Word.restrict, dite_eq_right hr]

private theorem restrict_endpointWord_eq_of_local_eq
    (f : P → Bool) (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A A' : ∀ i, U i →L[ℂ] U i) (B B' : ∀ i, V i →L[ℂ] V i)
    (hL : ∀ i, f (R.get i).left = true → A i = A' i)
    (hR : ∀ i, f (R.get i).right = true → B i = B' i) :
    (endpointWord R U V A B).restrict f (sources_endpointWord R U V A B) =
      (endpointWord R U V A' B').restrict f (sources_endpointWord R U V A' B') := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      have hTail := ih (fun i ↦ U i.succ) (fun i ↦ V i.succ)
        (fun i ↦ A i.succ) (fun i ↦ A' i.succ)
        (fun i ↦ B i.succ) (fun i ↦ B' i.succ)
        (fun i ↦ hL i.succ) (fun i ↦ hR i.succ)
      have hLeft := restrict_localEndpoint_congr f ⟨r.left, U 0⟩ (A 0) (A' 0)
        (⟨r.right, V 0⟩ :: slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)) (hL 0)
      have hRight := restrict_localEndpoint_congr f ⟨r.right, V 0⟩ (B 0) (B' 0)
        (slotLayout R (fun i ↦ U i.succ) (fun i ↦ V i.succ)) (hR 0)
      unfold endpointWord
      refine restrict_castLayouts_congr f _ _ ?_ ?_
        (slotLayout_cons r R U V).symm (slotLayout_cons r R U V).symm ?_
      · simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord,
          List.nil_append]
      · simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord,
          List.nil_append]
      · apply restrict_comp_congr f <;>
          try simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord,
            List.nil_append]
        · exact hLeft
        · apply restrict_frame_congr f
          apply restrict_comp_congr f <;>
            try simp only [Word.sources, Word.sources_localEndpoint, sources_endpointWord]
          · exact hRight
          · exact restrict_frame_congr f _ _ _ _ _ hTail

/-- On a fixed source inventory, the restricted endpoint operator depends only
on the maps at selected endpoint owners. Equalities are required solely for
those endpoint maps, without a premise asserting equality of local factors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and
565–588, pointwise endpoint locality in the construction. -/
theorem restrict_endpointWord_eval_eq_of_local_eq
    (f : P → Bool) (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A A' : ∀ i, U i →L[ℂ] U i) (B B' : ∀ i, V i →L[ℂ] V i)
    (hL : ∀ i, f (R.get i).left = true → A i = A' i)
    (hR : ∀ i, f (R.get i).right = true → B i = B' i) :
    ((endpointWord R U V A B).restrict f (sources_endpointWord R U V A B)).eval =
      ((endpointWord R U V A' B').restrict f (sources_endpointWord R U V A' B')).eval :=
  congrArg Circuit.eval (restrict_endpointWord_eq_of_local_eq f R U V A A' B B' hL hR)

end TNLean.Lattice.PartyCircuit.SourceInventory
end

end

section

noncomputable section
namespace TNLean.Lattice.PartyCircuit.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- The actual sampled source-input operator restricted to selected owners
depends only on the samples at incident source occurrences. The ket and bra
choices are fixed independently, and no unused sample or branch label is chosen.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and
565–588, pointwise locality of the sampled endpoint factors. -/
theorem restrict_sampledEndpointInputWord_eval_eq_of_incident_samples
    (w : SourceCircuit a b) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j j' : w.sourceLocations → Fin k) (ω ω' : SourceGaussianSamples w k)
    (f : Option {_p : P // true = true} → Bool)
    (h : ∀ i : Fin (partialSlots (fun _ : P ↦ true) w).length,
      f ((partialSlots (fun _ : P ↦ true) w).get i).left = true ∨
        f ((partialSlots (fun _ : P ↦ true) w).get i).right = true →
      j (allSourceSlotEquiv w i) = j' (allSourceSlotEquiv w i) ∧
        ω (partialSlotEquiv (fun _ : P ↦ true) w i).1
            (partialSlotChoice (fun _ : P ↦ true) w ξ i,
              partialSlotChoice (fun _ : P ↦ true) w ζ i) =
          ω' (partialSlotEquiv (fun _ : P ↦ true) w i).1
            (partialSlotChoice (fun _ : P ↦ true) w ξ i,
              partialSlotChoice (fun _ : P ↦ true) w ζ i)) :
    ((sampledEndpointInputWord w k lam L R ξ ζ j ω).restrict f
      (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).eval =
      ((sampledEndpointInputWord w k lam L R ξ ζ j' ω').restrict f
        (sources_sampledEndpointInputWord w k lam L R ξ ζ j' ω')).eval := by
  classical
  have hWord :
      ((sampledEndpointWord w k lam L R ξ ζ j ω).restrict f
        (sources_sampledEndpointWord w k lam L R ξ ζ j ω)).eval =
        ((sampledEndpointWord w k lam L R ξ ζ j' ω').restrict f
          (sources_sampledEndpointWord w k lam L R ξ ζ j' ω')).eval := by
    dsimp only [sampledEndpointWord, SourceInventory.endpointMatrixWord]
    refine SourceInventory.restrict_endpointWord_eval_eq_of_local_eq f
      (partialSlots (fun _ : P ↦ true) w) w.allSourceU w.allSourceV _ _ _ _ ?_ ?_
    · intro i hi
      obtain ⟨hj, hω⟩ := h i (Or.inl hi)
      simp only [sampledEndpointLeft, hj, hω]
    · intro i hi
      obtain ⟨hj, hω⟩ := h i (Or.inr hi)
      simp only [sampledEndpointRight, hj, hω]
  unfold sampledEndpointInputWord
  rw [Word.restrict_castLayouts f (sampledEndpointWord w k lam L R ξ ζ j ω)
      (List.append_nil _).symm (List.append_nil _).symm
      (sources_sampledEndpointWord w k lam L R ξ ζ j ω),
    Word.restrict_castLayouts f (sampledEndpointWord w k lam L R ξ ζ j' ω')
      (List.append_nil _).symm (List.append_nil _).symm
      (sources_sampledEndpointWord w k lam L R ξ ζ j' ω')]
  simp only [Circuit.eval_castLayouts, hWord]

end TNLean.Lattice.PartyCircuit.SourceCircuit
end

end
