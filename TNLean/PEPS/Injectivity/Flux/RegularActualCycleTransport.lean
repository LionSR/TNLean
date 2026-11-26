/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Flux.RegularActualCyclePhysicalPermutation
import TNLean.PEPS.Graph.Holonomy.RegularInternalGaugeTransport
import TNLean.PEPS.Graph.Holonomy.RegularTreeGaugeTransport

/-!
# Transport in actual derived cycle coordinates

The original bond assignment determines its normalized tree gauge and cycle
residuals. Directed transport of either the original assignment or a physically
permuted assignment is obtained by endpoint reconstruction. These identities
are auxiliary to SCP10, arXiv:1001.3807, lines 1765–1920 and Theorem 6.16,
lines 2271–2305. No coefficient, state or Gram identity is assumed.

It also contains the following results.

* `TNLean.PEPS.regularActualTwoChord_forwardTransport`,
  `TNLean.PEPS.regularActualTwoChord_reverseTransport`: actual two-chord transport in a vacant
  neighbouring face.
-/

open ManyBody (Edge)

section RegularActualCycleTransport

noncomputable section
namespace TNLean.PEPS
variable {V : Type*} [LinearOrder V]
variable {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]
variable (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
variable (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})

/-- The actual original transport is reconstructed from its derived coordinates.
Source: SCP10, lines 1765–1920. -/
theorem regularDirectedTransport_treeGauge_cycleResidual (u : Edge Γ → G)
    (v w : {x : V // x ∈ R}) (h : Γ.Adj v.1 w.1) :
    regularDirectedTransport u h =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        regularDirectedTransport
          (regularTreeCycleAssignment R T (regularRegionTreeCycleResidual R T hT htree o u)) h *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
  apply regularDirectedTransport_eq_of_internal_reconstruction R
    (regularRegionTreeGauge R T hT htree o u).1 _ u _ h v.2 w.2
  intro e he
  have H := regularGaugedTreeCycleAssignment_treeGauge_of_internal R T hT htree o u e he
  simpa only [regularGaugedTreeCycleAssignment, dite_eq_left he] using H.symm

/-- A forward or inverse actual cycle operation has its derived directed transport.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularActualCycleDirectionalPermutation_directedTransport
    (φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G))
    (reverse : Bool) (u : Edge Γ → G) (v w : {x : V // x ∈ R}) (h : Γ.Adj v.1 w.1) :
    regularDirectedTransport
      (regularActualCycleDirectionalPermutation R T hT htree o φ reverse u) h =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        regularDirectedTransport
          (regularTreeCycleAssignment R T
            ((if reverse then φ.symm else φ) (regularRegionTreeCycleResidual R T hT htree o u))) h *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
  apply regularDirectedTransport_eq_of_internal_reconstruction R
    (regularRegionTreeGauge R T hT htree o u).1 _ _ _ h v.2 w.2
  intro e he
  simp only [regularActualCycleDirectionalPermutation, regularActualCyclePermutation,
    regularRegionBondExtension, ite_eq_left he, regularGaugedTreeCycleAssignment, dite_eq_left he]

omit [Fintype G] in
/-- A selected native cycle coordinate gives the corresponding directed operator,
with inversion precisely in the reverse ordered orientation.
Source: SCP10, lines 1765–1920. -/
theorem regularTreeCycleAssignment_directedTransport
    (z : RegionCycleEdge (Γ := Γ) R T → G) (e : RegionCycleEdge (Γ := Γ) R T)
    {v w : V} (h : Γ.Adj v w) (he : ManyBody.Edge.ofAdj h = e.1.1) :
    regularDirectedTransport (regularTreeCycleAssignment R T z) h =
      if v < w then z e else (z e)⁻¹ := by
  simp only [regularDirectedTransport, he]
  have H : regularTreeCycleAssignment R T z e.1.1 = z e := by
    simp only [regularTreeCycleAssignment, dite_eq_left e.1.2.1,
      dite_eq_left e.1.2.2, dite_eq_left e.2]
  rw [H]

/-- A controlled two-chord operation or its inverse retains every other
literal ordered bond coefficient. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularActualTwoChordPermutation_eq_of_ne
    (e₀ e₁ : RegionCycleEdge (Γ := Γ) R T) (hne : e₀ ≠ e₁)
    (reverse : Bool) (u : Edge Γ → G) (e : Edge Γ) (he₁ : e ≠ e₁.1.1) :
    regularActualCycleDirectionalPermutation R T hT htree o
      (regularTwoCycleMove e₀ e₁ hne) reverse u e = u e := by
  classical
  let k := (regularRegionTreeGauge R T hT htree o u).1
  let ω := regularRegionTreeCycleResidual R T hT htree o u
  let φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G) :=
    if reverse then (regularTwoCycleMove e₀ e₁ hne).symm else regularTwoCycleMove e₀ e₁ hne
  have hcycle : regularTreeCycleAssignment R T (φ ω) e =
      regularTreeCycleAssignment R T ω e := by
    simp only [regularTreeCycleAssignment]
    split_ifs with ht hh hn
    · rfl
    · have hf : (⟨⟨e, ht, hh⟩, hn⟩ : RegionCycleEdge (Γ := Γ) R T) ≠ e₁ := by
        intro h
        exact he₁ (congrArg (fun f => f.1.1) h)
      cases reverse <;> simp [φ, regularTwoCycleMove, hf]
    all_goals rfl
  by_cases he : e.1.1 ∈ R ∧ e.1.2 ∈ R
  · have H := regularGaugedTreeCycleAssignment_treeGauge_of_internal R T hT htree o u e he
    change regularRegionBondExtension R
      (regularGaugedTreeCycleAssignment R T k (φ ω)) u e = u e
    rw [regularRegionBondExtension, ite_eq_left he,
      regularGaugedTreeCycleAssignment, dite_eq_left he, hcycle]
    simpa only [regularGaugedTreeCycleAssignment, dite_eq_left he] using H
  · simp only [regularActualCycleDirectionalPermutation, regularActualCyclePermutation,
      regularRegionBondExtension, ite_eq_right he]

end TNLean.PEPS

end

end RegularActualCycleTransport

section RegularActualTwoChordTransport

/-!
## Actual two-chord transport in a vacant neighbouring face

A five-edge tree path and two cooriented chords determine the elementary
six-site move. The vacancy condition is imposed on the actual loop transport;
the original assignment supplies its own gauge and residuals. This auxiliary
finite-graph calculation underlies SCP10, arXiv:1001.3807, Theorem 6.16,
lines 2271–2305. Native geometry and all original-spin operations remain
separate consumers. No state, Gram or supplied gauge equality is assumed.
-/

noncomputable section
namespace TNLean.PEPS
variable {V : Type*} [LinearOrder V]
variable {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]
variable (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
variable (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})

/-- Actual target vacancy gives the literal middle-chord replacement.
The two chords have the same ordered orientation. Source: SCP10,
Theorem 6.16, lines 2271–2305. -/
theorem regularActualTwoChord_forwardTransport (u : Edge Γ → G)
    (v₀ v₁ v₂ v₃ v₄ v₅ : {v : V // v ∈ R})
    (h₀₁ : T.Adj v₀ v₁) (h₁₂ : T.Adj v₁ v₂) (h₂₃ : T.Adj v₂ v₃)
    (h₃₄ : T.Adj v₃ v₄) (h₄₅ : T.Adj v₄ v₅)
    (h₀₅ : Γ.Adj v₀.1 v₅.1) (h₁₄ : Γ.Adj v₁.1 v₄.1)
    (e₀ e₁ : RegionCycleEdge (Γ := Γ) R T) (hne : e₀ ≠ e₁)
    (he₀ : ManyBody.Edge.ofAdj h₀₅ = e₀.1.1) (he₁ : ManyBody.Edge.ofAdj h₁₄ = e₁.1.1)
    (horder : v₁.1 < v₄.1 ↔ v₀.1 < v₅.1)
    (hv : regularWalkHolonomy u
      (.cons (SimpleGraph.induce_adj.mp (hT h₁₂))
        (.cons (SimpleGraph.induce_adj.mp (hT h₂₃))
          (.cons (SimpleGraph.induce_adj.mp (hT h₃₄)) (.cons h₁₄.symm .nil)))) = 1) :
    regularDirectedTransport
      (regularActualCycleDirectionalPermutation R T hT htree o
        (regularTwoCycleMove e₀ e₁ hne) false u) h₁₄ =
      (regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₄₅)))⁻¹ *
        regularDirectedTransport u h₀₅ *
        (regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₀₁)))⁻¹ := by
  classical
  let k := (regularRegionTreeGauge R T hT htree o u).1
  let ω := regularRegionTreeCycleResidual R T hT htree o u
  have H := regularRegionGaugeResidual_eq_one_iff_directedTransport R T hT htree o u
    h₁₄ v₁.2 v₄.2
  have he : (⟨ManyBody.Edge.ofAdj h₁₄, by rw [he₁]; exact e₁.1.2⟩ :
      {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) = e₁.1 := Subtype.ext he₁
  rw [he] at H
  have hres : ω e₁ = 1 := H.mpr
    ((regularRegionTreeGauge_fourStep_holonomy_eq_one_iff R T hT htree o u
      v₁ v₂ v₃ v₄ h₁₂ h₂₃ h₃₄ h₁₄).mp hv)
  have hcanon : regularDirectedTransport
      (regularTreeCycleAssignment R T (regularTwoCycleMove e₀ e₁ hne ω)) h₁₄ =
      regularDirectedTransport (regularTreeCycleAssignment R T ω) h₀₅ := by
    rw [regularTreeCycleAssignment_directedTransport R T _ e₁ h₁₄ he₁,
      regularTreeCycleAssignment_directedTransport R T ω e₀ h₀₅ he₀]
    simp only [horder, regularTwoCycleMove, Equiv.coe_fn_mk, ite_true,
      regularTweezerEquiv_symm_apply, hres, inv_one, mul_one]
  have hn := regularActualCycleDirectionalPermutation_directedTransport R T hT htree o
    (regularTwoCycleMove e₀ e₁ hne) false u v₁ v₄ h₁₄
  have hl := regularDirectedTransport_treeGauge_cycleResidual R T hT htree o u v₀ v₅ h₀₅
  have hb := regularRegionTreeGauge_directedTransport R T hT htree o u h₀₁
    (SimpleGraph.induce_adj.mp (hT h₀₁))
  have ht := regularRegionTreeGauge_directedTransport R T hT htree o u h₄₅
    (SimpleGraph.induce_adj.mp (hT h₄₅))
  change regularDirectedTransport _ h₁₄ =
    k v₄ * regularDirectedTransport (regularTreeCycleAssignment R T
      (regularTwoCycleMove e₀ e₁ hne ω)) h₁₄ * (k v₁)⁻¹ at hn
  change regularDirectedTransport u h₀₅ =
    k v₅ * regularDirectedTransport (regularTreeCycleAssignment R T ω) h₀₅ * (k v₀)⁻¹ at hl
  change regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₀₁)) =
    k v₁ * (k v₀)⁻¹ at hb
  change regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₄₅)) =
    k v₅ * (k v₄)⁻¹ at ht
  rw [hn, hcanon, hl, hb, ht]
  group

/-- Actual vacancy of the other face gives the reverse literal replacement.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularActualTwoChord_reverseTransport (u : Edge Γ → G)
    (v₀ v₁ v₂ v₃ v₄ v₅ : {v : V // v ∈ R})
    (h₀₁ : T.Adj v₀ v₁) (h₁₂ : T.Adj v₁ v₂) (h₂₃ : T.Adj v₂ v₃)
    (h₃₄ : T.Adj v₃ v₄) (h₄₅ : T.Adj v₄ v₅)
    (h₀₅ : Γ.Adj v₀.1 v₅.1) (h₁₄ : Γ.Adj v₁.1 v₄.1)
    (e₀ e₁ : RegionCycleEdge (Γ := Γ) R T) (hne : e₀ ≠ e₁)
    (he₀ : ManyBody.Edge.ofAdj h₀₅ = e₀.1.1) (he₁ : ManyBody.Edge.ofAdj h₁₄ = e₁.1.1)
    (horder : v₁.1 < v₄.1 ↔ v₀.1 < v₅.1)
    (hv : regularWalkHolonomy u
      (.cons (SimpleGraph.induce_adj.mp (hT h₀₁))
        (.cons h₁₄ (.cons (SimpleGraph.induce_adj.mp (hT h₄₅)) (.cons h₀₅.symm .nil)))) = 1) :
    regularDirectedTransport
      (regularActualCycleDirectionalPermutation R T hT htree o
        (regularTwoCycleMove e₀ e₁ hne) true u) h₁₄ =
      regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₃₄)) *
        regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₂₃)) *
        regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₁₂)) := by
  classical
  let k := (regularRegionTreeGauge R T hT htree o u).1
  let ω := regularRegionTreeCycleResidual R T hT htree o u
  let c₀ := regularDirectedTransport (regularTreeCycleAssignment R T ω) h₀₅
  let c₁ := regularDirectedTransport (regularTreeCycleAssignment R T ω) h₁₄
  have hl := regularDirectedTransport_treeGauge_cycleResidual R T hT htree o u v₀ v₅ h₀₅
  have hm := regularDirectedTransport_treeGauge_cycleResidual R T hT htree o u v₁ v₄ h₁₄
  have hb := regularRegionTreeGauge_directedTransport R T hT htree o u h₀₁
    (SimpleGraph.induce_adj.mp (hT h₀₁))
  have ht := regularRegionTreeGauge_directedTransport R T hT htree o u h₄₅
    (SimpleGraph.induce_adj.mp (hT h₄₅))
  change regularDirectedTransport u h₀₅ = k v₅ * c₀ * (k v₀)⁻¹ at hl
  change regularDirectedTransport u h₁₄ = k v₄ * c₁ * (k v₁)⁻¹ at hm
  change regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₀₁)) =
    k v₁ * (k v₀)⁻¹ at hb
  change regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₄₅)) =
    k v₅ * (k v₄)⁻¹ at ht
  simp only [regularWalkHolonomy_cons, regularWalkHolonomy_nil, one_mul,
    regularDirectedTransport_symm u h₀₅] at hv
  have hword : (regularDirectedTransport u h₀₅)⁻¹ *
      regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₄₅)) *
      regularDirectedTransport u h₁₄ *
      regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₀₁)) =
      k v₀ * (c₀⁻¹ * c₁) * (k v₀)⁻¹ := by rw [hl, hm, hb, ht]; group
  rw [hword] at hv
  have hs : c₀⁻¹ * c₁ = 1 := by
    calc
      c₀⁻¹ * c₁ = (k v₀)⁻¹ * (k v₀ * (c₀⁻¹ * c₁) * (k v₀)⁻¹) * k v₀ := by group
      _ = 1 := by rw [hv]; group
  have hc : c₀ = c₁ := inv_mul_eq_one.mp hs
  change regularDirectedTransport (regularTreeCycleAssignment R T ω) h₀₅ =
    regularDirectedTransport (regularTreeCycleAssignment R T ω) h₁₄ at hc
  rw [regularTreeCycleAssignment_directedTransport R T ω e₀ h₀₅ he₀,
    regularTreeCycleAssignment_directedTransport R T ω e₁ h₁₄ he₁] at hc
  simp only [horder] at hc
  have hres : ω e₁ = ω e₀ := by
    by_cases hlt : v₀.1 < v₅.1
    · simpa only [ite_eq_left hlt] using hc.symm
    · have hi : (ω e₁)⁻¹ = (ω e₀)⁻¹ := by
        simpa only [ite_eq_right hlt] using hc.symm
      exact inv_injective hi
  have hcanon : regularDirectedTransport
      (regularTreeCycleAssignment R T ((regularTwoCycleMove e₀ e₁ hne).symm ω)) h₁₄ = 1 := by
    rw [regularTreeCycleAssignment_directedTransport R T _ e₁ h₁₄ he₁]
    simp [regularTwoCycleMove, regularTweezerEquiv_apply, hres]
  have hn := regularActualCycleDirectionalPermutation_directedTransport R T hT htree o
    (regularTwoCycleMove e₀ e₁ hne) true u v₁ v₄ h₁₄
  change regularDirectedTransport _ h₁₄ =
    k v₄ * regularDirectedTransport (regularTreeCycleAssignment R T
      ((regularTwoCycleMove e₀ e₁ hne).symm ω)) h₁₄ * (k v₁)⁻¹ at hn
  have h₁ := regularRegionTreeGauge_directedTransport R T hT htree o u h₁₂
    (SimpleGraph.induce_adj.mp (hT h₁₂))
  have h₂ := regularRegionTreeGauge_directedTransport R T hT htree o u h₂₃
    (SimpleGraph.induce_adj.mp (hT h₂₃))
  have h₃ := regularRegionTreeGauge_directedTransport R T hT htree o u h₃₄
    (SimpleGraph.induce_adj.mp (hT h₃₄))
  change regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₁₂)) =
    k v₂ * (k v₁)⁻¹ at h₁
  change regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₂₃)) =
    k v₃ * (k v₂)⁻¹ at h₂
  change regularDirectedTransport u (SimpleGraph.induce_adj.mp (hT h₃₄)) =
    k v₄ * (k v₃)⁻¹ at h₃
  rw [hn, hcanon, h₁, h₂, h₃]
  group

end TNLean.PEPS

end

end RegularActualTwoChordTransport
