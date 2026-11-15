/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTreeGaugeTransport
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Tree gauges fixed on an untwisted component

A connected region has a spanning tree whose root-normalized gauge is the
identity on the entire root component of a supplied untwisted subgraph.
Choose a spanning forest of that subgraph and extend it to a spanning tree
of the region. The tree gauge is constant along every forest edge.

This is a noncommutative step toward the complementary contraction in SCP10,
arXiv:1001.3807v3, Lemma 6.14 and Theorem 6.9, lines 1935–1990 and 2199–2214.
Neither the untwisted subgraph nor its boundary connectivity is inferred from
endpoint exclusion here. See `docs/paper-gaps/scp10_anchored_tree_gauge.tex`.
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- Construct a root-normalized tree gauge that fixes the whole root component
of an untwisted subgraph and removes every internal tree operator. The tree,
forest and gauge are derived internally; no commutativity is required.
Auxiliary noncentral contraction step for SCP10, Lemma 6.14 and Theorem 6.9. -/
theorem exists_regularRegionTreeGauge_fixed_on_untwisted_component
    [Finite G]
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (U : SimpleGraph {v : V // v ∈ R}) (hU : U ≤ Γ.induce (R : Set V))
    (o : {v : V // v ∈ R}) (u : Edge Γ → G)
    (hu : ∀ {v w : {v : V // v ∈ R}} (h : U.Adj v w),
      regularDirectedTransport u (hU h) = 1) :
    ∃ (T : SimpleGraph {v : V // v ∈ R}) (k : {v : V // v ∈ R} → G),
      T ≤ Γ.induce (R : Set V) ∧ T.IsTree ∧ k o = 1 ∧
        (∀ v, U.Reachable o v → k v = 1) ∧
        ∀ e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R},
          T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩ →
            regularRegionGaugeResidual R k u e = 1 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨F, hFU, hFacyclic, hFreach⟩ := U.exists_isAcyclic_reachable_eq_le
  obtain ⟨T, hFT, hT, htree⟩ :=
    hR.exists_isTree_le_of_le_of_isAcyclic (hFU.trans hU) hFacyclic
  let k := (regularRegionTreeGauge R T hT htree o u).1
  have hedge {v w : {v : V // v ∈ R}} (h : F.Adj v w) : k w = k v := by
    have hg := regularRegionTreeGauge_directedTransport R T hT htree o u (v := v) (w := w)
      (hFT h) (hU (hFU h))
    have hz := hu (v := v) (w := w) (hFU h)
    have hg' : 1 = k w * (k v)⁻¹ := hz.symm.trans hg
    have hm := congrArg (fun z : G => z * k v) hg'
    simpa only [one_mul, mul_assoc, inv_mul_cancel, mul_one] using hm.symm
  have hwalk {v w : {v : V // v ∈ R}} (p : F.Walk v w) : k w = k v := by
    induction p with
    | nil => rfl
    | cons h p ih => exact ih.trans (hedge h)
  refine ⟨T, k, hT, htree, regularRegionTreeGauge_root R T hT htree o u, ?_, ?_⟩
  · intro v hv
    have hvF : F.Reachable o v := by rw [hFreach]; exact hv
    obtain ⟨p⟩ := hvF
    exact (hwalk p).trans (regularRegionTreeGauge_root R T hT htree o u)
  · intro e he
    exact regularRegionGaugeResidual_eq_one_of_tree R T hT htree o u e he

variable [Fintype G] [Fintype V] [DecidableRel Γ.Adj] {d : ℕ}

/-- If every complementary boundary endpoint belongs to the root's untwisted
component, construct a global gauge fixing the observation region and all its
incident operators while removing a complementary spanning tree. The actual
closed PEPS vector is preserved by local regular invariance. No centrality or
desired density identity is assumed. Auxiliary step for SCP10, Lemma 6.14. -/
theorem exists_regularComplementGauge_fixed_on_incident
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (R : Finset V) (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (U : SimpleGraph {v : V // v ∈ Finset.univ \ R})
    (hU : U ≤ Γ.induce ((Finset.univ \ R : Finset V) : Set V))
    (o : {v : V // v ∈ Finset.univ \ R}) (u : Edge Γ → G)
    (hu : ∀ {v w : {v : V // v ∈ Finset.univ \ R}} (h : U.Adj v w),
      regularDirectedTransport u (hU h) = 1)
    (hboundary : ∀ v : {v : V // v ∈ Finset.univ \ R},
      (∃ w ∈ R, Γ.Adj v.1 w) → U.Reachable o v)
    (hincident : ∀ e : Edge Γ, IsRegionIncidentEdge R e → u e = 1) :
    ∃ (T : SimpleGraph {v : V // v ∈ Finset.univ \ R}) (k : V → G),
      T ≤ Γ.induce ((Finset.univ \ R : Finset V) : Set V) ∧ T.IsTree ∧
        (∀ v ∈ R, k v = 1) ∧
        (∀ e : Edge Γ, IsRegionIncidentEdge R e →
          regularVertexGaugeOperators k u e = 1) ∧
        (∀ e : {e : Edge Γ // e.1.1 ∈ Finset.univ \ R ∧ e.1.2 ∈ Finset.univ \ R},
          T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩ →
            regularVertexGaugeOperators k u e.1 = 1) ∧
        SameState (groupBondTensor (regularTwistedSite a u))
          (groupBondTensor (regularTwistedSite a (regularVertexGaugeOperators k u))) := by
  classical
  let S := Finset.univ \ R
  obtain ⟨T, kS, hT, htree, _, hfixed, hremove⟩ :=
    exists_regularRegionTreeGauge_fixed_on_untwisted_component S hS U hU o u hu
  let k : V → G := fun v => if hv : v ∈ S then kS ⟨v, hv⟩ else 1
  have hkR (v : V) (hv : v ∈ R) : k v = 1 := by simp [k, S, hv]
  have hkB (v : V) (hv : ∃ w ∈ R, Γ.Adj v w) : k v = 1 := by
    by_cases hvR : v ∈ R
    · exact hkR v hvR
    · have hvS : v ∈ S := by simp [S, hvR]
      have hh := hfixed ⟨v, hvS⟩ (hboundary ⟨v, hvS⟩ hv)
      simpa only [k, dite_eq_left hvS] using hh
  refine ⟨T, k, hT, htree, hkR, ?_, ?_, sameState_regularVertexGauge a ha k u⟩
  · intro e he
    have ht : k e.1.1 = 1 := by
      rcases he with ht | hh
      · exact hkR _ ht
      · exact hkB _ ⟨e.1.2, hh, e.2.2⟩
    have hh : k e.1.2 = 1 := by
      rcases he with ht | hh
      · exact hkB _ ⟨e.1.1, ht, e.2.2.symm⟩
      · exact hkR _ hh
    simp only [regularVertexGaugeOperators, ht, hh, hincident e he, inv_one, one_mul]
  · intro e he
    have h := hremove e he
    have ht : e.1.1.1 ∈ S := e.2.1
    have hh : e.1.1.2 ∈ S := e.2.2
    change (k e.1.1.2)⁻¹ * u e.1 * k e.1.1.1 = 1
    dsimp only [k]
    rw [dite_eq_left hh, dite_eq_left ht]
    exact h

end TNLean.PEPS
