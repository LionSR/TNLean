/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusActualPlaquetteVacancy
import TNLean.PEPS.RegularActualCyclePhysicalPermutation

/-!
# A fixed native operation on arbitrary actual horizontal-patch inputs

The bond assignment determines its tree gauge and its two cycle residuals.
The controlled multiplication changes the middle residual by left multiplication
with the left residual and reconstructs using the original tree background.
Every exterior and crossing operator is retained. The physical unitary is
chosen before every input and every boundary column.

Source: SCP10, arXiv:1001.3807, accessible coordinates, lines 1765–1920,
and Theorem 6.16, lines 2271–2305.

**Scope restriction (finite torus and regular action):** Width is at least four
and height at least three. This operation uses the derived actual coordinates;
the accompanying vacancy lemma interprets a trivial neighbouring plaquette as
a trivial middle residual. The complete prescribed braid remains separate.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance actualHorizontalWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance actualHorizontalWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance actualHorizontalHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G] [Fintype G]

private def moveEquiv (p : X) : Equiv.Perm
    (RegionCycleEdge (Γ := Γₜ) (translatedTwoPlaquetteRegion p)
      (translatedTwoPlaquetteTree p) → G) :=
  regularTwoCycleMove (translatedTwoPlaquetteCycleBond p 0)
    (translatedTwoPlaquetteCycleBond p 1)
    ((translatedTwoPlaquetteCycleBond_injective p).ne (by decide))

/-- Reconstruct the changed residuals with the original derived tree gauge.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
def torusActualHorizontalFluxMove (p : X) (u : Edge Γₜ → G) : Edge Γₜ → G :=
  regularActualCyclePermutation (translatedTwoPlaquetteRegion p)
    (translatedTwoPlaquetteTree p) (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) (moveEquiv p) u

/-- Every actual ordered bond other than the middle chord is retained literally.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusActualHorizontalFluxMove_eq_of_ne (p : X) (u : Edge Γₜ → G)
    (e : Edge Γₜ) (hne : e ≠ (translatedTwoPlaquetteCycleBond p 1).1.1) :
    torusActualHorizontalFluxMove p u e = u e := by
  classical
  let R := translatedTwoPlaquetteRegion p
  let T := translatedTwoPlaquetteTree p
  let k := (regularRegionTreeGauge R T (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) u).1
  let ω := regularRegionTreeCycleResidual R T (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) u
  have hcycle : regularTreeCycleAssignment R T (moveEquiv p ω) e =
      regularTreeCycleAssignment R T ω e := by
    simp only [regularTreeCycleAssignment]
    split_ifs with ht hh hn
    · rfl
    · have hf : (⟨⟨e, ht, hh⟩, hn⟩ : RegionCycleEdge (Γ := Γₜ) R T) ≠
          translatedTwoPlaquetteCycleBond p 1 := by
        intro h
        exact hne (congrArg (fun f => f.1.1) h)
      simp only [moveEquiv, regularTwoCycleMove, Equiv.coe_fn_mk, ite_eq_right hf]
    all_goals rfl
  by_cases he : e.1.1 ∈ R ∧ e.1.2 ∈ R
  · have H := regularGaugedTreeCycleAssignment_treeGauge_of_internal R T
      (translatedTwoPlaquetteTree_le p) (translatedTwoPlaquetteTree_isTree p)
      (translatedTwoPlaquetteIso p 0) u e he
    change regularRegionBondExtension R
      (regularGaugedTreeCycleAssignment R T k (moveEquiv p ω)) u e = u e
    rw [regularRegionBondExtension, ite_eq_left he]
    rw [regularGaugedTreeCycleAssignment, dite_eq_left he, hcycle]
    simpa only [regularGaugedTreeCycleAssignment, dite_eq_left he] using H
  · change ¬ (e.1.1 ∈ translatedTwoPlaquetteRegion p ∧
      e.1.2 ∈ translatedTwoPlaquetteRegion p) at he
    simp only [torusActualHorizontalFluxMove, regularActualCyclePermutation,
      regularRegionBondExtension, ite_eq_right he]

/-- Vacancy determines the changed middle coefficient from the original
normalized gauge and the original left residual. Source: SCP10,
Theorem 6.16, lines 2271–2305. -/
theorem torusActualHorizontalFluxMove_middle_of_vacancy (p : X) (u : Edge Γₜ → G)
    (hv : regularWalkHolonomy u (torusPlaquetteWalk (p.1 + 1, p.2)) = 1) :
    let e := translatedTwoPlaquetteCycleBond p 1
    let k := (regularRegionTreeGauge (translatedTwoPlaquetteRegion p)
      (translatedTwoPlaquetteTree p) (translatedTwoPlaquetteTree_le p)
      (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) u).1
    torusActualHorizontalFluxMove p u e.1.1 =
      k ⟨e.1.1.1.2, e.1.2.2⟩ *
        regularRegionTreeCycleResidual (translatedTwoPlaquetteRegion p)
          (translatedTwoPlaquetteTree p) (translatedTwoPlaquetteTree_le p)
          (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) u
          (translatedTwoPlaquetteCycleBond p 0) *
        (k ⟨e.1.1.1.1, e.1.2.1⟩)⁻¹ := by
  classical
  have hres := (regularRegionTreeCycleResidual_middle_eq_one_iff_rightPlaquette p u).mpr hv
  dsimp only
  have he := (translatedTwoPlaquetteCycleBond p 1).1.2
  simp only [torusActualHorizontalFluxMove, regularActualCyclePermutation,
    regularRegionBondExtension, ite_eq_left he, regularGaugedTreeCycleAssignment,
    dite_eq_left he, regularTreeCycleAssignment, dite_eq_left he.1, dite_eq_left he.2,
    dite_eq_left (translatedTwoPlaquetteCycleBond p 1).2, moveEquiv, regularTwoCycleMove,
    Equiv.coe_fn_mk, ite_true,
    regularTweezerEquiv_symm_apply, hres, inv_one, mul_one]

/-- Vacancy determines the changed directed bond from three literal original
transports. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusActualHorizontalFluxMove_up_transport_of_vacancy (p : X)
    (u : Edge Γₜ → G)
    (hv : regularWalkHolonomy u (torusPlaquetteWalk (p.1 + 1, p.2)) = 1) :
    regularDirectedTransport (torusActualHorizontalFluxMove p u)
      (torusGraph_adj_up (p.1 + 1) p.2) =
      regularDirectedTransport u (torusGraph_adj_right p.1 (p.2 + 1)) *
        regularDirectedTransport u (torusGraph_adj_up p.1 p.2) *
        (regularDirectedTransport u (torusGraph_adj_right p.1 p.2))⁻¹ := by
  classical
  let R := translatedTwoPlaquetteRegion p
  let T := translatedTwoPlaquetteTree p
  let φ := translatedTwoPlaquetteIso p
  let k := (regularRegionTreeGauge R T (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (φ 0) u).1
  let ω := regularRegionTreeCycleResidual R T (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (φ 0) u
  have hres : ω (translatedTwoPlaquetteCycleBond p 1) = 1 :=
    (regularRegionTreeCycleResidual_middle_eq_one_iff_rightPlaquette p u).mpr hv
  have hA (z : RegionCycleEdge (Γ := Γₜ) R T → G) (i : Fin 2) :
      regularTreeCycleAssignment R T z
        (Edge.ofAdj (torusGraph_adj_up (p.1 + (i.val : ZMod width)) p.2)) =
      z (translatedTwoPlaquetteCycleBond p i) := by
    rw [← translatedTwoPlaquetteCycleBond_eq_up]
    change regularTreeCycleAssignment (translatedTwoPlaquetteRegion p)
      (translatedTwoPlaquetteTree p) z (translatedTwoPlaquetteCycleBond p i).1.1 = _
    simp only [regularTreeCycleAssignment,
      dite_eq_left (translatedTwoPlaquetteCycleBond p i).1.2.1,
      dite_eq_left (translatedTwoPlaquetteCycleBond p i).1.2.2,
      dite_eq_left (translatedTwoPlaquetteCycleBond p i).2]
  have horder : ((p.1 + 1, p.2) : X) < (p.1 + 1, p.2 + 1) ↔
      (p : X) < (p.1, p.2 + 1) := by
    change toLex ((p.1 + 1).val, p.2.val) < toLex ((p.1 + 1).val, (p.2 + 1).val) ↔
      toLex (p.1.val, p.2.val) < toLex (p.1.val, (p.2 + 1).val)
    simp only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or, true_and]
  have hcanon : regularDirectedTransport (regularTreeCycleAssignment R T (moveEquiv p ω))
      (torusGraph_adj_up (p.1 + 1) p.2) =
      regularDirectedTransport (regularTreeCycleAssignment R T ω)
        (torusGraph_adj_up p.1 p.2) := by
    have hA₀ := hA ω 0
    have hA₁ := hA (moveEquiv p ω) 1
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, add_zero] at hA₀ hA₁
    unfold regularDirectedTransport
    rw [hA₀, hA₁]
    simp only [Prod.mk.eta, horder, moveEquiv, regularTwoCycleMove, Equiv.coe_fn_mk,
      ite_true, regularTweezerEquiv_symm_apply, hres, inv_one, mul_one]
  have hcoords (i : Fin 6) := translatedTwoPlaquetteIso_vertex_coordinates p i
  have hv₀ := hcoords 0
  have hv₁ := hcoords 1
  have hv₄ := hcoords 4
  have hv₅ := hcoords 5
  norm_num at hv₀ hv₁ hv₄ hv₅
  have hm₀ : p ∈ R := by rw [← hv₀]; exact (φ 0).2
  have hm₁ : (p.1 + 1, p.2) ∈ R := by rw [← hv₁]; exact (φ 1).2
  have hm₄ : (p.1 + 1, p.2 + 1) ∈ R := by rw [← hv₄]; exact (φ 4).2
  have hm₅ : (p.1, p.2 + 1) ∈ R := by rw [← hv₅]; exact (φ 5).2
  have hs₀ : (⟨p, hm₀⟩ : {v : X // v ∈ R}) = φ 0 := Subtype.ext hv₀.symm
  have hs₁ : (⟨(p.1 + 1, p.2), hm₁⟩ : {v : X // v ∈ R}) = φ 1 := Subtype.ext hv₁.symm
  have hs₄ : (⟨(p.1 + 1, p.2 + 1), hm₄⟩ : {v : X // v ∈ R}) = φ 4 :=
    Subtype.ext hv₄.symm
  have hs₅ : (⟨(p.1, p.2 + 1), hm₅⟩ : {v : X // v ∈ R}) = φ 5 :=
    Subtype.ext hv₅.symm
  have hrec (e : Edge Γₜ) (he : e.1.1 ∈ R ∧ e.1.2 ∈ R) :
      u e = k ⟨e.1.2, he.2⟩ * regularTreeCycleAssignment R T ω e *
        (k ⟨e.1.1, he.1⟩)⁻¹ := by
    have H := regularGaugedTreeCycleAssignment_treeGauge_of_internal R T
      (translatedTwoPlaquetteTree_le p) (translatedTwoPlaquetteTree_isTree p) (φ 0) u e he
    simpa only [regularGaugedTreeCycleAssignment, dite_eq_left he] using H.symm
  have hnew (e : Edge Γₜ) (he : e.1.1 ∈ R ∧ e.1.2 ∈ R) :
      torusActualHorizontalFluxMove p u e =
        k ⟨e.1.2, he.2⟩ * regularTreeCycleAssignment R T (moveEquiv p ω) e *
          (k ⟨e.1.1, he.1⟩)⁻¹ := by
    change regularRegionBondExtension R
      (regularGaugedTreeCycleAssignment R T k (moveEquiv p ω)) u e = _
    simp only [regularRegionBondExtension, ite_eq_left he,
      regularGaugedTreeCycleAssignment, dite_eq_left he]
  have hl := regularDirectedTransport_eq_of_internal_reconstruction R k
    (regularTreeCycleAssignment R T ω) u hrec (torusGraph_adj_up p.1 p.2) hm₀ hm₅
  have hn := regularDirectedTransport_eq_of_internal_reconstruction R k
    (regularTreeCycleAssignment R T (moveEquiv p ω)) (torusActualHorizontalFluxMove p u)
    hnew (torusGraph_adj_up (p.1 + 1) p.2) hm₁ hm₄
  rw [hs₀, hs₅] at hl
  rw [hs₁, hs₄] at hn
  have htree {i j : Fin 6} (h : twoPlaquetteTree.Adj i j) : T.Adj (φ i) (φ j) := by
    change twoPlaquetteTree.Adj
      ((translatedTwoPlaquetteVertexEquiv p).symm (translatedTwoPlaquetteVertexEquiv p i))
      ((translatedTwoPlaquetteVertexEquiv p).symm (translatedTwoPlaquetteVertexEquiv p j))
    simpa only [Equiv.symm_apply_apply] using h
  have ht₀₁ := htree (by decide : twoPlaquetteTree.Adj 0 1)
  have ht₅₄ := htree (by decide : twoPlaquetteTree.Adj 5 4)
  have hb := regularRegionTreeGauge_directedTransport R T (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (φ 0) u ht₀₁
    (SimpleGraph.induce_adj.mp (translatedTwoPlaquetteTree_le p ht₀₁))
  have ht := regularRegionTreeGauge_directedTransport R T (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (φ 0) u ht₅₄
    (SimpleGraph.induce_adj.mp (translatedTwoPlaquetteTree_le p ht₅₄))
  rw [regularDirectedTransport_eq_of_endpoints u
    (SimpleGraph.induce_adj.mp (translatedTwoPlaquetteTree_le p ht₀₁))
    (torusGraph_adj_right p.1 p.2) hv₀ hv₁] at hb
  rw [regularDirectedTransport_eq_of_endpoints u
    (SimpleGraph.induce_adj.mp (translatedTwoPlaquetteTree_le p ht₅₄))
    (torusGraph_adj_right p.1 (p.2 + 1)) hv₅ hv₄] at ht
  change regularDirectedTransport u (torusGraph_adj_right p.1 p.2) =
    k (φ 1) * (k (φ 0))⁻¹ at hb
  change regularDirectedTransport u (torusGraph_adj_right p.1 (p.2 + 1)) =
    k (φ 4) * (k (φ 5))⁻¹ at ht
  rw [hn, hcanon, hl, hb, ht]
  group

/-- One original six-spin unitary performs the derived operation on every
actual input, before all boundary or exterior data. Source: SCP10,
Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusActualHorizontalFluxMove {d : ℕ}
    {a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ}
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (p : X) :
    ∃ W : Matrix ({v : X // v ∈ translatedTwoPlaquetteRegion p} → Fin d)
        ({v : X // v ∈ translatedTwoPlaquetteRegion p} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({v : X // v ∈ translatedTwoPlaquetteRegion p} → Fin d) ℂ ∧
      regionLocalTerm (translatedTwoPlaquetteRegion p) W ∈
        Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (u : Edge Γₜ → G)
          (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (translatedTwoPlaquetteRegion p) e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a u))
          (translatedTwoPlaquetteRegion p) (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (torusActualHorizontalFluxMove p u))) (translatedTwoPlaquetteRegion p)
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ u : Edge Γₜ → G,
        regionLocalTerm (translatedTwoPlaquetteRegion p) W *ᵥ
          stateCoeff (groupBondTensor (regularTwistedSite a u)) =
        stateCoeff (groupBondTensor (regularTwistedSite a (torusActualHorizontalFluxMove p u))) :=
  exists_unitary_regularActualCyclePhysicalPermutation (translatedTwoPlaquetteRegion p)
    (translatedTwoPlaquetteTree p) (translatedTwoPlaquetteTree_le p)
    (translatedTwoPlaquetteTree_isTree p) (translatedTwoPlaquetteIso p 0) a ha (moveEquiv p)
    (regularTwoCycleMove_conjugation _ _ _)

end TNLean.PEPS
