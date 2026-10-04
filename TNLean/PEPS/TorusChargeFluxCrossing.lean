/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusChargeStringDeformation
import TNLean.PEPS.ThreePlaquetteGeometry
import TNLean.PEPS.RegularChargeFluxPhysicalTransport
import TNLean.Algebra.ZModSmallDifference

/-!
# An original-spin charge crossing beside an actual flux endpoint

The eight-site strip lies above the middle row of the source's deformation
figure and extends one column to its left. Its leftmost plaquette contains
the first flux endpoint. The charge reference is the central horizontal edge
of the lower row. Tree gauges and the residual flux are computed from the
literal initial string, including periodic seams.

Source: SCP10, arXiv:1001.3807, lines 2560–2581.
**Scope restriction (local crossing):** This finite-strip physical operation
is not identified with the complete prescribed braid or its reunion experiment.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (3 < height)]
local instance crossingHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance crossingWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance crossingHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance crossingWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G]

private abbrev base (v : X) : X := (v.1 - 1, v.2 + 1)
/-- The actual eight-site strip containing the flux endpoint and the displayed charge bond.
Source: SCP10, charge–flux crossing, lines 2560–2581; auxiliary finite-strip geometry. -/
abbrev torusChargeFluxCrossingRegion (v : X) : Finset X :=
  translatedThreePlaquetteRegion (v.1-1,v.2+1)
private abbrev R (v : X) := torusChargeFluxCrossingRegion v
private abbrev T (v : X) := translatedThreePlaquetteTree (base v)
private abbrev E (v : X) := translatedThreePlaquetteVertexEquiv (base v)

private theorem vertex_table (v : X) (i : Fin 8) :
    (E v i).1 =
      ![(v.1-1,v.2+1),(v.1,v.2+1),(v.1+1,v.2+1),(v.1+2,v.2+1),
        (v.1+2,v.2+2),(v.1+1,v.2+2),(v.1,v.2+2),(v.1-1,v.2+2)] i := by
  have h : (E v i).1 =
      ((![0,1,2,3,3,2,1,0] i : ℕ) + (v.1-1),
       (![0,0,0,0,1,1,1,1] i : ℕ) + (v.2+1)) := rfl
  rw [h]
  fin_cases i <;> ext <;> norm_num <;> ring

omit [NeZero height] in
private theorem one_ne_zero_height : (1 : ZMod height) ≠ 0 := by
  exact one_ne_zero

private def rowGauge (v : X) (k : G) : RootedGroupLabels (G := G) (E v 0) :=
  ⟨fun w => if w.1.2 = v.2 + 1 then 1 else k, by
    change (if (E v 0).1.2 = v.2+1 then (1:G) else k) = 1
    rw [vertex_table]
    simp⟩

private theorem rowGauge_vertex (v : X) (k : G) (i : Fin 8) :
    (rowGauge v k).1 (E v i) = ![1,1,1,1,k,k,k,k] i := by
  rw [rowGauge]
  change (if (E v i).1.2 = v.2+1 then 1 else k) = _
  rw [vertex_table]
  have h21 : (2 : ZMod height) ≠ 1 := by
    intro h
    have h' : (1 : ZMod height) + 1 = 1 + 0 := by
      simpa only [one_add_one_eq_two, add_zero] using h
    exact one_ne_zero_height (add_left_cancel h')
  fin_cases i <;> simp [h21]

variable [Fintype G]

private theorem tree_directed_gradient (v : X) (u : Edge Γₜ → G)
    (i j : Fin 8) (hij : (T v).Adj (E v i) (E v j)) :
    let κ := (regularRegionTreeGauge (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0) u).1
    κ (E v j) * (κ (E v i))⁻¹ =
      regularDirectedTransport u
        (show (Γₜ).Adj (E v i).1 (E v j).1 from
          translatedThreePlaquetteTree_le (base v) hij) := by
  dsimp only
  let a := E v i
  let b := E v j
  let h : (Γₜ).Adj a.1 b.1 := translatedThreePlaquetteTree_le (base v) hij
  change _ = regularDirectedTransport u h
  rcases lt_or_gt_of_ne h.ne with hab | hba
  · let e : {e : Edge Γₜ // e.1.1 ∈ R v ∧ e.1.2 ∈ R v} :=
      ⟨⟨(a.1,b.1),hab,h⟩,a.2,b.2⟩
    rw [regularDirectedTransport_of_lt _ _ hab]
    exact regularRegionTreeGauge_gradient (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0) u e hij
  · let e : {e : Edge Γₜ // e.1.1 ∈ R v ∧ e.1.2 ∈ R v} :=
      ⟨⟨(b.1,a.1),hba,h.symm⟩,b.2,a.2⟩
    rw [regularDirectedTransport_of_gt _ _ hba]
    have hg := regularRegionTreeGauge_gradient (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0) u e hij.symm
    change _ = _ at hg
    have hg' :
        (regularRegionTreeGauge (R v) (T v)
          (translatedThreePlaquetteTree_le (base v))
          (translatedThreePlaquetteTree_isTree (base v)) (E v 0) u).1 (E v i) *
        ((regularRegionTreeGauge (R v) (T v)
          (translatedThreePlaquetteTree_le (base v))
          (translatedThreePlaquetteTree_isTree (base v)) (E v 0) u).1 (E v j))⁻¹ =
        u e.1 := hg
    rw [← hg']
    group

private theorem path_step (v : X) (i : Fin 7) :
    (T v).Adj (E v i.castSucc) (E v i.succ) := by
  change (SimpleGraph.pathGraph 8).Adj
    ((E v).symm (E v i.castSucc)) ((E v).symm (E v i.succ))
  simp only [Equiv.symm_apply_apply, SimpleGraph.pathGraph_adj]
  exact Or.inl rfl

omit [Fintype G] in
private theorem transport_eq_of_vertices (u : Edge Γₜ → G) {a b c d : X}
    (h : (Γₜ).Adj a b) (h' : (Γₜ).Adj c d) (ha : a = c) (hb : b = d) :
    regularDirectedTransport u h = regularDirectedTransport u h' := by
  subst c d
  rfl

omit [Fintype G] in
private theorem source_horizontal_one (v q : X) (k : G) :
    regularDirectedTransport (torusSweptStringInitialOperators v k 1)
        (torusGraph_adj_right q.1 q.2) = 1 ∧
      regularDirectedTransport (torusSweptStringInitialOperators v k 1)
        (torusGraph_adj_right q.1 q.2).symm = 1 := by
  have h : regularDirectedTransport (torusSweptStringInitialOperators v k 1)
      (torusGraph_adj_right q.1 q.2) = 1 := by
    simpa only [torusSweptStringInitialRight, inv_one, ite_self] using
      torusSweptStringInitialOperators_right_transport v q k (1 : G)
  refine ⟨h,?_⟩
  rw [regularDirectedTransport_symm _ (torusGraph_adj_right q.1 q.2), h, inv_one]

omit [Fintype G] in
private theorem source_path_transport (v : X) (k : G) (i : Fin 7) :
    regularDirectedTransport (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v i.castSucc).1 (E v i.succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v i)) =
      ![1,1,1,k,1,1,1] i := by
  fin_cases i
  · let q : X := (v.1-1,v.2+1)
    have hcoord := transport_eq_of_vertices
      (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v (0 : Fin 7).castSucc).1
          (E v (0 : Fin 7).succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v 0))
      (torusGraph_adj_right q.1 q.2)
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
    rw [hcoord]
    exact (source_horizontal_one v q k).1
  · let q : X := (v.1,v.2+1)
    have hcoord := transport_eq_of_vertices
      (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v (1 : Fin 7).castSucc).1
          (E v (1 : Fin 7).succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v 1))
      (torusGraph_adj_right q.1 q.2)
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
    rw [hcoord]
    exact (source_horizontal_one v q k).1
  · let q : X := (v.1+1,v.2+1)
    have hcoord := transport_eq_of_vertices
      (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v (2 : Fin 7).castSucc).1
          (E v (2 : Fin 7).succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v 2))
      (torusGraph_adj_right q.1 q.2)
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
    rw [hcoord]
    exact (source_horizontal_one v q k).1
  · let q : X := (v.1+2,v.2+1)
    have hcoord := transport_eq_of_vertices
      (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v (3 : Fin 7).castSucc).1
          (E v (3 : Fin 7).succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v 3))
      (torusGraph_adj_up q.1 q.2)
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
    rw [hcoord]
    have ht := torusSweptStringInitialOperators_up_transport v q k (1 : G)
    simpa [q, torusSweptStringInitialUp] using ht
  · let q : X := (v.1+1,v.2+2)
    have hcoord := transport_eq_of_vertices
      (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v (4 : Fin 7).castSucc).1
          (E v (4 : Fin 7).succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v 4))
      (torusGraph_adj_right q.1 q.2).symm
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
    rw [hcoord]
    exact (source_horizontal_one v q k).2
  · let q : X := (v.1,v.2+2)
    have hcoord := transport_eq_of_vertices
      (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v (5 : Fin 7).castSucc).1
          (E v (5 : Fin 7).succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v 5))
      (torusGraph_adj_right q.1 q.2).symm
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
    rw [hcoord]
    exact (source_horizontal_one v q k).2
  · let q : X := (v.1-1,v.2+2)
    have hcoord := transport_eq_of_vertices
      (torusSweptStringInitialOperators v k 1)
      (show (Γₜ).Adj (E v (6 : Fin 7).castSucc).1
          (E v (6 : Fin 7).succ).1 from
        translatedThreePlaquetteTree_le (base v) (path_step v 6))
      (torusGraph_adj_right q.1 q.2).symm
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
      (by norm_num [vertex_table, q, sub_eq_add_neg, add_assoc])
    rw [hcoord]
    exact (source_horizontal_one v q k).2

private theorem source_treeGauge_vertex (v : X) (k : G) (i : Fin 8) :
    (regularRegionTreeGauge (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0)
      (torusSweptStringInitialOperators v k 1)).1 (E v i) =
      ![1,1,1,1,k,k,k,k] i := by
  induction i using Fin.induction with
  | zero => exact regularRegionTreeGauge_root _ _ _ _ _ _
  | succ i hi =>
    have hg := tree_directed_gradient v
      (torusSweptStringInitialOperators v k 1) i.castSucc i.succ (path_step v i)
    dsimp only at hg
    rw [source_path_transport] at hg
    have hs := mul_inv_eq_iff_eq_mul.mp hg
    rw [hi] at hs
    fin_cases i <;> simpa using hs

private theorem source_treeGauge (v : X) (k : G) :
    regularRegionTreeGauge (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0)
      (torusSweptStringInitialOperators v k 1) = rowGauge v k := by
  apply Subtype.ext
  funext w
  obtain ⟨i,rfl⟩ := (E v).surjective w
  rw [source_treeGauge_vertex, rowGauge_vertex]

omit [Fintype G] in
private theorem source_up_left (v : X) (k : G) :
    torusSweptStringInitialOperators v k 1
      (Edge.ofAdj (torusGraph_adj_up (v.1-1) (v.2+1))) = 1 := by
  have hx : ∀ i : Fin 4, v.1-1 ≠ v.1 + (i.val : ZMod width) := by
    intro i hi
    rw [sub_eq_add_neg] at hi
    have he : ((-1 : ℤ) : ZMod width) = ((i.val : ℤ) : ZMod width) := by
      simpa only [Int.cast_neg, Int.cast_one, Int.cast_natCast, sub_eq_add_neg] using
        (add_left_cancel hi)
    have hd : ((i.val : ℤ) - (-1)).natAbs < width := by
      have hw := Fact.out (p := 4 < width)
      fin_cases i <;> norm_num <;> omega
    have := (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt (-1) i.val hd).mp he
    omega
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  norm_num at h0 h1 h2 h3
  have ht := torusSweptStringInitialOperators_up_transport v (v.1-1,v.2+1) k (1 : G)
  have ht' : regularDirectedTransport (torusSweptStringInitialOperators v k 1)
      (torusGraph_adj_up (v.1-1) (v.2+1)) = 1 := by
    simpa [torusSweptStringInitialUp, h0, h1, h2, h3] using ht
  simp only [regularDirectedTransport] at ht'
  split_ifs at ht' <;> simpa only [inv_eq_one] using ht'

omit [Fintype G] in
/-- The actual displayed horizontal charge bond, with its derived internal-edge certificate.
Source: SCP10, charge–flux crossing, lines 2560–2581. -/
def torusChargeFluxCrossingChargeBond (v : X) :
    {e : Edge Γₜ // e.1.1 ∈ torusChargeFluxCrossingRegion v ∧
      e.1.2 ∈ torusChargeFluxCrossingRegion v} := by
  refine ⟨torusSweptStringChargeEdge v, ?_⟩
  have h2 : (v.1+1,v.2+1) ∈ R v := by
    have h := (E v 2).2
    simpa [vertex_table] using h
  have h3 : (v.1+2,v.2+1) ∈ R v := by
    have h := (E v 3).2
    simpa [vertex_table] using h
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right (v.1+1) (v.2+1)) with
    ⟨ht,hh⟩ | ⟨ht,hh⟩
  · change (Edge.ofAdj _).1.1 ∈ _ ∧ (Edge.ofAdj _).1.2 ∈ _
    rw [ht,hh]
    simpa only [add_assoc, one_add_one_eq_two] using And.intro h2 h3
  · change (Edge.ofAdj _).1.1 ∈ _ ∧ (Edge.ofAdj _).1.2 ∈ _
    rw [ht,hh]
    simpa only [add_assoc, one_add_one_eq_two] using And.intro h3 h2

private theorem source_charge_tail (v : X) (k : G) :
    (regularRegionTreeGauge (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0)
      (torusSweptStringInitialOperators v k 1)).1
      ⟨(torusChargeFluxCrossingChargeBond v).1.1.1,
        (torusChargeFluxCrossingChargeBond v).2.1⟩ = 1 := by
  rw [source_treeGauge]
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right (v.1+1) (v.2+1)) with
    ⟨ht,hh⟩ | ⟨ht,hh⟩ <;>
    simp [rowGauge, torusChargeFluxCrossingChargeBond, torusSweptStringChargeEdge, ht]

private theorem source_cycle_residual (v : X) (k : G) :
    regularRegionTreeCycleResidual (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0)
      (torusSweptStringInitialOperators v k 1)
      (translatedThreePlaquetteCycleBond (base v) 0) =
      if (v.1-1,v.2+1) < (v.1-1,v.2+2) then k⁻¹ else k := by
  let b := translatedThreePlaquetteCycleBond (base v) 0
  have hb : b.1.1 = Edge.ofAdj (torusGraph_adj_up (v.1-1) (v.2+1)) := by
    simpa [b, base] using translatedThreePlaquetteCycleBond_eq_up (base v) 0
  have hu : torusSweptStringInitialOperators v k 1 b.1.1 = 1 := by
    rw [hb]
    exact source_up_left v k
  have h21 : (2 : ZMod height) ≠ 1 := by
    intro h
    have h' : (1 : ZMod height) + 1 = 1 + 0 := by
      simpa only [one_add_one_eq_two, add_zero] using h
    exact one_ne_zero_height (add_left_cancel h')
  change regularRegionGaugeResidual (R v)
    (regularRegionTreeGauge (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0)
      (torusSweptStringInitialOperators v k 1)).1
    (torusSweptStringInitialOperators v k 1) b.1 = _
  rw [source_treeGauge]
  by_cases ho : (v.1-1,v.2+1) < (v.1-1,v.2+2)
  · have hp : (b.1.1).1 = ((v.1-1,v.2+1),(v.1-1,v.2+2)) := by
      rw [hb, Edge.ofAdj_of_lt _ (by simpa only [add_assoc, one_add_one_eq_two] using ho)]
      simp only [add_assoc, one_add_one_eq_two]
    simp [regularRegionGaugeResidual, rowGauge, hu, hp, ho, h21]
  · have hr : (v.1-1,v.2+2) < (v.1-1,v.2+1) := by
      apply lt_of_le_of_ne (not_lt.mp ho)
      intro he
      exact h21 (add_left_cancel (congrArg Prod.snd he))
    have hp : (b.1.1).1 = ((v.1-1,v.2+2),(v.1-1,v.2+1)) := by
      rw [hb, Edge.ofAdj_of_gt _ (by simpa only [add_assoc, one_add_one_eq_two] using hr)]
      simp only [add_assoc, one_add_one_eq_two]
    simp [regularRegionGaugeResidual, rowGauge, hu, hp, ho, h21]

private theorem source_parameter (v : X) (k p : G) :
    regularChargeFluxParameter (R v) (T v)
      (translatedThreePlaquetteTree_le (base v))
      (translatedThreePlaquetteTree_isTree (base v)) (E v 0)
      (torusChargeFluxCrossingChargeBond v)
      (translatedThreePlaquetteCycleBond (base v) 0)
      (torusSweptStringInitialOperators v k 1) p =
      if (v.1-1,v.2+1) < (v.1-1,v.2+2) then p*k else p*k⁻¹ := by
  unfold regularChargeFluxParameter
  dsimp only
  rw [source_charge_tail, source_cycle_residual]
  split_ifs <;> simp

variable [DecidableEq G]
/-- A fixed original-spin unitary beside the literal flux endpoint implements the charge
parameter change, uniformly in the inserted flux, character and open boundary column.
Source: SCP10, lines 2560–2581. This is the auxiliary eight-site crossing operation. -/
theorem IsGIsometric.exists_unitary_torusChargeFluxCrossing {d : ℕ}
    (a : G → G → G → G → Fin d → ℂ)
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d)
        ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d) ℂ ∧
      ∀ (k : G) (χ : G → ℂ) (p : G)
        (θ : {f : Edge Γₜ // IsRegionBoundaryEdge (torusChargeFluxCrossingRegion v) f} → G),
        W *ᵥ regularWeightedOpenRegionWeight (torusIncidentSite a)
          (torusChargeFluxCrossingRegion v) (torusSweptStringInitialOperators v k 1)
          (fun η => χ (p * η ⟨(torusChargeFluxCrossingChargeBond v).1,
            Or.inl (torusChargeFluxCrossingChargeBond v).2.1⟩)) θ =
        regularWeightedOpenRegionWeight (torusIncidentSite a)
          (torusChargeFluxCrossingRegion v) (torusSweptStringInitialOperators v k 1)
          (fun η => χ ((p*k⁻¹) * η ⟨(torusChargeFluxCrossingChargeBond v).1,
            Or.inl (torusChargeFluxCrossingChargeBond v).2.1⟩)) θ := by
  classical
  obtain ⟨W,hW,hact⟩ := exists_unitary_regularChargeFluxPhysicalTransport
    (torusIncidentSite (width := width) (height := height) a)
    (fun w => ha.isGIsometric_torusIncidentSite w) (R v) (T v)
    (translatedThreePlaquetteTree_le (base v))
    (translatedThreePlaquetteTree_isTree (base v)) (E v 0)
    (torusChargeFluxCrossingChargeBond v) (translatedThreePlaquetteCycleBond (base v) 0)
  by_cases ho : (v.1-1,v.2+1) < (v.1-1,v.2+2)
  · refine ⟨W.conjTranspose, ?_, ?_⟩
    · exact (Unitary.star_mem hW)
    · intro k χ p θ
      have h := hact (torusSweptStringInitialOperators v k 1) χ (p*k⁻¹) θ
      rw [source_parameter, ite_eq_left ho] at h
      have hp : p*k⁻¹*k = p := by group
      rw [hp] at h
      have h' := congrArg (fun ψ => W.conjTranspose *ᵥ ψ) h
      have hGram : W.conjTranspose * W = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hW
      rw [Matrix.mulVec_mulVec, hGram, Matrix.one_mulVec] at h'
      exact h'.symm
  · refine ⟨W,hW,?_⟩
    intro k χ p θ
    have h := hact (torusSweptStringInitialOperators v k 1) χ p θ
    rw [source_parameter, ite_eq_right ho] at h
    exact h

/-- The same type of fixed physical crossing retains the literal correlated charge-pair
order, uniformly in the unsummed partner reference. Source: SCP10, lines 2505–2535
and 2560–2581. No product decomposition of the charge-pair weight is used. -/
theorem IsGIsometric.exists_unitary_torusCorrelatedChargeFluxCrossing {d : ℕ}
    (a : G → G → G → G → Fin d → ℂ)
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d)
        ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d) ℂ ∧
      ∀ (k : G) (χ : G → ℂ) (p q : G)
        (θ : {f : Edge Γₜ // IsRegionBoundaryEdge (torusChargeFluxCrossingRegion v) f} → G),
        W *ᵥ regularWeightedOpenRegionWeight (torusIncidentSite a)
          (torusChargeFluxCrossingRegion v) (torusSweptStringInitialOperators v k 1)
          (fun η => χ (p*q⁻¹ * η ⟨(torusChargeFluxCrossingChargeBond v).1,
            Or.inl (torusChargeFluxCrossingChargeBond v).2.1⟩)) θ =
        regularWeightedOpenRegionWeight (torusIncidentSite a)
          (torusChargeFluxCrossingRegion v) (torusSweptStringInitialOperators v k 1)
          (fun η => χ (p*q⁻¹*k⁻¹ * η ⟨(torusChargeFluxCrossingChargeBond v).1,
            Or.inl (torusChargeFluxCrossingChargeBond v).2.1⟩)) θ := by
  obtain ⟨W,hW,hact⟩ := IsGIsometric.exists_unitary_torusChargeFluxCrossing a ha v
  refine ⟨W,hW,?_⟩
  intro k χ p q θ
  simpa only [one_mul, mul_assoc] using hact k (fun t => χ (p*q⁻¹*t)) 1 θ

end TNLean.PEPS
