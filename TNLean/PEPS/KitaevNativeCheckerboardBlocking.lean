/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.KitaevCheckerboardBlocking
import TNLean.PEPS.GraphOpenRegionContraction
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.PEPS.EdgeMapSubgraph

/-!
# Native four-site checkerboard coefficients

The actual translated torus plaquette is identified with the four-site
contraction of SCP10, equations `eq:ex:kitaev-tens` and
`eq:ex:kitaev-colordiff-rep`, lines 2718–2827. The four internal bonds and the
native leg reads are derived from the actual plaquette, rather than supplied as
contraction hypotheses.

**Scope restriction (one locally oriented native block):** Both torus periods
are at least three, and the four corner orientations are prescribed on this
block. This does not construct a globally alternating field on an odd torus,
a globally tiled blocking, or a physical renormalization operation. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. No Hamiltonian claim
is made.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance kitaevNativeWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance kitaevNativeHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private abbrev RI (v : TV) :=
  {e : Edge Γₜ // e.1.1 ∈ torusPlaquetteRegion v ∧ e.1.2 ∈ torusPlaquetteRegion v}
private abbrev RB (v : TV) := {e : Edge Γₜ // IsRegionBoundaryEdge (torusPlaquetteRegion v) e}

private def point (v : TV) : Fin 4 → TV :=
  ![(v.1 + 1, v.2 + 1), (v.1 + 1, v.2), v, (v.1, v.2 + 1)]

private theorem point_mem (v : TV) (i : Fin 4) : point v i ∈ torusPlaquetteRegion v := by
  fin_cases i <;> simp [point, torusPlaquetteRegion, torusPlaquetteWalk,
    SimpleGraph.Walk.support]

omit [NeZero width] [NeZero height] in
private theorem point_injective (v : TV) : Function.Injective (point v) := by
  rcases v with ⟨x,y⟩
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [point, Prod.mk.injEq]

/-- The actual plaquette sites, clockwise from the upper right. Source: SCP10,
`eq:ex:kitaev-tens`, lines 2718–2794; local corner orientations only. -/
def kitaevNativeBlockVertexEquiv (v : TV) :
    Fin 4 ≃ {w : TV // w ∈ torusPlaquetteRegion v} :=
  Equiv.ofBijective (fun i => ⟨point v i, point_mem v i⟩) <| by
    refine ⟨fun i j h => point_injective v (congrArg Subtype.val h), ?_⟩
    intro w
    have hm := w.2
    have hm' : w.1 = (v.1 + 1,v.2) ∨ w.1 = (v.1 + 1,v.2 + 1) ∨
        w.1 = (v.1,v.2 + 1) ∨ w.1 = v := by
      simpa [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support] using hm
    rcases hm' with h | h | h | h
    · exact ⟨1, Subtype.ext (by simpa [point] using h.symm)⟩
    · exact ⟨0, Subtype.ext (by simpa [point] using h.symm)⟩
    · exact ⟨3, Subtype.ext (by simpa [point] using h.symm)⟩
    · exact ⟨2, Subtype.ext (by simpa [point] using h.symm)⟩

private def bond (v : TV) : Fin 4 → Edge Γₜ :=
  ![torusRightEdge (v.1,v.2 + 1), torusUpEdge (v.1 + 1,v.2),
    torusRightEdge v, torusUpEdge v]

private theorem bond_internal (v : TV) (i : Fin 4) :
    (bond v i).1.1 ∈ torusPlaquetteRegion v ∧
      (bond v i).1.2 ∈ torusPlaquetteRegion v := by
  have hr (x y : TV) (hadj : (Γₜ).Adj x y)
      (hx : x ∈ torusPlaquetteRegion v) (hy : y ∈ torusPlaquetteRegion v) :
      (Edge.ofAdj hadj).1.1 ∈ torusPlaquetteRegion v ∧
        (Edge.ofAdj hadj).1.2 ∈ torusPlaquetteRegion v := by
    rcases Edge.ofAdj_endpoints hadj with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩
    · simpa only [h₀,h₁] using And.intro hx hy
    · simpa only [h₀,h₁] using And.intro hy hx
  fin_cases i
  · exact hr _ _ (torusGraph_adj_right v.1 (v.2 + 1)) (point_mem v 3) (point_mem v 0)
  · exact hr _ _ (torusGraph_adj_up (v.1 + 1) v.2) (point_mem v 1) (point_mem v 0)
  · exact hr _ _ (torusGraph_adj_right v.1 v.2) (point_mem v 2) (point_mem v 1)
  · exact hr _ _ (torusGraph_adj_up v.1 v.2) (point_mem v 2) (point_mem v 3)

private theorem bond_injective (v : TV) : Function.Injective (bond v) := by
  rcases v with ⟨x,y⟩
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [bond, torusRightEdge_injective.eq_iff, torusUpEdge_injective.eq_iff,
      torusRightEdge_ne_torusUpEdge, Ne.symm (torusRightEdge_ne_torusUpEdge _ _)]

private theorem bond_surjective (v : TV) :
    Function.Surjective (fun i => (⟨bond v i, bond_internal v i⟩ : RI v)) := by
  intro e
  obtain ⟨i,hi⟩ := (kitaevNativeBlockVertexEquiv v).surjective ⟨e.1.1.1,e.2.1⟩
  obtain ⟨j,hj⟩ := (kitaevNativeBlockVertexEquiv v).surjective ⟨e.1.1.2,e.2.2⟩
  have hi' : point v i = e.1.1.1 := congrArg Subtype.val hi
  have hj' : point v j = e.1.1.2 := congrArg Subtype.val hj
  have hadj : (Γₜ).Adj (point v i) (point v j) := by
    simpa only [hi',hj'] using e.1.2.2
  rcases v with ⟨x,y⟩
  fin_cases i <;> fin_cases j <;>
    simp [point, torusGraph, torusHorizontalNeighbor, torusVerticalNeighbor] at hadj
  · refine ⟨1, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_up (x + 1) y) e.1 (Or.inr ⟨hj',hi'⟩)
  · refine ⟨0, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_right x (y + 1)) e.1 (Or.inr ⟨hj',hi'⟩)
  · refine ⟨1, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_up (x + 1) y) e.1 (Or.inl ⟨hi',hj'⟩)
  · refine ⟨2, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_right x y) e.1 (Or.inr ⟨hj',hi'⟩)
  · refine ⟨2, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_right x y) e.1 (Or.inl ⟨hi',hj'⟩)
  · refine ⟨3, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_up x y) e.1 (Or.inl ⟨hi',hj'⟩)
  · refine ⟨0, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_right x (y + 1)) e.1 (Or.inl ⟨hi',hj'⟩)
  · refine ⟨3, Subtype.ext ?_⟩
    exact Edge.ofAdj_eq_of_endpoints (torusGraph_adj_up x y) e.1 (Or.inr ⟨hj',hi'⟩)

private def bonds (v : TV) : Fin 4 ≃ RI v :=
  Equiv.ofBijective (fun i => ⟨bond v i,bond_internal v i⟩)
    ⟨fun _i _j h => bond_injective v (congrArg Subtype.val h), bond_surjective v⟩

private def crossing (v : TV) (i : Fin 4) (second : Bool) : Edge Γₜ :=
  ![torusUpEdge (v.1 + (if second then 1 else 0),v.2 + 1),
    torusRightEdge (v.1 + 1,v.2 + (if second then 0 else 1)),
    torusUpEdge (v.1 + (if second then 0 else 1),v.2 - 1),
    torusRightEdge (v.1 - 1,v.2 + (if second then 1 else 0))] i

private theorem two_step_ne {n : ℕ} [Fact (2 < n)] (x : ZMod n) : x + 1 + 1 ≠ x := by
  intro h
  exact zmod_not_add_one_eq_and_add_one_eq (x + 1) x ⟨rfl,h⟩

private theorem minus_one_ne_plus {n : ℕ} [Fact (2 < n)] (x : ZMod n) :
    x - 1 ≠ x + 1 := by
  intro h
  have hc := congrArg (fun t => t + 1) h
  simp only [sub_add_cancel] at hc
  exact two_step_ne x hc.symm

private theorem outside_vertical (v : TV) (x : ZMod width) (upper : Bool) :
    (x,if upper then v.2 + 1 + 1 else v.2 - 1) ∉ torusPlaquetteRegion v := by
  rcases v with ⟨vx,vy⟩
  have h₂ : (1 : ZMod height) + 1 ≠ 0 := by simpa using two_step_ne (0 : ZMod height)
  have hm := minus_one_ne_plus vy
  cases upper <;>
    simp [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
      Prod.mk.injEq, h₂, hm, add_assoc]

private theorem outside_horizontal (v : TV) (y : ZMod height) (right : Bool) :
    (if right then v.1 + 1 + 1 else v.1 - 1,y) ∉ torusPlaquetteRegion v := by
  rcases v with ⟨vx,vy⟩
  have h₂ : (1 : ZMod width) + 1 ≠ 0 := by simpa using two_step_ne (0 : ZMod width)
  have hm := minus_one_ne_plus vx
  cases right <;>
    simp [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
      Prod.mk.injEq, h₂, hm, add_assoc]

private theorem crossing_boundary (v : TV) (i : Fin 4) (second : Bool) :
    IsRegionBoundaryEdge (torusPlaquetteRegion v) (crossing v i second) := by
  have hr (x y : TV) (hadj : (Γₜ).Adj x y)
      (hx : (x ∈ torusPlaquetteRegion v ∧ y ∉ torusPlaquetteRegion v) ∨
        (x ∉ torusPlaquetteRegion v ∧ y ∈ torusPlaquetteRegion v)) :
      IsRegionBoundaryEdge (torusPlaquetteRegion v) (Edge.ofAdj hadj) := by
    rcases Edge.ofAdj_endpoints hadj with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩
    · simpa only [IsRegionBoundaryEdge,h₀,h₁] using hx
    · simpa only [IsRegionBoundaryEdge,h₀,h₁,or_comm,and_comm] using hx
  fin_cases i <;> cases second
  · simpa [crossing,torusUpEdge,torusRightEdge] using hr _ _ (torusGraph_adj_up v.1 (v.2 + 1))
      (Or.inl ⟨point_mem v 3, outside_vertical v v.1 true⟩)
  · simpa [crossing,torusUpEdge,torusRightEdge] using hr _ _ (torusGraph_adj_up (v.1 + 1) (v.2 + 1))
      (Or.inl ⟨point_mem v 0, outside_vertical v (v.1 + 1) true⟩)
  · simpa [crossing,torusUpEdge,torusRightEdge] using
      hr _ _ (torusGraph_adj_right (v.1 + 1) (v.2 + 1))
      (Or.inl ⟨point_mem v 0, outside_horizontal v (v.2 + 1) true⟩)
  · simpa [crossing,torusUpEdge,torusRightEdge] using hr _ _ (torusGraph_adj_right (v.1 + 1) v.2)
      (Or.inl ⟨point_mem v 1, outside_horizontal v v.2 true⟩)
  · simpa [crossing,torusUpEdge,torusRightEdge] using hr _ _ (torusGraph_adj_up (v.1 + 1) (v.2 - 1))
      (Or.inr ⟨outside_vertical v (v.1 + 1) false,
        by simpa [point] using point_mem v 1⟩)
  · simpa [crossing,torusUpEdge,torusRightEdge] using hr _ _ (torusGraph_adj_up v.1 (v.2 - 1))
      (Or.inr ⟨outside_vertical v v.1 false, by simpa [point] using point_mem v 2⟩)
  · simpa [crossing,torusUpEdge,torusRightEdge] using hr _ _ (torusGraph_adj_right (v.1 - 1) v.2)
      (Or.inr ⟨outside_horizontal v v.2 false, by simpa [point] using point_mem v 2⟩)
  · simpa [crossing,torusUpEdge,torusRightEdge] using
      hr _ _ (torusGraph_adj_right (v.1 - 1) (v.2 + 1))
      (Or.inr ⟨outside_horizontal v (v.2 + 1) false,
        by simpa [point] using point_mem v 3⟩)

private def boundary (v : TV) (i : Fin 4) (second : Bool) : RB v :=
  ⟨crossing v i second, crossing_boundary v i second⟩

private def legs (w : TV) : Fin 4 → IncidentEdge Γₜ w :=
  ![torusTopLeg w, torusRightLeg w, torusDownLeg w, torusLeftLeg w]

private def port (v : TV) : Fin 4 → Fin 4 → RI v ⊕ RB v :=
  ![![.inr (boundary v 0 true), .inr (boundary v 1 false),
      .inl (bonds v 1), .inl (bonds v 0)],
    ![.inl (bonds v 1), .inr (boundary v 1 true),
      .inr (boundary v 2 false), .inl (bonds v 2)],
    ![.inl (bonds v 3), .inl (bonds v 2),
      .inr (boundary v 2 true), .inr (boundary v 3 false)],
    ![.inr (boundary v 0 false), .inl (bonds v 0),
      .inl (bonds v 3), .inr (boundary v 3 true)]]

private theorem port_edge (v : TV) (i j : Fin 4) :
    (legs (point v i) j).1 = (port v i j).elim Subtype.val Subtype.val := by
  fin_cases i <;> fin_cases j <;>
    simp [legs, point, port, boundary, crossing, bonds, bond,
      torusTopLeg, torusRightLeg, torusDownLeg, torusLeftLeg,
      torusDownEdge, torusLeftEdge]

private def assembled (v : TV) (ξ : RI v → KitaevBit) (θ : RB v → KitaevBit) :=
  (graphRegionIncidentConfigEquiv (X := KitaevBit) (torusPlaquetteRegion v)).symm (ξ,θ)

private theorem assembled_internal (v : TV) (ξ : RI v → KitaevBit)
    (θ : RB v → KitaevBit) (e : RI v) :
    assembled v ξ θ ⟨e.1,Or.inl e.2.1⟩ = ξ e := by
  rw [← graphRegionIncidentConfigEquiv_apply_internal (torusPlaquetteRegion v)
    (assembled v ξ θ) e]
  exact congrArg (fun t => t.1 e) ((graphRegionIncidentConfigEquiv
    (X := KitaevBit) (torusPlaquetteRegion v)).apply_symm_apply (ξ,θ))

private theorem assembled_boundary (v : TV) (ξ : RI v → KitaevBit)
    (θ : RB v → KitaevBit) (e : RB v) :
    assembled v ξ θ ⟨e.1,isRegionBoundaryEdge_touches _ e.2⟩ = θ e := by
  rw [← graphRegionIncidentConfigEquiv_apply_boundary (torusPlaquetteRegion v)
    (assembled v ξ θ) e]
  exact congrArg (fun t => t.2 e) ((graphRegionIncidentConfigEquiv
    (X := KitaevBit) (torusPlaquetteRegion v)).apply_symm_apply (ξ,θ))

private theorem assembled_leg (v : TV) (ξ : RI v → KitaevBit)
    (θ : RB v → KitaevBit) (i j : Fin 4) :
    assembled v ξ θ ⟨(legs (point v i) j).1,
      isRegionIncidentEdge_of_regionVertex (torusPlaquetteRegion v)
        ⟨point v i,point_mem v i⟩ (legs (point v i) j)⟩ =
      (port v i j).elim ξ θ := by
  have he := port_edge v i j
  rcases hp : port v i j with e | e
  · rw [hp] at he
    have hh : (⟨(legs (point v i) j).1,
        isRegionIncidentEdge_of_regionVertex (torusPlaquetteRegion v)
          ⟨point v i,point_mem v i⟩ (legs (point v i) j)⟩ :
        {e : Edge Γₜ // IsRegionIncidentEdge (torusPlaquetteRegion v) e}) =
        ⟨e.1,Or.inl e.2.1⟩ := Subtype.ext he
    rw [hh]
    exact assembled_internal v ξ θ e
  · rw [hp] at he
    have hh : (⟨(legs (point v i) j).1,
        isRegionIncidentEdge_of_regionVertex (torusPlaquetteRegion v)
          ⟨point v i,point_mem v i⟩ (legs (point v i) j)⟩ :
        {e : Edge Γₜ // IsRegionIncidentEdge (torusPlaquetteRegion v) e}) =
        ⟨e.1,isRegionBoundaryEdge_touches _ e.2⟩ := Subtype.ext he
    rw [hh]
    exact assembled_boundary v ξ θ e

/-- The elementary tensor placed at the four native corners, with precisely the
checkerboard orientations of SCP10, lines 2718–2794. This locally prescribed
family does not assert a global checkerboard field on an odd torus. -/
def kitaevNativeCheckerboardSite (v w : TV) (η : IncidentEdge Γₜ w → KitaevBit)
    (s : KitaevBit) : ℂ :=
  kitaevElementaryTensor (decide (w = (v.1 + 1,v.2 + 1) ∨ w = v))
    (fun j => η (legs w j)) s

/-- Read the eight actual crossing labels in clockwise boundary-pair order.
Source: SCP10, the four-site blocking diagram, lines 2755–2794. -/
def kitaevNativeBlockBoundary (v : TV)
    (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (torusPlaquetteRegion v) e} → KitaevBit) :
    KitaevBlockBoundary :=
  fun i => (θ (boundary v i false),θ (boundary v i true))

omit [NeZero width] [NeZero height] in
private theorem corner_orientation (v : TV) (i : Fin 4) :
    decide (point v i = (v.1 + 1,v.2 + 1) ∨ point v i = v) =
      decide (i = 0 ∨ i = 2) := by
  rcases v with ⟨x,y⟩
  fin_cases i <;> simp [point]

private theorem site_assembled (v : TV) (ξ : RI v → KitaevBit)
    (θ : RB v → KitaevBit) (i : Fin 4) (s : KitaevBit) :
    kitaevNativeCheckerboardSite v (point v i)
      (fun e => assembled v ξ θ ⟨e.1,
        isRegionIncidentEdge_of_regionVertex (torusPlaquetteRegion v)
          ⟨point v i,point_mem v i⟩ e⟩) s =
      kitaevElementaryTensor (decide (i = 0 ∨ i = 2))
        (fun j => (port v i j).elim ξ θ) s := by
  unfold kitaevNativeCheckerboardSite
  rw [corner_orientation]
  congr 1
  funext j
  exact assembled_leg v ξ θ i j

private def cornerLabels (v : TV) (x : Fin 4 → KitaevBit)
    (θ : RB v → KitaevBit) : Fin 4 → Fin 4 → KitaevBit :=
  ![![θ (boundary v 0 true),θ (boundary v 1 false),x 1,x 0],
    ![x 1,θ (boundary v 1 true),θ (boundary v 2 false),x 2],
    ![x 3,x 2,θ (boundary v 2 true),θ (boundary v 3 false)],
    ![θ (boundary v 0 false),x 0,x 3,θ (boundary v 3 true)]]

private theorem port_labels (v : TV) (x : Fin 4 → KitaevBit)
    (θ : RB v → KitaevBit) (i : Fin 4) :
    (fun j => (port v i j).elim (((bonds v).arrowCongr (Equiv.refl KitaevBit)) x) θ) =
      cornerLabels v x θ i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [port,cornerLabels,Equiv.arrowCongr_apply]

/-- The actual open contraction on any translated native plaquette equals the
four-site checkerboard block, for every crossing assignment and every original
physical spin configuration. Source: SCP10, lines 2755–2827. The two periods are
at least three; orientations are prescribed locally, without a global tiling. -/
theorem graphOpenRegionNetwork_kitaevNativeCheckerboardSite (v : TV)
    (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (torusPlaquetteRegion v) e} → KitaevBit)
    (σ : {w : TV // w ∈ torusPlaquetteRegion v} → KitaevBit) :
    graphOpenRegionNetwork (kitaevNativeCheckerboardSite v) (torusPlaquetteRegion v) θ σ =
      kitaevCheckerboardBlock (kitaevNativeBlockBoundary v θ)
        (fun i => σ (kitaevNativeBlockVertexEquiv v i)) := by
  classical
  rw [graphOpenRegionNetwork_eq_sum_internal]
  let E : (Fin 4 → KitaevBit) ≃ (RI v → KitaevBit) :=
    (bonds v).arrowCongr (Equiv.refl KitaevBit)
  rw [← E.sum_comp]
  unfold kitaevCheckerboardBlock
  apply Finset.sum_congr rfl
  intro x _
  rw [← (kitaevNativeBlockVertexEquiv v).prod_comp]
  change (∏ i : Fin 4, kitaevNativeCheckerboardSite v (point v i)
    (fun e => assembled v (E x) θ ⟨e.1,
      isRegionIncidentEdge_of_regionVertex (torusPlaquetteRegion v)
        ⟨point v i,point_mem v i⟩ e⟩)
      (σ (kitaevNativeBlockVertexEquiv v i))) = _
  simp_rw [site_assembled]
  change _ =
    kitaevElementaryTensor false
      ![θ (boundary v 0 false),x 0,x 3,θ (boundary v 3 true)]
      (σ (kitaevNativeBlockVertexEquiv v 3)) *
    kitaevElementaryTensor true
      ![θ (boundary v 0 true),θ (boundary v 1 false),x 1,x 0]
      (σ (kitaevNativeBlockVertexEquiv v 0)) *
    kitaevElementaryTensor false
      ![x 1,θ (boundary v 1 true),θ (boundary v 2 false),x 2]
      (σ (kitaevNativeBlockVertexEquiv v 1)) *
    kitaevElementaryTensor true
      ![x 3,x 2,θ (boundary v 2 true),θ (boundary v 3 false)]
      (σ (kitaevNativeBlockVertexEquiv v 2))
  simp_rw [show E = (bonds v).arrowCongr (Equiv.refl KitaevBit) from rfl,port_labels]
  rw [Fin.prod_univ_four]
  have hr (a b c d : ℂ) : a * b * c * d = d * a * b * c := by ring
  exact hr _ _ _ _

/-- The native contraction is nonzero exactly at equal boundary pairs and the
four adjacent color differences. Source: SCP10, lines 2755–2827. Every actual
crossing label remains in the statement. -/
theorem graphOpenRegionNetwork_kitaevNativeCheckerboardSite_apply (v : TV)
    (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (torusPlaquetteRegion v) e} → KitaevBit)
    (σ : {w : TV // w ∈ torusPlaquetteRegion v} → KitaevBit) :
    graphOpenRegionNetwork (kitaevNativeCheckerboardSite v) (torusPlaquetteRegion v) θ σ =
      if (∀ i, (kitaevNativeBlockBoundary v θ i).2 =
          (kitaevNativeBlockBoundary v θ i).1) ∧
        (fun i => σ (kitaevNativeBlockVertexEquiv v i)) =
          kitaevBlockColorSpins (fun i => (kitaevNativeBlockBoundary v θ i).1)
      then 1 else 0 := by
  rw [graphOpenRegionNetwork_kitaevNativeCheckerboardSite,kitaevCheckerboardBlock_apply]

end TNLean.PEPS
