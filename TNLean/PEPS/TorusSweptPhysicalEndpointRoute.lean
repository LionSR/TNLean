/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSweptPatchEndpointGeometry

/-!
# An actual endpoint route surrounding the other flux endpoint

The twelve-step plaquette-base route starts at B1, circles the native A1 base,
and ends immediately left of B2. Its thirteen plaquette footprints, together
with the existing twenty-site witness, require thirty physical vertices.
The route has a chosen clockwise orientation in the present coordinate
convention. This is geometry for the physical movement discussed in SCP10,
arXiv:1001.3807, lines 2340–2423; no braid or movement identity is asserted.
-/
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance sweptPhysicalRouteWidthSix : Fact (6 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance sweptPhysicalRouteHeightFive : Fact (5 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance sweptPhysicalRouteWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptPhysicalRouteHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The offsets of the endpoint route, shifted by `(1,2)` as in the existing
coordinate witness. Source: SCP10, physical fluxon motion, lines 2340–2423. -/
def sweptPhysicalBRouteCoordinate : Fin 13 → Fin 6 × Fin 5 :=
  ![(2,3),(3,3),(3,4),(4,4),(5,4),(5,3),(5,2),
    (4,2),(3,2),(2,2),(1,2),(1,1),(1,0)]

/-- The translated native vertices of the endpoint route. -/
def torusSweptPhysicalBRouteVertex (v : X) (i : Fin 13) : X :=
  torusSweptPatchCoordinate v (sweptPhysicalBRouteCoordinate i)

private theorem route_adj (v : X) (i : Fin 12) :
    (Γₜ).Adj (torusSweptPhysicalBRouteVertex v i.castSucc)
      (torusSweptPhysicalBRouteVertex v i.succ) := by
  unfold torusSweptPhysicalBRouteVertex
  rw [torusSweptPatchCoordinate_adj_iff]
  fin_cases i <;> norm_num [sweptPhysicalBRouteCoordinate]

/-- The actual twelve successive steps of the endpoint route. -/
def torusSweptPhysicalBRoute (v : X) :
    (Γₜ).Walk (torusSweptPhysicalBRouteVertex v 0)
      (torusSweptPhysicalBRouteVertex v 12) :=
  .cons (route_adj v 0) (.cons (route_adj v 1) (.cons (route_adj v 2)
    (.cons (route_adj v 3) (.cons (route_adj v 4) (.cons (route_adj v 5)
      (.cons (route_adj v 6) (.cons (route_adj v 7) (.cons (route_adj v 8)
        (.cons (route_adj v 9) (.cons (route_adj v 10)
          (.cons (route_adj v 11) .nil)))))))))))

/-- The endpoint route has twelve actual steps. -/
theorem torusSweptPhysicalBRoute_length (v : X) :
    (torusSweptPhysicalBRoute v).length = 12 := rfl

/-- The route starts at the actual B1 plaquette base. -/
theorem torusSweptPhysicalBRoute_start (v : X) :
    torusSweptPhysicalBRouteVertex v 0 = torusSweptPatchEndpoint v 2 := by
  rw [torusSweptPatchEndpoint_eq]
  simp [torusSweptPhysicalBRouteVertex, sweptPhysicalBRouteCoordinate,
    torusSweptPatchCoordinate, translate_apply]
  constructor <;> ring

/-- The route finishes immediately left of the actual B2 plaquette base. -/
theorem torusSweptPhysicalBRoute_end (v : X) :
    torusSweptPhysicalBRouteVertex v 12 = (v.1, v.2 - 2) := by
  simp [torusSweptPhysicalBRouteVertex, sweptPhysicalBRouteCoordinate,
    torusSweptPatchCoordinate, translate_apply]

/-- Integer-coordinate physical vertices occupied by the route plaquettes and
by the four-endpoint witness. Their envelope has seven columns and six rows. -/
def sweptPhysicalRouteFootprintCoordinates : Finset (Fin 7 × Fin 6) :=
  (Finset.univ.image (fun p : SweptPatchCoordinate =>
    (p.1.1.castSucc, p.1.2.castSucc))) ∪
  (Finset.univ.image (fun p : Fin 13 × (Fin 2 × Fin 2) =>
    let q := sweptPhysicalBRouteCoordinate p.1
    ((⟨q.1.val + p.2.1.val, by omega⟩ : Fin 7),
      (⟨q.2.val + p.2.2.val, by omega⟩ : Fin 6))))

/-- The existing witness and the route's elementary movement footprints require
exactly thirty sites. This is an auxiliary source-braiding geometry. -/
theorem card_sweptPhysicalRouteFootprintCoordinates :
    sweptPhysicalRouteFootprintCoordinates.card = 30 := by decide +kernel

/-- Native physical coordinates in the seven-column, six-row envelope. -/
def torusSweptPhysicalRouteCoordinate (v : X) (p : Fin 7 × Fin 6) : X :=
  translate (v.1 - 1) (v.2 - 2) ((p.1.val : ZMod width), (p.2.val : ZMod height))

/-- Every physical coordinate in the route envelope is distinct on the torus,
including when the translated envelope crosses either periodic seam. -/
theorem torusSweptPhysicalRouteCoordinate_injective (v : X) :
    Function.Injective (torusSweptPhysicalRouteCoordinate v) := by
  intro p q h
  have hxy := (translate (v.1 - 1) (v.2 - 2)).injective h
  have hx := congrArg (fun z : X => z.1.val) hxy
  have hy := congrArg (fun z : X => z.2.val) hxy
  have hx' (p : Fin 7 × Fin 6) : p.1.val < width := by
    have := Fact.out (p := 7 < width); omega
  have hy' (p : Fin 7 × Fin 6) : p.2.val < height := by
    have := Fact.out (p := 6 < height); omega
  rw [ZMod.val_natCast_of_lt (hx' p), ZMod.val_natCast_of_lt (hx' q)] at hx
  rw [ZMod.val_natCast_of_lt (hy' p), ZMod.val_natCast_of_lt (hy' q)] at hy
  exact Prod.ext (Fin.ext hx) (Fin.ext hy)

/-- The actual thirty-site movement footprint. -/
def torusSweptPhysicalRouteFootprint (v : X) : Finset X :=
  sweptPhysicalRouteFootprintCoordinates.image (torusSweptPhysicalRouteCoordinate v)

/-- The actual native physical footprint consists of thirty distinct sites. -/
theorem torusSweptPhysicalRouteFootprint_card (v : X) :
    (torusSweptPhysicalRouteFootprint v).card = 30 := by
  rw [torusSweptPhysicalRouteFootprint, Finset.card_image_of_injective _
    (torusSweptPhysicalRouteCoordinate_injective v)]
  exact card_sweptPhysicalRouteFootprintCoordinates

/-- Every corner of every route plaquette belongs to the native movement
footprint; therefore each adjacent-plaquette elementary move is supported there. -/
theorem torusSweptPhysicalBRoute_corner_mem_footprint
    (v : X) (i : Fin 13) (ε : Fin 2 × Fin 2) :
    translate (v.1 - 1) (v.2 - 2)
      (((sweptPhysicalBRouteCoordinate i).1.val + ε.1.val : ℕ),
        ((sweptPhysicalBRouteCoordinate i).2.val + ε.2.val : ℕ)) ∈
      torusSweptPhysicalRouteFootprint v := by
  apply Finset.mem_image.mpr
  refine ⟨((⟨(sweptPhysicalBRouteCoordinate i).1.val + ε.1.val, by omega⟩ : Fin 7),
    (⟨(sweptPhysicalBRouteCoordinate i).2.val + ε.2.val, by omega⟩ : Fin 6)), ?_, rfl⟩
  exact Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ ((i, ε) : Fin 13 × (Fin 2 × Fin 2))))

/-- Every vertex of the actual endpoint route lies in the thirty-site footprint. -/
theorem torusSweptPhysicalBRoute_vertex_mem_footprint (v : X) (i : Fin 13) :
    torusSweptPhysicalBRouteVertex v i ∈ torusSweptPhysicalRouteFootprint v := by
  simpa [torusSweptPhysicalBRouteVertex, torusSweptPatchCoordinate] using
    torusSweptPhysicalBRoute_corner_mem_footprint v i (0, 0)

/-- The full actual twelve-step route is contained in the native footprint. -/
theorem torusSweptPhysicalBRoute_mem_footprint (v : X) :
    ∀ x ∈ (torusSweptPhysicalBRoute v).support,
      x ∈ torusSweptPhysicalRouteFootprint v := by
  intro x hx
  simp only [torusSweptPhysicalBRoute, SimpleGraph.Walk.support,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact torusSweptPhysicalBRoute_vertex_mem_footprint v _

/-- The final plaquette is adjacent to the unchanged B2 plaquette, as required
for a later joint-flux measurement. No measurement identity is asserted here. -/
theorem torusSweptPhysicalBRoute_end_adj_partner (v : X) :
    (Γₜ).Adj (torusSweptPhysicalBRouteVertex v 12) (torusSweptPatchEndpoint v 3) := by
  rw [torusSweptPhysicalBRoute_end, torusSweptPatchEndpoint_eq]
  change (Γₜ).Adj (v.1, v.2 - 2) (v.1 + 1, v.2 - 2)
  exact torusGraph_adj_right v.1 (v.2 - 2)

/-- None of the successive moving plaquette bases coincides with either A
endpoint or the unchanged B2 endpoint. Source: SCP10, lines 2340–2423. -/
theorem torusSweptPhysicalBRoute_avoids_partners (v : X) (i : Fin 13) :
    torusSweptPhysicalBRouteVertex v i ≠ torusSweptPatchEndpoint v 0 ∧
      torusSweptPhysicalBRouteVertex v i ≠ torusSweptPatchEndpoint v 1 ∧
      torusSweptPhysicalBRouteVertex v i ≠ torusSweptPatchEndpoint v 3 := by
  have hc : ∀ i : Fin 13, sweptPhysicalBRouteCoordinate i ≠ (0, 3) ∧
      sweptPhysicalBRouteCoordinate i ≠ (4, 3) ∧
      sweptPhysicalBRouteCoordinate i ≠ (2, 0) := by decide +kernel
  change torusSweptPatchCoordinate v (sweptPhysicalBRouteCoordinate i) ≠
      torusSweptPatchCoordinate v (0, 3) ∧
    torusSweptPatchCoordinate v (sweptPhysicalBRouteCoordinate i) ≠
      torusSweptPatchCoordinate v (4, 3) ∧
    torusSweptPatchCoordinate v (sweptPhysicalBRouteCoordinate i) ≠
      torusSweptPatchCoordinate v (2, 0)
  exact ⟨fun h => (hc i).1 ((torusSweptPatchCoordinate_injective v) h),
    fun h => (hc i).2.1 ((torusSweptPatchCoordinate_injective v) h),
    fun h => (hc i).2.2 ((torusSweptPatchCoordinate_injective v) h)⟩

end TNLean.PEPS
