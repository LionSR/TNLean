import TNLean.PEPS.RegionBlock.PartitionBonds
import TNLean.PEPS.OpenRegionContraction

/-! # Coarse vertex tensors from a partition and uniform physical coordinates -/

open ManyBody (Edge)
namespace TNLean.PEPS.PartitionBonds

variable {V B : Type*} [Fintype V] [LinearOrder V] [LinearOrder B]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (block : V → B) {d D : ℕ}

/-- The fine sites assigned to a coarse vertex. -/
def sites (b : B) := Finset.univ.filter (fun v => block v = b)

omit [DecidableRel G.Adj] in
private theorem touches (e : Crossing (G := G) block) (b : B) :
    ((project block e).1.1 = b ∨ (project block e).1.2 = b) ↔
      IsRegionBoundaryEdge (sites block b) e.1 := by
  have ends := Edge.ofAdj_endpoints (SimpleGraph.map_adj_apply' e.1.2.2 e.2)
  change ((Edge.ofAdj _).1.1 = b ∨ (Edge.ofAdj _).1.2 = b) ↔ _
  rcases ends with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp only [h, h', IsRegionBoundaryEdge, sites, Finset.mem_filter, Finset.mem_univ, true_and]
    <;> have := e.2 <;> grind

private def crossOfBoundary (b : B) (e : {e : Edge G // IsRegionBoundaryEdge (sites block b) e}) :
    Crossing (G := G) block :=
  ⟨e.1, by
    have h := e.2
    simp only [IsRegionBoundaryEdge, sites, Finset.mem_filter, Finset.mem_univ, true_and] at h
    grind⟩

/-- Read a bundled leg at the unique incident coarse edge containing the fine bond. -/
def boundaryLabels (A : Tensor G d) (b : B) :
    ((q : IncidentEdge (G.map block) b) → (e : Fiber block q.1) → Fin (A.bondDim e.1.1)) ≃
      RegionBoundaryConfig A (sites block b) where
  toFun y e :=
    let c := crossOfBoundary block b e
    y ⟨project block c, (touches block c b).2 e.2⟩ ⟨c, rfl⟩
  invFun x q e := x ⟨e.1.1, (touches block e.1 b).1 (e.2.symm ▸ q.2)⟩
  right_inv _ := rfl
  left_inv y := by
    funext q e
    obtain ⟨q, hq⟩ := q
    rcases e with ⟨e, he⟩
    change project block e = q at he
    subst q
    rfl

variable (A : Tensor G d)
abbrev Bundle (q : Edge (G.map block)) := (e : Fiber block q) → Fin (A.bondDim e.1.1)

noncomputable def bundleDim (q : Edge (G.map block)) := Nat.card (Bundle block A q)

noncomputable def decode (q : Edge (G.map block)) : Fin (bundleDim block A q) ≃ Bundle block A q :=
  (Finite.equivFin _).symm

variable [DecidableRel (G.map block).Adj]

noncomputable def legs (b : B) :
    ((q : IncidentEdge (G.map block) b) → Fin (bundleDim block A q.1)) ≃
      RegionBoundaryConfig A (sites block b) :=
  (Equiv.piCongrRight fun q : IncidentEdge (G.map block) b => decode block A q.1).trans
    (boundaryLabels block A b)

/-- The caller supplies a uniform physical basis for all blocks. -/
noncomputable def coarseTensor (phys : ∀ b, Fin D ≃ RegionPhysicalConfig (d := d) (sites block b)) :
    Tensor (G.map block) D where
  bondDim := bundleDim block A
  component b y s := openRegionWeight A (sites block b) (legs block A b y) (phys b s)

/-- Injective physical maps on the individual fine regions give vertex injectivity of
the quotient tensor. -/
theorem coarseTensor_vertexInjective
    (phys : ∀ b, Fin D ≃ RegionPhysicalConfig (d := d) (sites block b))
    (h : ∀ b, Function.Injective (openRegionMap A (sites block b))) :
    IsVertexInjective (coarseTensor block A phys) := by
  classical
  intro b
  let R := sites block b
  have base := (Pi.linearIndependent_single_one (RegionBoundaryConfig A R) ℂ).map'
    (openRegionMap A R) (LinearMap.ker_eq_bot.mpr (h b))
  have cols : LinearIndependent ℂ (openRegionWeight A R) := by
    simpa only [Function.comp_def, openRegionMap_single] using base
  exact ((cols.comp _ (legs block A b).injective).map'
    (LinearEquiv.funCongrLeft ℂ ℂ (phys b)).toLinearMap
    (LinearEquiv.funCongrLeft ℂ ℂ (phys b)).ker)

end TNLean.PEPS.PartitionBonds
