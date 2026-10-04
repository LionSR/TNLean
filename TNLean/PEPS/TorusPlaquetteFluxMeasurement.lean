/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCycleFluxMeasurement
import TNLean.PEPS.EdgeMapSubgraph
import TNLean.PEPS.RegularPhysicalCutColumnAction
import TNLean.PEPS.RegularTorusEntropy
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Detecting a flux class on four original torus spins

The four-step boundary walk of a native plaquette has exactly four physical
sites. Its induced graph is connected, so the physical closed-walk measurement
applies without any supplied spanning tree or cycle coordinates. The resulting
complete positive projective measurement detects the conjugacy class of the
actual plaquette holonomy for every assignment of regular bond operators.

For a one-bond open string, the ordered bond receives the group element or its
inverse according to its incidence direction. Its four-step holonomy is proved
to be the prescribed element. One fixed measurement therefore detects its flux
conjugacy class for every outgoing boundary configuration and on the actual globally
contracted PEPS coefficient matrix. The additional physical outcome is the
orthogonal complement of the tensor's used range.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, fluxon strings and
Theorem 6.15, `thm:anyons:detect-fluxons`, local source lines 2181–2197 and
2217–2267.

**Scope restriction (regular native tori and explicit strings):** Both torus
periods are at least three. The string consumer concerns the explicitly
constructed one-bond strings on all four sides; the general detector measures
arbitrary inserted plaquette holonomies. The relation to deformation of open strings
and to parent-Hamiltonian states remains separate. These source restrictions
are recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The positively oriented four-step walk around a native torus plaquette.
Source: SCP10, flux detection, Theorem 6.15, lines 2217–2267. -/
def torusPlaquetteWalk (v : X) : (Γₜ).Walk v v :=
  .cons (torusGraph_adj_right v.1 v.2)
    (.cons (torusGraph_adj_up (v.1 + 1) v.2)
      (.cons (torusGraph_adj_right v.1 (v.2 + 1)).symm
        (.cons (torusGraph_adj_up v.1 v.2).symm .nil)))

variable {G : Type*} [Group G]

/-- Counterclockwise plaquette transport is the reverse-ordered product of its
four directed steps. Source: SCP10, Theorem 6.15, lines 2217–2267. -/
theorem regularWalkHolonomy_torusPlaquetteWalk (u : Edge Γₜ → G) (v : X) :
    regularWalkHolonomy u (torusPlaquetteWalk v) =
      (regularDirectedTransport u (torusGraph_adj_up v.1 v.2))⁻¹ *
        (regularDirectedTransport u (torusGraph_adj_right v.1 (v.2 + 1)))⁻¹ *
        regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) v.2) *
        regularDirectedTransport u (torusGraph_adj_right v.1 v.2) := by
  change (((1 * regularDirectedTransport u (torusGraph_adj_up v.1 v.2).symm) *
    regularDirectedTransport u (torusGraph_adj_right v.1 (v.2 + 1)).symm) *
    regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) v.2)) *
    regularDirectedTransport u (torusGraph_adj_right v.1 v.2) = _
  rw [regularDirectedTransport_symm u (torusGraph_adj_up v.1 v.2),
    regularDirectedTransport_symm u (torusGraph_adj_right v.1 (v.2 + 1)), one_mul]

/-- Clockwise plaquette transport is the inverse of the counterclockwise
transport. Source: SCP10, fluxon-braiding figure, lines 2361–2395. -/
theorem regularWalkHolonomy_torusPlaquetteWalk_reverse (u : Edge Γₜ → G) (v : X) :
    regularWalkHolonomy u (torusPlaquetteWalk v).reverse =
      (regularDirectedTransport u (torusGraph_adj_right v.1 v.2))⁻¹ *
        (regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) v.2))⁻¹ *
        regularDirectedTransport u (torusGraph_adj_right v.1 (v.2 + 1)) *
        regularDirectedTransport u (torusGraph_adj_up v.1 v.2) := by
  rw [regularWalkHolonomy_reverse, regularWalkHolonomy_torusPlaquetteWalk]
  group


/-- The four physical sites surrounding a native torus plaquette. Source:
SCP10, the detection tweezer in Theorem 6.15, lines 2225–2258. -/
def torusPlaquetteRegion (v : X) : Finset X :=
  (torusPlaquetteWalk v).support.toFinset

/-- A native plaquette has exactly four physical sites. Source: SCP10,
Theorem 6.15, lines 2225–2258. -/
theorem torusPlaquetteRegion_card (v : X) : (torusPlaquetteRegion v).card = 4 := by
  rcases v with ⟨x, y⟩
  have hx : x + 1 ≠ x := by simp
  have hy : y + 1 ≠ y := by simp
  simp [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
    hx, hy, Ne.symm hx, Ne.symm hy]

private theorem plaquette_connected (v : X) :
    ((Γₜ).induce (torusPlaquetteRegion v : Set X)).Connected := by
  have hR : (torusPlaquetteRegion v : Set X) =
      {x | x ∈ (torusPlaquetteWalk v).support} := by
    ext x
    simp [torusPlaquetteRegion]
  rw [hR]
  exact (torusPlaquetteWalk v).connected_induce_support

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- A one-bond flux string with directed transport `g` along the lower side
of a native plaquette. The ordered edge receives `g` or `g⁻¹` according to its
orientation; every other edge receives the identity. Source: SCP10,
fluxon strings, lines 2181–2197, and Theorem 6.15, lines 2217–2267. -/
def torusPlaquetteFluxInsertion (v : X) (g : G) (e : Edge (Γₜ)) : G :=
  if e = Edge.ofAdj (torusGraph_adj_right v.1 v.2) then
    if v < (v.1 + 1, v.2) then g else g⁻¹
  else 1

omit [Fintype G] [DecidableEq G] in
/-- The actual four-step plaquette holonomy of the one-bond flux insertion is
its prescribed group element. Source: SCP10, the single endpoint configuration
in Theorem 6.15, lines 2220–2245. -/
theorem regularWalkHolonomy_torusPlaquetteFluxInsertion (v : X) (g : G) :
    regularWalkHolonomy (torusPlaquetteFluxInsertion v g) (torusPlaquetteWalk v) = g := by
  classical
  have hy : v.2 + 1 ≠ v.2 := by simp
  let h₀ := torusGraph_adj_right v.1 v.2
  let h₁ := torusGraph_adj_up (v.1 + 1) v.2
  let h₂ := (torusGraph_adj_right v.1 (v.2 + 1)).symm
  let h₃ := (torusGraph_adj_up v.1 v.2).symm
  have hne₁ : Edge.ofAdj h₁ ≠ Edge.ofAdj h₀ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₁ h₀ Prod.snd rfl (Or.inr hy)
  have hne₂ : Edge.ofAdj h₂ ≠ Edge.ofAdj h₀ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₂ h₀ Prod.snd rfl (Or.inl hy)
  have hne₃ : Edge.ofAdj h₃ ≠ Edge.ofAdj h₀ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₃ h₀ Prod.snd rfl (Or.inl hy)
  have hfirst : regularDirectedTransport (torusPlaquetteFluxInsertion v g) h₀ = g := by
    unfold regularDirectedTransport torusPlaquetteFluxInsertion
    split_ifs <;> simp_all
  have hrest {x y : X} (h : (Γₜ).Adj x y) (hne : Edge.ofAdj h ≠ Edge.ofAdj h₀) :
      regularDirectedTransport (torusPlaquetteFluxInsertion v g) h = 1 := by
    simp [regularDirectedTransport, torusPlaquetteFluxInsertion, hne]
  rw [regularWalkHolonomy_torusPlaquetteWalk]
  have hs₁ := hrest h₁ hne₁
  have hs₂ := hrest h₂ hne₂
  have hs₃ := hrest h₃ hne₃
  rw [regularDirectedTransport_symm _ (torusGraph_adj_right v.1 (v.2 + 1))] at hs₂
  rw [regularDirectedTransport_symm _ (torusGraph_adj_up v.1 v.2)] at hs₃
  simp_all

/-- A complete measurement on the four original physical sites surrounding
any native torus plaquette detects its nonabelian holonomy class. All spanning
trees and cycle coordinates are derived internally. Source: SCP10,
Theorem 6.15, flux detection, lines 2217–2267. -/
theorem IsGIsometric.exists_torusPlaquette_physicalMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (u : Edge (Γₜ) → G)
        (θ : {f : Edge (Γₜ) // IsRegionBoundaryEdge (torusPlaquetteRegion v) f} → G)
        (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight
            (groupBondTensor (regularTwistedSite (torusIncidentSite a) u))
            (torusPlaquetteRegion v) (fun f => Fintype.equivFin G (θ f)) =
          if C = some (ConjClasses.mk (regularWalkHolonomy u (torusPlaquetteWalk v)))
          then openRegionWeight
            (groupBondTensor (regularTwistedSite (torusIncidentSite a) u))
            (torusPlaquetteRegion v) (fun f => Fintype.equivFin G (θ f)) else 0 := by
  classical
  let R := torusPlaquetteRegion v
  have hsupport : ∀ x ∈ (torusPlaquetteWalk v).support, x ∈ (R : Set X) := by
    intro x hx
    exact List.mem_toFinset.mpr hx
  let o : {x : X // x ∈ R} := ⟨v, hsupport _ (torusPlaquetteWalk v).start_mem_support⟩
  let p : ((Γₜ).induce (R : Set X)).Walk o o :=
    (torusPlaquetteWalk v).induce (R : Set X) hsupport
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ :=
    exists_regularClosedWalkClass_physicalMeasurement (torusIncidentSite a)
      (fun w => ha.isGIsometric_torusIncidentSite w) R (plaquette_connected v) o p
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro u θ C
  have hp : regularWalkHolonomy (regularRegionInternalOperators R u) p =
      regularWalkHolonomy u (torusPlaquetteWalk v) := by
    rw [regularWalkHolonomy_inducedWalk, SimpleGraph.Walk.map_induce]
    rfl
  simpa only [hp] using hQact u θ C

/-- One fixed complete projective measurement detects the flux class `C[g]`
of every one-bond open regular string ending at a native torus plaquette,
independently of the outgoing labels. The bond assignment and its holonomy
are constructed and proved, rather than supplied as measurement assumptions.
Source: SCP10, Theorem 6.15, lines 2217–2267. -/
theorem IsGIsometric.exists_torusPlaquette_fluxClass_measurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (g : G)
        (θ : {f : Edge (Γₜ) // IsRegionBoundaryEdge (torusPlaquetteRegion v) f} → G)
        (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight
            (groupBondTensor (regularTwistedSite (torusIncidentSite a)
              (torusPlaquetteFluxInsertion v g)))
            (torusPlaquetteRegion v) (fun f => Fintype.equivFin G (θ f)) =
          if C = some (ConjClasses.mk g)
          then openRegionWeight
            (groupBondTensor (regularTwistedSite (torusIncidentSite a)
              (torusPlaquetteFluxInsertion v g)))
            (torusPlaquetteRegion v) (fun f => Fintype.equivFin G (θ f)) else 0 := by
  classical
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := ha.exists_torusPlaquette_physicalMeasurement v
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro g θ C
  simpa only [regularWalkHolonomy_torusPlaquetteFluxInsertion] using
    hQact (torusPlaquetteFluxInsertion v g) θ C

/-- The same four-site measurement detects the plaquette holonomy class for
every actual bond assignment in the globally contracted torus PEPS. Its action is left
multiplication of the native physical cut matrix, hence is supported exactly
on the plaquette's four physical spins. Source: SCP10, Theorem 6.15,
lines 2217–2267; no parent-Hamiltonian identification is used. -/
theorem IsGIsometric.exists_torusPlaquette_holonomy_cutMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (u : Edge (Γₜ) → G) (C : Option (ConjClasses G)),
        Q C * regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite a) u)
            (torusPlaquetteRegion v) =
          if C = some (ConjClasses.mk (regularWalkHolonomy u (torusPlaquetteWalk v)))
          then regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite a) u)
            (torusPlaquetteRegion v) else 0 := by
  classical
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := ha.exists_torusPlaquette_physicalMeasurement v
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro u C
  apply mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
  exact fun θ => hQact u θ C

/-- The same four-site measurement detects the class of an explicit one-bond
flux string in the actual globally contracted torus PEPS. Its action is left
multiplication of the native physical cut matrix, hence is supported exactly
on the plaquette's four physical spins. Source: SCP10, Theorem 6.15,
lines 2217–2267; no parent-Hamiltonian identification is used. -/
theorem IsGIsometric.exists_torusPlaquette_fluxClass_cutMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (g : G) (C : Option (ConjClasses G)),
        Q C * regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite a) (torusPlaquetteFluxInsertion v g))
            (torusPlaquetteRegion v) =
          if C = some (ConjClasses.mk g)
          then regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite a) (torusPlaquetteFluxInsertion v g))
            (torusPlaquetteRegion v) else 0 := by
  classical
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := ha.exists_torusPlaquette_holonomy_cutMeasurement v
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro g C
  simpa only [regularWalkHolonomy_torusPlaquetteFluxInsertion] using
    hQact (torusPlaquetteFluxInsertion v g) C

/-- The four oriented sides of the actual plaquette walk, in traversal order.
Source: SCP10, Theorem 6.15, lines 2262–2267: a string may attach to any side. -/
def torusPlaquetteSide (v : X) (i : Fin 4) :
    {q : X × X // (Γₜ).Adj q.1 q.2} :=
  ![⟨(v, (v.1 + 1, v.2)), torusGraph_adj_right v.1 v.2⟩,
    ⟨((v.1 + 1, v.2), (v.1 + 1, v.2 + 1)), torusGraph_adj_up (v.1 + 1) v.2⟩,
    ⟨((v.1 + 1, v.2 + 1), (v.1, v.2 + 1)),
      (torusGraph_adj_right v.1 (v.2 + 1)).symm⟩,
    ⟨((v.1, v.2 + 1), v), (torusGraph_adj_up v.1 v.2).symm⟩] i

private theorem plaquette_side_edge_injective (v : X) :
    Function.Injective (fun i : Fin 4 => Edge.ofAdj (torusPlaquetteSide v i).2) := by
  have hx : v.1 + 1 ≠ v.1 := by simp
  have hy : v.2 + 1 ≠ v.2 := by simp
  let h₀ := torusGraph_adj_right v.1 v.2
  let h₁ := torusGraph_adj_up (v.1 + 1) v.2
  let h₂ := (torusGraph_adj_right v.1 (v.2 + 1)).symm
  let h₃ := (torusGraph_adj_up v.1 v.2).symm
  have h₁₀ : Edge.ofAdj h₁ ≠ Edge.ofAdj h₀ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₁ h₀ Prod.snd rfl (Or.inr hy)
  have h₂₀ : Edge.ofAdj h₂ ≠ Edge.ofAdj h₀ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₂ h₀ Prod.snd rfl (Or.inl hy)
  have h₃₀ : Edge.ofAdj h₃ ≠ Edge.ofAdj h₀ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₃ h₀ Prod.snd rfl (Or.inl hy)
  have h₂₁ : Edge.ofAdj h₂ ≠ Edge.ofAdj h₁ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₂ h₁ Prod.fst rfl (Or.inr (Ne.symm hx))
  have h₃₁ : Edge.ofAdj h₃ ≠ Edge.ofAdj h₁ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₃ h₁ Prod.fst rfl (Or.inl (Ne.symm hx))
  have h₃₂ : Edge.ofAdj h₃ ≠ Edge.ofAdj h₂ :=
    Edge.ofAdj_ne_of_endpoint_coordinates h₃ h₂ Prod.snd rfl (Or.inr (Ne.symm hy))
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [torusPlaquetteSide]

/-- Directed insertion of a one-bond regular string on any of the four sides.
The ordered edge carries `g` or its inverse according to the traversal direction.
Source: SCP10, Theorem 6.15, lines 2262–2267. -/
def torusPlaquetteSideInsertion (v : X) (i : Fin 4) (g : G) (e : Edge (Γₜ)) : G :=
  if e = Edge.ofAdj (torusPlaquetteSide v i).2 then
    if (torusPlaquetteSide v i).1.1 < (torusPlaquetteSide v i).1.2 then g else g⁻¹
  else 1

omit [Fintype G] [DecidableEq G] in
/-- A string attached to any oriented plaquette side has the prescribed
plaquette holonomy. The orientation is derived from the actual ordered edge.
Source: SCP10, Theorem 6.15, lines 2262–2267. -/
theorem regularWalkHolonomy_torusPlaquetteSideInsertion (v : X) (i : Fin 4) (g : G) :
    regularWalkHolonomy (torusPlaquetteSideInsertion v i g) (torusPlaquetteWalk v) = g := by
  classical
  have hside : regularDirectedTransport (torusPlaquetteSideInsertion v i g)
      (torusPlaquetteSide v i).2 = g := by
    unfold regularDirectedTransport torusPlaquetteSideInsertion
    split_ifs <;> simp_all
  have hother (j : Fin 4) (hji : j ≠ i) :
      regularDirectedTransport (torusPlaquetteSideInsertion v i g)
        (torusPlaquetteSide v j).2 = 1 := by
    have he : Edge.ofAdj (torusPlaquetteSide v j).2 ≠
        Edge.ofAdj (torusPlaquetteSide v i).2 :=
      fun h => hji (plaquette_side_edge_injective v h)
    simp [regularDirectedTransport, torusPlaquetteSideInsertion, he]
  change (((1 * regularDirectedTransport (torusPlaquetteSideInsertion v i g)
      (torusPlaquetteSide v 3).2) * regularDirectedTransport
      (torusPlaquetteSideInsertion v i g) (torusPlaquetteSide v 2).2) *
      regularDirectedTransport (torusPlaquetteSideInsertion v i g)
      (torusPlaquetteSide v 1).2) * regularDirectedTransport
      (torusPlaquetteSideInsertion v i g) (torusPlaquetteSide v 0).2 = g
  fin_cases i <;> simp (disch := decide) only [hother, hside, mul_one, one_mul]

/-- One fixed four-spin projective measurement detects a flux string attached
on any of the four plaquette sides in the actual globally contracted state.
No outgoing label or chosen side is supplied to the measurement construction.
Source: SCP10, Theorem 6.15, lines 2262–2267. -/
theorem IsGIsometric.exists_torusPlaquette_allSides_cutMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (i : Fin 4) (g : G) (C : Option (ConjClasses G)),
        Q C * regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite a) (torusPlaquetteSideInsertion v i g))
            (torusPlaquetteRegion v) =
          if C = some (ConjClasses.mk g)
          then regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite a) (torusPlaquetteSideInsertion v i g))
            (torusPlaquetteRegion v) else 0 := by
  classical
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := ha.exists_torusPlaquette_holonomy_cutMeasurement v
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro i g C
  simpa only [regularWalkHolonomy_torusPlaquetteSideInsertion] using
    hQact (torusPlaquetteSideInsertion v i g) C

/-- Actual inserted torus states with different measured plaquette classes
have orthogonal physical coefficient columns. No normalization or
parent-Hamiltonian hypothesis is required. Source: SCP10, Theorem 6.15,
lines 2217–2267, physical distinguishability of flux conjugacy classes. -/
theorem IsGIsometric.torusPlaquette_cutMatrix_orthogonal_of_class_ne
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X)
    (u w : Edge (Γₜ) → G)
    (hne : ConjClasses.mk (regularWalkHolonomy u (torusPlaquetteWalk v)) ≠
      ConjClasses.mk (regularWalkHolonomy w (torusPlaquetteWalk v))) :
    (regularPhysicalCutMatrix (regularTwistedSite (torusIncidentSite a) u)
      (torusPlaquetteRegion v)).conjTranspose *
      regularPhysicalCutMatrix (regularTwistedSite (torusIncidentSite a) w)
        (torusPlaquetteRegion v) = 0 := by
  classical
  obtain ⟨Q, hQh, _, _, hQact⟩ := ha.exists_torusPlaquette_holonomy_cutMeasurement v
  let C := some (ConjClasses.mk (regularWalkHolonomy u (torusPlaquetteWalk v)))
  let M := regularPhysicalCutMatrix (regularTwistedSite (torusIncidentSite a) u)
    (torusPlaquetteRegion v)
  let N := regularPhysicalCutMatrix (regularTwistedSite (torusIncidentSite a) w)
    (torusPlaquetteRegion v)
  have hM : Q C * M = M := by simpa only [C, ↓reduceIte] using hQact u C
  have hN : Q C * N = 0 := by
    simpa only [C, Option.some.injEq, hne, ↓reduceIte] using hQact w C
  change M.conjTranspose * N = 0
  calc
    M.conjTranspose * N = (Q C * M).conjTranspose * N := by rw [hM]
    _ = M.conjTranspose * (Q C * N) := by
      rw [Matrix.conjTranspose_mul, (hQh C).1.eq, Matrix.mul_assoc]
    _ = 0 := by rw [hN, Matrix.mul_zero]

end TNLean.PEPS
