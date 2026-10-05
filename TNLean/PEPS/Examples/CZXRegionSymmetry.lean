/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXOpenRegion
import TNLean.PEPS.EdgeScalarSolve

/-!
# Physical symmetry of an actual CZX region

The local controlled-phase factors cancel on internal bonds. Only crossing-bond
factors remain in the physical symmetry of the genuine open-region contraction.
The bottom and left pair reversal is the native orientation of the CZX tensor.

**Scope restriction (simple torus graph):** both periods are at least three;
see `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

**Local fix (bond orientation):** bottom and left pairs are reversed as in
`docs/paper-gaps/rmp_peps_czx_bond_orientation.tex`.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), boundary symmetry, lines 330–345.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

private theorem czxLegPhase_mul_self (x : Fin 4) : czxLegPhase x * czxLegPhase x = 1 := by
  rw [czxLegPhase, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Reversing a virtual bond pair does not change its controlled phase. -/
theorem czxLegPhase_swap (x : Fin 4) :
    czxLegPhase (czxBondSwap x) = czxLegPhase x := by
  obtain ⟨⟨a,b⟩, rfl⟩ := czxBond.surjective x
  simp [mul_comm]

/-- Simultaneous bit flips commute with reversal of a virtual bond pair. -/
theorem czxLegFlip_swap (x : Fin 4) :
    czxLegFlip (czxBondSwap x) = czxBondSwap (czxLegFlip x) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := czxBond.surjective x
  simp

private theorem czx_phase_prod_endpoints (R : Finset (TorusVertex width height))
    (e : Edge (torusGraph width height)) (x : Fin 4) :
    (∏ v : incVertex e, if v.1 ∈ R then czxLegPhase x else 1) =
      if IsRegionBoundaryEdge R e then czxLegPhase x else 1 := by
  classical
  let v₁ : incVertex e := ⟨e.1.1, Or.inl rfl⟩
  let v₂ : incVertex e := ⟨e.1.2, Or.inr rfl⟩
  have hv : v₁ ≠ v₂ := fun h => (ne_of_lt e.2.1) (congrArg Subtype.val h)
  have hu : (Finset.univ : Finset (incVertex e)) = {v₁,v₂} := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases v.2 with h | h
    · exact Or.inl (Subtype.ext h.symm)
    · exact Or.inr (Subtype.ext h.symm)
  rw [hu, Finset.prod_pair hv]
  by_cases h₁ : e.1.1 ∈ R <;> by_cases h₂ : e.1.2 ∈ R <;>
    simp [v₁, v₂, IsRegionBoundaryEdge, h₁, h₂, czxLegPhase_mul_self]

private theorem czx_phase_prod_incidence (R : Finset (TorusVertex width height))
    (η : Edge (torusGraph width height) → Fin 4) :
    (∏ v : TorusVertex width height, ∏ e : IncidentEdge (torusGraph width height) v,
      if v ∈ R then czxLegPhase (η e.1) else 1) =
      ∏ e : Edge (torusGraph width height),
        if IsRegionBoundaryEdge R e then czxLegPhase (η e) else 1 := by
  classical
  rw [← Fintype.prod_sigma (fun p : (Σ v, IncidentEdge (torusGraph width height) v) =>
    if p.1 ∈ R then czxLegPhase (η p.2.1) else 1),
    ← Equiv.prod_comp (sigmaSwap (G := torusGraph width height)).symm, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro e _
  exact czx_phase_prod_endpoints R e (η e)

private theorem czx_phase_prod_legs (v : TorusVertex width height)
    (η : IncidentEdge (torusGraph width height) v → Fin 4) :
    czxLegPhase (η (torusTopLeg v)) * czxLegPhase (η (torusRightLeg v)) *
      czxLegPhase (η (torusDownLeg v)) * czxLegPhase (η (torusLeftLeg v)) =
        ∏ e, czxLegPhase (η e) := by
  have h := Fintype.prod_equiv (torusIncidentLegEquiv v)
    (fun i => czxLegPhase (η (torusIncidentLeg v i)))
    (fun e => czxLegPhase (η e)) (fun _ => rfl)
  simpa [Fin.prod_univ_four, torusIncidentLeg, mul_assoc] using h

private theorem czx_region_phase_prod (R : Finset (TorusVertex width height))
    (η : RegionIncidentConfig (czxPEPS width height) R) :
    (∏ w : {w // w ∈ R}, ∏ e : IncidentEdge (torusGraph width height) w.1,
      czxLegPhase (η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩)) =
      ∏ e : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e},
        czxLegPhase (η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) := by
  classical
  change ({e : Edge (torusGraph width height) // IsRegionIncidentEdge R e} → Fin 4) at η
  let ζ : Edge (torusGraph width height) → Fin 4 :=
    fun e => if he : IsRegionIncidentEdge R e then η ⟨e,he⟩ else 0
  have hz (w : {w // w ∈ R}) (e : IncidentEdge (torusGraph width height) w.1) :
      ζ e.1 = η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩ := by
    dsimp [ζ]
    rw [dite_eq_left (isRegionIncidentEdge_of_regionVertex R w e)]
  calc
    _ = ∏ w : {w // w ∈ R}, ∏ e : IncidentEdge (torusGraph width height) w.1,
          czxLegPhase (ζ e.1) := by simp only [hz]
    _ = ∏ v : TorusVertex width height, ∏ e : IncidentEdge (torusGraph width height) v,
          if v ∈ R then czxLegPhase (ζ e.1) else 1 := by
      simp only [Finset.prod_ite_irrel, Finset.prod_const_one, Finset.prod_ite_mem_eq]
      exact Finset.prod_coe_sort R (fun v =>
        ∏ e : IncidentEdge (torusGraph width height) v, czxLegPhase (ζ e.1))
    _ = ∏ e : Edge (torusGraph width height),
          if IsRegionBoundaryEdge R e then czxLegPhase (ζ e) else 1 :=
      czx_phase_prod_incidence R ζ
    _ = ∏ e : {e : Edge (torusGraph width height) // IsRegionBoundaryEdge R e},
          czxLegPhase (ζ e.1) := by
      rw [← Finset.prod_filter]
      exact Finset.prod_subtype _ (by simp) _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e _
      simp [ζ, isRegionBoundaryEdge_touches R e.2]

/-- Flip both qubits on every actual crossing bond of the region. -/
def czxRegionBoundaryFlip (R : Finset (TorusVertex width height)) :
    Equiv.Perm (RegionBoundaryConfig (czxPEPS width height) R) :=
  Equiv.piCongrRight fun _ => czxLegFlip

/-- Controlled-phase factors on the actual crossing bonds. Internal bonds do not
appear because their two equal factors multiply to one. -/
noncomputable def czxRegionBoundaryPhase (R : Finset (TorusVertex width height))
    (μ : RegionBoundaryConfig (czxPEPS width height) R) : ℂ :=
  ∏ e, czxLegPhase (μ e)

private theorem czx_component_pullthrough (v : TorusVertex width height)
    (η : IncidentEdge (torusGraph width height) v → Fin 4) (s' : Fin 16) :
    (∑ s, czxOnSite s' s * (czxPEPS width height).component v η s) =
      (∏ e, czxLegPhase (η e)) *
        (czxPEPS width height).component v (fun e => czxLegFlip (η e)) s' := by
  change (∑ s, czxOnSite s' s * czxSiteTensor _ _ _ _ s) = _
  rw [czxOnSite_mul_czxSiteTensor]
  simp only [czxLegPhase_swap, czxLegFlip_swap, czxPEPS, torusSiteTensor]
  rw [czx_phase_prod_legs]

/-- Physical on-site symmetry of the genuine CZX open-region map. The boundary
operator is the product of the actual crossing-bond flips and phases.
Source: CLW11, cancellation of internal controlled phases, lines 330–345. -/
theorem regionPhysicalMap_czxOnSite_openRegionWeight
    (R : Finset (TorusVertex width height))
    (μ : RegionBoundaryConfig (czxPEPS width height) R) :
    regionPhysicalMap R (fun _ => czxOnSite)
        (openRegionWeight (czxPEPS width height) R μ) =
      czxRegionBoundaryPhase R μ •
        openRegionWeight (czxPEPS width height) R (czxRegionBoundaryFlip R μ) := by
  classical
  let e : Equiv.Perm (RegionIncidentConfig (czxPEPS width height) R) :=
    Equiv.piCongrRight fun _ => czxLegFlip
  have hb (η : RegionIncidentConfig (czxPEPS width height) R) :
      regionIncidentBoundaryLabel (czxPEPS width height) R (e η) =
          czxRegionBoundaryFlip R μ ↔
        regionIncidentBoundaryLabel (czxPEPS width height) R η = μ := by
    constructor
    · intro h
      funext f
      exact czxLegFlip.injective (congrFun h f)
    · intro h
      exact congrArg (czxRegionBoundaryFlip R) h
  funext σ
  rw [regionPhysicalMap_openRegionWeight]
  change _ = czxRegionBoundaryPhase R μ * _
  have hs : (∑ η : RegionIncidentConfig (czxPEPS width height) R,
      if regionIncidentBoundaryLabel (czxPEPS width height) R η = μ then
        regionIncidentWeight (czxPEPS width height) R (e η) σ else 0) =
      openRegionWeight (czxPEPS width height) R (czxRegionBoundaryFlip R μ) σ := by
    unfold openRegionWeight
    exact Fintype.sum_equiv e _ _ (fun η => by simp only [hb])
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  by_cases hη : regionIncidentBoundaryLabel (czxPEPS width height) R η = μ
  · simp only [hη, ite_true]
    calc
      _ = (∏ w : {w // w ∈ R}, ∏ f : IncidentEdge (torusGraph width height) w.1,
            czxLegPhase (η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)) *
          regionIncidentWeight (czxPEPS width height) R (e η) σ := by
        rw [regionIncidentWeight, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro w _
        exact czx_component_pullthrough w.1 _ (σ w)
      _ = _ := by
        rw [czx_region_phase_prod]
        congr 1
        exact congrArg (fun ν => ∏ f, czxLegPhase (ν f)) hη
  · simp [hη]

/-- Matrix intertwining for the actual CZX region contraction and its crossing-bond
symmetry. This is the physical region map, rather than an abstract boundary chain. -/
theorem regionPhysicalProductMatrix_czxOnSite_intertwines
    (R : Finset (TorusVertex width height)) :
    regionPhysicalProductMatrix R (fun _ => czxOnSite) *
        openRegionCoefficientMatrix (czxPEPS width height) R =
      openRegionCoefficientMatrix (czxPEPS width height) R *
        Matrix.monomial (czxRegionBoundaryFlip R) (czxRegionBoundaryPhase R) := by
  classical
  ext σ μ
  have h := congrFun (regionPhysicalMap_czxOnSite_openRegionWeight R μ) σ
  simpa [regionPhysicalMap_apply, regionPhysicalProductMatrix, Matrix.mul_apply,
    openRegionCoefficientMatrix, Matrix.monomial_apply, mul_ite, mul_comm] using h

end TNLean.PEPS
