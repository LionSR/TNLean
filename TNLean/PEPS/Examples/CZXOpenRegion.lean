/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.CZXOnSiteSymmetry
import TNLean.PEPS.TorusIncidentCoordinates
import TNLean.PEPS.RegionPhysicalMap

/-!
# Actual open-region coefficients of the CZX tensor

A physical qubit configuration fixes every virtual bond touching the region.
Consequently each actual open-region coefficient is zero or one, and different
virtual boundary configurations have disjoint physical supports. There is no
multiplicity from bonds outside the region in this statement.

**Local fix (CZX bond orientation):** the native tensor reverses bottom and left
pairs, as documented in `docs/paper-gaps/rmp_peps_czx_bond_orientation.tex`.

**Scope restriction (simple torus graph):** both periods are at least three;
see `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## References

- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752), region boundary, lines 330–345.
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127), Appendix A, CZX tensor.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

private theorem czx_component_eq_one_of_ne_zero (v : TorusVertex width height)
    (η : IncidentEdge (torusGraph width height) v → Fin 4) (s : Fin 16)
    (h : (czxPEPS width height).component v η s ≠ 0) :
    (czxPEPS width height).component v η s = 1 := by
  dsimp [czxPEPS, torusSiteTensor, czxSiteTensor] at *
  split_ifs at * <;> simp_all

private theorem czx_component_labels_unique (v : TorusVertex width height)
    (η θ : IncidentEdge (torusGraph width height) v → Fin 4) (s : Fin 16)
    (hη : (czxPEPS width height).component v η s ≠ 0)
    (hθ : (czxPEPS width height).component v θ s ≠ 0) : η = θ := by
  unfold czxPEPS torusSiteTensor czxSiteTensor at hη hθ
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hη hθ
  apply torusIncidentCoordinates_injective v
  exact Prod.ext (hη.1.trans hθ.1.symm) (Prod.ext (hη.2.1.trans hθ.2.1.symm)
    (Prod.ext (czxBondSwap.injective (hη.2.2.1.trans hθ.2.2.1.symm))
      (czxBondSwap.injective (hη.2.2.2.trans hθ.2.2.2.symm))))

/-- A physical configuration determines at most one nonzero incident-bond assignment.
Source: the four virtual pairs of the printed CZX tensor, review Appendix A. -/
theorem czx_regionIncidentConfig_unique (R : Finset (TorusVertex width height))
    (σ : RegionPhysicalConfig (d := 16) R)
    (η θ : RegionIncidentConfig (czxPEPS width height) R)
    (hη : regionIncidentWeight (czxPEPS width height) R η σ ≠ 0)
    (hθ : regionIncidentWeight (czxPEPS width height) R θ σ ≠ 0) : η = θ := by
  classical
  have hlocal (w : {w // w ∈ R}) := czx_component_labels_unique w.1
    (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩)
    (fun e => θ ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) (σ w)
    ((Finset.prod_ne_zero_iff.mp hη) w (Finset.mem_univ _))
    ((Finset.prod_ne_zero_iff.mp hθ) w (Finset.mem_univ _))
  funext e
  rcases e.2 with he | he
  · exact congrFun (hlocal ⟨e.1.1.1, he⟩) ⟨e.1, Or.inl rfl⟩
  · exact congrFun (hlocal ⟨e.1.1.2, he⟩) ⟨e.1, Or.inr rfl⟩

private theorem czx_regionIncidentWeight_eq_one (R : Finset (TorusVertex width height))
    (σ : RegionPhysicalConfig (d := 16) R)
    (η : RegionIncidentConfig (czxPEPS width height) R)
    (hη : regionIncidentWeight (czxPEPS width height) R η σ ≠ 0) :
    regionIncidentWeight (czxPEPS width height) R η σ = 1 := by
  classical
  apply Finset.prod_eq_one
  intro w _
  exact czx_component_eq_one_of_ne_zero w.1 _ (σ w)
    ((Finset.prod_ne_zero_iff.mp hη) w (Finset.mem_univ _))

open scoped Classical in
/-- Exact support indicator of the actual CZX open-region contraction. No exterior
bond labels or unproved normalization factor enter the formula. -/
theorem openRegionWeight_czxPEPS (R : Finset (TorusVertex width height))
    (μ : RegionBoundaryConfig (czxPEPS width height) R)
    (σ : RegionPhysicalConfig (d := 16) R) :
    openRegionWeight (czxPEPS width height) R μ σ =
      if ∃ η : RegionIncidentConfig (czxPEPS width height) R,
        regionIncidentBoundaryLabel (czxPEPS width height) R η = μ ∧
          regionIncidentWeight (czxPEPS width height) R η σ ≠ 0 then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨η, hμ, hη⟩ := h
    rw [openRegionWeight, Fintype.sum_eq_single η]
    · simp [hμ, czx_regionIncidentWeight_eq_one R σ η hη]
    · intro θ hθ
      have hz : regionIncidentWeight (czxPEPS width height) R θ σ = 0 := by
        by_contra hn
        exact hθ (czx_regionIncidentConfig_unique R σ θ η hn hη)
      simp [hz]
  · apply Finset.sum_eq_zero
    intro η _
    by_cases hμ : regionIncidentBoundaryLabel (czxPEPS width height) R η = μ
    · have hz : regionIncidentWeight (czxPEPS width height) R η σ = 0 := by
        by_contra hn
        exact h ⟨η, hμ, hn⟩
      simp [hμ, hz]
    · simp [hμ]

/-- Different boundary basis vectors have disjoint physical supports under the
actual CZX region map. Source: the plaquette support of CLW11, lines 330–345. -/
theorem openRegionWeight_czxPEPS_disjoint
    (R : Finset (TorusVertex width height))
    (μ ν : RegionBoundaryConfig (czxPEPS width height) R) (hμν : μ ≠ ν)
    (σ : RegionPhysicalConfig (d := 16) R) :
    star (openRegionWeight (czxPEPS width height) R μ σ) *
      openRegionWeight (czxPEPS width height) R ν σ = 0 := by
  classical
  rw [openRegionWeight_czxPEPS, openRegionWeight_czxPEPS]
  split_ifs with hμ hν hν <;> simp only [star_zero, star_one, mul_zero, mul_one]
  obtain ⟨η, hημ, hη⟩ := hμ
  obtain ⟨θ, hθν, hθ⟩ := hν
  have hηθ := czx_regionIncidentConfig_unique R σ η θ hη hθ
  exact False.elim (hμν (hημ.symm.trans (hηθ ▸ hθν)))

/-- The actual CZX region Gram matrix is diagonal in the virtual boundary basis.
No assumption of local injectivity or a Gram formula is made. -/
theorem openRegionCoefficientMatrix_czxPEPS_gram_offDiagonal
    (R : Finset (TorusVertex width height))
    (μ ν : RegionBoundaryConfig (czxPEPS width height) R) (hμν : μ ≠ ν) :
    ((openRegionCoefficientMatrix (czxPEPS width height) R).conjTranspose *
      openRegionCoefficientMatrix (czxPEPS width height) R) μ ν = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro σ _
  exact openRegionWeight_czxPEPS_disjoint R μ ν hμν σ

/-- Assign one bit to each plaquette corner coordinate and copy it to the four
physical qubits surrounding that plaquette. -/
def czxPlaquettePhysical (q : TorusVertex width height → Fin 2)
    (v : TorusVertex width height) : Fin 16 :=
  czxQubits ((q (v.1,v.2+1), q (v.1+1,v.2+1)), (q (v.1+1,v.2), q v))

/-- Native bond labels of a plaquette-bit configuration. Right and top bonds
read their endpoint plaquettes in the tensor's native order. -/
noncomputable def czxPlaquetteBondConfig (q : TorusVertex width height → Fin 2) :
    Edge (torusGraph width height) → Fin 4 :=
  (Sum.elim (fun v => czxBond (q (v.1+1,v.2+1), q (v.1+1,v.2)))
    (fun v => czxBond (q (v.1,v.2+1), q (v.1+1,v.2+1)))) ∘ torusEdgeEquiv.symm

@[simp] theorem czxPlaquetteBondConfig_right (q : TorusVertex width height → Fin 2)
    (v : TorusVertex width height) :
    czxPlaquetteBondConfig q (torusRightEdge v) =
      czxBond (q (v.1+1,v.2+1), q (v.1+1,v.2)) := by
  change (Sum.elim _ _) (torusEdgeEquiv.symm (torusEdgeEquiv (Sum.inl v))) = _
  simp only [Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem czxPlaquetteBondConfig_up (q : TorusVertex width height → Fin 2)
    (v : TorusVertex width height) :
    czxPlaquetteBondConfig q (torusUpEdge v) =
      czxBond (q (v.1,v.2+1), q (v.1+1,v.2+1)) := by
  change (Sum.elim _ _) (torusEdgeEquiv.symm (torusEdgeEquiv (Sum.inr v))) = _
  simp only [Equiv.symm_apply_apply, Sum.elim_inr]

/-- Every site tensor takes value one on its plaquette-copying configuration. -/
theorem component_czxPlaquettePhysical (q : TorusVertex width height → Fin 2)
    (v : TorusVertex width height) :
    (czxPEPS width height).component v (fun e => czxPlaquetteBondConfig q e.1)
      (czxPlaquettePhysical q v) = 1 := by
  change czxSiteTensor (czxPlaquetteBondConfig q (torusUpEdge v))
    (czxPlaquetteBondConfig q (torusRightEdge v))
    (czxBondSwap (czxPlaquetteBondConfig q (torusDownEdge v)))
    (czxBondSwap (czxPlaquetteBondConfig q (torusLeftEdge v))) _ = 1
  simp [torusDownEdge, torusLeftEdge, czxSiteTensor, czxPlaquettePhysical,
    czxTopLeft, czxTopRight, czxBottomRight, czxBottomLeft]

/-- A plaquette-bit configuration witnesses a nonzero actual region column.
This also fixes its normalization: the selected coefficient is exactly one. -/
theorem openRegionWeight_czxPlaquettePhysical (R : Finset (TorusVertex width height))
    (q : TorusVertex width height → Fin 2) :
    openRegionWeight (czxPEPS width height) R
      (fun e => czxPlaquetteBondConfig q e.1) (fun v => czxPlaquettePhysical q v.1) = 1 := by
  classical
  apply (openRegionWeight_czxPEPS R
    (fun e => czxPlaquetteBondConfig q e.1) (fun v => czxPlaquettePhysical q v.1)).trans
  apply ite_eq_left
  refine ⟨fun e => czxPlaquetteBondConfig q e.1, rfl, ?_⟩
  simp [regionIncidentWeight, component_czxPlaquettePhysical]

end TNLean.PEPS
