import TNLean.PEPS.TorusCutCoefficientExtraction
import TNLean.PEPS.TorusCutProjectorExpansion

/-! Regression checks for the literal four-block cut spaces. -/

open TNLean.PEPS

example : Fintype.card (TorusCutBoundaryConfig 2 2 (Fin 2)) = 256 := by
  rw [card_torusCutBoundaryConfig_two]
  norm_num

example : Fintype.card (TorusBondLabels 2 2 (Multiplicative (ZMod 2))) = 256 := by
  rw [card_torusBondLabels_two]
  norm_num

private def boundary (x y : Fin 2) : TorusCutBoundaryConfig 2 2 (Fin 2) :=
  (fun i ↦ if i = 0 then (x, 0) else (0, 0),
    fun i ↦ if i = 0 then (y, 0) else (0, 0))
private def correlated (η : TorusCutBoundaryConfig 2 2 (Fin 2)) : ℂ :=
  if (η.1 0).1 = (η.2 0).1 then 1 else 0
example : ¬∃ Oh Ov : TorusVertex 2 2 → Matrix (Fin 2) (Fin 2) ℂ,
    correlated = torusCutBondBoundary 0 0 Oh Ov := by
  rintro ⟨Oh, Ov, h⟩
  have h00 := congrFun h (boundary 0 0)
  have h01 := congrFun h (boundary 0 1)
  have h11 := congrFun h (boundary 1 1)
  simp only [correlated, boundary, Fin.isValue, ite_self, ↓reduceIte,
    torusCutBondBoundary, zero_sub, ZMod.neg_eq_self_mod_two, zero_ne_one, zero_eq_mul]
    at h00 h01 h11
  rcases h01 with hh | hv
  · rw [hh, zero_mul] at h00
    exact one_ne_zero h00
  · rw [hv, mul_zero] at h11
    exact one_ne_zero h11

section SiteDependence
variable {G V Phys : Type*} [Group G] [Fintype V] [DecidableEq V]

-- The four physical tensors are independent parameters; no homogeneity is inferred.
example (U : G →* Matrix V V ℂ)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusLegRep U g = siteMap (a v)) :
    sitewiseCommutingClosureSpan U a ≤ fourTorusCutSpace a :=
  sitewiseCommutingClosureSpan_le_fourTorusCutSpace U a ha

-- The coefficient characterization quantifies over one arbitrary joint boundary tensor.
example (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ψ : (TorusVertex 2 2 → Phys) → ℂ) :
    ψ ∈ fourTorusCutSpace a ↔
      ∀ c r, ∃ M : TorusCutBoundaryConfig 2 2 V → ℂ,
        ∀ σ, torusCutCoeff a c r M σ = ψ σ :=
  mem_fourTorusCutSpace_iff a ψ

variable [Fintype G] [Finite Phys]

-- Each of the eight bonds may have a different matching representation.
example (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v, IsGInjective (torusMatchedLegRep Uh Uv v) (siteMap (a v))) :
    fourTorusCutSpace a =
      (fourTorusCutSpace (fun v ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v))).map
        (torusSitewisePhysicalMap (fun v ↦ LinearMap.toMatrix' (siteMap (a v)))) :=
  fourTorusCutSpace_eq_map_representationAveragingSite _ a ha

-- Coherent sums cannot be compared term by term until this dual extraction is applied.
example (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (c d : TorusBondLabels 2 2 G → ℂ)
    (heq : (∑ q, c q • torusRepresentationBondProduct Uh Uv q) =
      ∑ q, d q • torusRepresentationBondProduct Uh Uv q) : c = d :=
  (sum_torusRepresentationBondProduct_eq_iff Uh Uv hU c d).mp heq
end SiteDependence

set_option linter.hashCommand false

#print axioms TNLean.PEPS.torusCutCoeff_bondBoundary
#print axioms TNLean.PEPS.torusCutSpace_eq_span_single
#print axioms TNLean.PEPS.sitewiseCommutingClosureSpan_le_fourTorusCutSpace
#print axioms TNLean.PEPS.fourTorusCutSpace_eq_map_representationAveragingSite
#print axioms TNLean.PEPS.torusCutCoeff_representationAveragingSite
#print axioms TNLean.PEPS.torusBondCoefficientExtraction_sum
#print axioms TNLean.PEPS.linearIndependent_torusRepresentationBondProduct
