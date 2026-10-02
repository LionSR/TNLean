/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteIndicatorSum
import TNLean.PEPS.RegularRegionGramExpansion
import TNLean.PEPS.RegularSiteGram
import TNLean.PEPS.RegionPhysicalMap

/-!
# Open regions in the physical coordinates of the regular averaging projector

The canonical physical coordinate at a site is one group label on each incident
half-edge. The region matrix fixes its crossing labels and sums only the incident
bond labels. Thus every internal bond is summed once, and no exterior labels occur.
The local coefficient is the regular averaging projector itself.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Observation
`obs:iso:accessible-virt` and the subsequent blocking argument,
`Papers/1001.3807/paper_v3.tex`, lines 1765–1920. The construction retains the
original graph and its actual open-region contraction.

**Local fix (normalization):** The two existence statements recovering the
projector use the positive site factors allowed by `IsGIsometric`. The normalized
adjoint is divided by that factor. This convention is documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The physical coordinates exposed by the regular projector at the sites of
an open region: one group label on each incident half-edge. -/
abbrev RegionHalfEdgeConfig (G : Type*) (R : Finset V) :=
  (w : {w : V // w ∈ R}) → IncidentEdge Γ w.1 → G

/-- The canonical regular-projector region coefficients. Crossing labels are
fixed; the summation then runs once over each internal bond assignment. -/
noncomputable def regularProjectorOpenRegionMatrix (R : Finset V) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R)
      ({f : Edge Γ // IsRegionBoundaryEdge R f} → G) ℂ :=
  fun α θ => ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
    if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ then
      ∏ w : {w : V // w ∈ R},
        regularLegProjector (IncidentEdge Γ w.1) (α w)
          (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)
    else 0

/-- With the canonical regular-projector coefficients, the local physical map
is exactly the regular averaging projector. -/
theorem regularSiteMap_regularLegProjector
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    regularSiteMap (fun η α : ι → G => regularLegProjector ι α η) =
      (regularLegRepresentation (G := G) ι).averageMap := by
  change Matrix.toLin' (LinearMap.toMatrix' _) = _
  exact Matrix.toLin'_toMatrix' _

/-- The canonical coefficient map is regular G-isometric with factor one.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1784. -/
theorem isGIsometric_regularLegProjector
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsGIsometric (regularLegRepresentation (G := G) ι)
      (regularSiteMap (fun η α : ι → G => regularLegProjector ι α η)) := by
  rw [regularSiteMap_regularLegProjector]
  let ρ := regularLegRepresentation (G := G) ι
  have hinv : ∀ g, ρ.averageMap ∘ₗ ρ g = ρ.averageMap := by
    intro g
    change ρ.averageMap * ρ g = ρ.averageMap
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← map_mul, GroupAlgebra.mul_average_right]
  refine ⟨⟨hinv, ?_⟩, 1, zero_lt_one, ?_⟩
  · intro x hx hzero
    rwa [ρ.averageMap_id x hx] at hzero
  · intro x hx y hy
    rw [ρ.averageMap_id x hx, ρ.averageMap_id y hy]
    simp only [Complex.ofReal_one, one_mul]

/-- A local G-injective inverse recovers the canonical regular projector
coefficients. Source: SCP10, Definition 5.1(ii), lines 1278–1296. -/
theorem IsGInjective.exists_regularProjectorCoefficients
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {a : (ι → G) → κ → ℂ}
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a)) :
    ∃ F : Matrix (ι → G) κ ℂ, ∀ α η : ι → G,
      (∑ s : κ, F α s * a η s) = regularLegProjector ι α η := by
  classical
  obtain ⟨-, L, hL⟩ := (isGInjective_iff_exists_leftInverse _ _).mp ha
  refine ⟨LinearMap.toMatrix' L, fun α η => ?_⟩
  have hmat := congrArg LinearMap.toMatrix' hL
  rw [LinearMap.toMatrix'_comp, toMatrix_regularSiteMap] at hmat
  exact congrFun (congrFun hmat α) η

/-- The adjoint coefficients of a regular isometric site recover the canonical
projector coefficients after division by its positive isometry factor. -/
theorem IsGIsometric.exists_regularProjectorCoefficients
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {a : (ι → G) → κ → ℂ}
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ α η : ι → G,
      (∑ s : κ, ((c : ℂ)⁻¹ * star (a α s)) * a η s) =
        regularLegProjector ι α η := by
  obtain ⟨c, hc, h⟩ := ha.exists_regularSiteGram
  refine ⟨c, hc, fun α η => ?_⟩
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hgram : (∑ s : κ, star (a α s) * a η s) =
      (c : ℂ) * regularLegProjector ι α η := by
    rw [h, regularLegProjector_apply]
    simp only [div_eq_mul_inv, mul_assoc]
  calc
    _ = (c : ℂ)⁻¹ * ∑ s : κ, star (a α s) * a η s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      exact mul_assoc _ _ _
    _ = _ := by rw [hgram, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

/-- An invariant regular site is unchanged when its virtual projector is
inserted. This is the reverse local operation in SCP10 Observation
`obs:iso:accessible-virt`, lines 1765–1784. -/
theorem IsGInjective.regularSiteMap_projector_coefficients
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {a : (ι → G) → κ → ℂ}
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a))
    (s : κ) (η : ι → G) :
    (∑ α : ι → G, a α s * regularLegProjector ι α η) = a η s := by
  have hmap : regularSiteMap a ∘ₗ (regularLegRepresentation ι).averageMap =
      regularSiteMap a := LinearMap.ext (apply_averageMap_of_forall_comp_eq ha.invariant)
  have hmat := congrArg LinearMap.toMatrix' hmap
  rw [LinearMap.toMatrix'_comp, toMatrix_regularSiteMap] at hmat
  exact congrFun (congrFun hmat s) η

/-- Expanding the canonical projector at each site gives one group translation
per vertex and the original internal-bond summation. -/
theorem regularProjectorOpenRegionMatrix_apply (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularProjectorOpenRegionMatrix R α θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card *
        ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
          ∑ q : {w : V // w ∈ R} → G,
            if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                  η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ ∧
                (∀ w : {w : V // w ∈ R}, α w = q w •
                  (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩))
            then 1 else 0 := by
  classical
  unfold regularProjectorOpenRegionMatrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  by_cases hb : (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ
  · simp only [hb, ↓reduceIte, true_and]
    simp only [regularLegProjector_apply, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    congr 1
    exact Fintype.prod_sum_boole _
  · simp only [hb, ↓reduceIte, false_and, Finset.sum_const_zero, mul_zero]

variable {d : ℕ}

omit [Fintype V] [DecidableEq G] in
/-- Encoding the group labels does not alter the prescribed boundary condition. -/
theorem regionIncidentBoundaryLabel_regularGroup_iff
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (η : {f : Edge Γ // IsRegionIncidentEdge R f} → G)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regionIncidentBoundaryLabel (groupBondTensor a) R
        (regularRegionIncidentConfigEquiv a R η) =
          (fun f => Fintype.equivFin G (θ f)) ↔
      (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ :=
  (Equiv.piCongrRight (fun _ : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
    Fintype.equivFin G)).injective.eq_iff

/-- Local physical maps recovering the projector coefficients identify the
canonical matrix with the original finite-region contraction, coefficient by
coefficient. No global Gram or factorization identity is assumed. -/
theorem regionPhysicalMap_eq_regularProjectorOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regionPhysicalMap R F (openRegionWeight (groupBondTensor a) R
      (fun f => Fintype.equivFin G (θ f))) α =
      regularProjectorOpenRegionMatrix R α θ := by
  classical
  rw [regionPhysicalMap_openRegionWeight,
    ← Equiv.sum_comp (regularRegionIncidentConfigEquiv a R)]
  unfold regularProjectorOpenRegionMatrix
  apply Finset.sum_congr rfl
  intro η _
  simp only [regionIncidentBoundaryLabel_regularGroup_iff]
  split_ifs
  · apply Finset.prod_congr rfl
    intro w _
    simpa only [groupBondTensor, regularRegionIncidentConfigEquiv,
      Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply] using
      hF w.1 (α w) (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)
  · rfl

/-- In an enumeration of the crossing bonds, the product of the local physical
matrices with the actual ordered open-region matrix is the canonical matrix. -/
theorem regionPhysicalProductMatrix_mul_regularOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regionPhysicalProductMatrix R F * regularOpenRegionMatrix a R e =
      fun α x => regularProjectorOpenRegionMatrix R α (fun f => x (e f)) := by
  ext α x
  change regionPhysicalMap R F (fun σ => regularOpenRegionMatrix a R e σ x) α = _
  exact regionPhysicalMap_eq_regularProjectorOpenRegionMatrix a F hF R α (fun f => x (e f))

/-- Recovering the original local coefficients from the canonical projector
recovers the actual contracted region as well. Source: SCP10 Observation
`obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regionPhysicalMap_regularProjectorOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regionPhysicalMap R (fun v => Matrix.of (fun s α => a v α s))
      (fun α => regularProjectorOpenRegionMatrix R α θ) =
      openRegionWeight (groupBondTensor a) R (fun f => Fintype.equivFin G (θ f)) := by
  classical
  funext σ
  rw [regionPhysicalMap_apply (In := fun v => IncidentEdge Γ v → G)
    (Out := fun _ => Fin d)]
  simp only [regularProjectorOpenRegionMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold openRegionWeight
  rw [← Equiv.sum_comp (regularRegionIncidentConfigEquiv a R)]
  apply Finset.sum_congr rfl
  intro η _
  simp only [regionIncidentBoundaryLabel_regularGroup_iff]
  by_cases hb : (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ
  · simp only [hb, ↓reduceIte, Matrix.of_apply, regionIncidentWeight,
      groupBondTensor, regularRegionIncidentConfigEquiv, Equiv.piCongrRight_apply,
      Pi.map_apply, Equiv.symm_apply_apply, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (w : {w : V // w ∈ R}) (β : IncidentEdge Γ w.1 → G) =>
      a w.1 β (σ w) * regularLegProjector (IncidentEdge Γ w.1) β
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩))]
    apply Finset.prod_congr rfl
    intro w _
    exact (ha w.1).regularSiteMap_projector_coefficients _ _
  · simp only [hb, ↓reduceIte, mul_zero, Finset.sum_const_zero]

/-- Applying the normalized local adjoint at every site of an actual regular
isometric region exposes the canonical half-edge physical coordinates.
Source: SCP10, Observation `obs:iso:accessible-virt`, lines 1765–1820.
The positive factors are those of `IsGIsometric`. -/
theorem exists_regularProjectorOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) :
    ∃ c : V → ℝ, (∀ v, 0 < c v) ∧ ∀ (R : Finset V)
      (α : RegionHalfEdgeConfig (Γ := Γ) G R)
      (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G),
      regionPhysicalMap R (fun v α s => (c v : ℂ)⁻¹ * star (a v α s))
        (openRegionWeight (groupBondTensor a) R
          (fun f => Fintype.equivFin G (θ f))) α =
        regularProjectorOpenRegionMatrix R α θ := by
  classical
  choose c hc h using fun v => (ha v).exists_regularProjectorCoefficients
  refine ⟨c, hc, fun R α θ => ?_⟩
  exact regionPhysicalMap_eq_regularProjectorOpenRegionMatrix a _ h R α θ

end TNLean.PEPS
