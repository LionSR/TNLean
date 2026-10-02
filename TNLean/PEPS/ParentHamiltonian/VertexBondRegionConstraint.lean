/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.VertexBondCoordinates
import TNLean.PEPS.ParentHamiltonian.VertexInverseRegionSlice

/-!
# Internal Bell constraints from actual regional virtual contractions

Every internal edge of a region carries one common bond label in its
actual virtual contraction. Its coefficients vanish when the two endpoint
labels differ and are unchanged when both labels are permuted together.
These identities imply the Bell-vector condition on each fixed-complement
bond slice of a global vector satisfying the actual regional virtual
support conditions. No positivity of bond dimensions is assumed.

Source: CPGSV21, arXiv:2011.12127, Section IV.C.1, the independent
virtual-bond constraints and site inverses, lines 2017–2044.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Permute the labels of one bond and leave every other bond unchanged.
Source: the independent virtual Bell pair in CPGSV21, lines 2017–2028. -/
noncomputable def edgeLabelPerm (A : Tensor Γ d) (e : Edge Γ)
    (σ : Equiv.Perm (Fin (A.bondDim e))) (f : Edge Γ) :
    Equiv.Perm (Fin (A.bondDim f)) := by
  classical
  exact if h : f = e then h ▸ σ else Equiv.refl _

/-- Simultaneously permute both half-edge labels of one bond in a region.
Source: the common label of each virtual pair in CPGSV21, lines 2017–2028. -/
noncomputable def regionVertexEdgeLabelPerm (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (σ : Equiv.Perm (Fin (A.bondDim e))) :
    Equiv.Perm (RegionVertexVirtualConfig A R) :=
  Equiv.piCongrRight (fun _ => Equiv.piCongrRight (fun f => edgeLabelPerm A e σ f.1))

private noncomputable def regionIncidentEdgeLabelPerm (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (σ : Equiv.Perm (Fin (A.bondDim e))) :
    Equiv.Perm (RegionIncidentConfig A R) :=
  Equiv.piCongrRight (fun f => edgeLabelPerm A e σ f.1)

omit [Fintype V] in
private theorem edgeLabelPerm_apply_self (A : Tensor Γ d) (e : Edge Γ)
    (σ : Equiv.Perm (Fin (A.bondDim e))) (a : Fin (A.bondDim e)) :
    edgeLabelPerm A e σ e a = σ a := by
  simp only [edgeLabelPerm, dite_true]

omit [Fintype V] in
private theorem edgeLabelPerm_apply_of_ne (A : Tensor Γ d) (e f : Edge Γ)
    (σ : Equiv.Perm (Fin (A.bondDim e))) (h : f ≠ e) (a : Fin (A.bondDim f)) :
    edgeLabelPerm A e σ f a = a := by
  simp only [edgeLabelPerm, dite_false, h, Equiv.refl_apply]

omit [Fintype V] in
private theorem regionIncidentVertexConfig_edgeLabelPerm (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (σ : Equiv.Perm (Fin (A.bondDim e))) (η : RegionIncidentConfig A R) :
    regionIncidentVertexConfig A R (regionIncidentEdgeLabelPerm A R e σ η) =
      regionVertexEdgeLabelPerm A R e σ (regionIncidentVertexConfig A R η) := rfl

omit [Fintype V] in
private theorem regionIncidentBoundaryLabel_edgeLabelPerm (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    (σ : Equiv.Perm (Fin (A.bondDim e))) (η : RegionIncidentConfig A R) :
    regionIncidentBoundaryLabel A R (regionIncidentEdgeLabelPerm A R e σ η) =
      regionIncidentBoundaryLabel A R η := by
  funext f
  change edgeLabelPerm A e σ f.1 _ = _
  apply edgeLabelPerm_apply_of_ne
  intro h
  have hf := f.2
  rw [h] at hf
  simp [IsRegionBoundaryEdge, hfirst, hsecond] at hf

/-- The actual virtual coefficient is unchanged by permuting both labels
of an internal edge together. Source: the independent Bell-bond summation
of CPGSV21, Section IV.C.1, lines 2017–2028. -/
theorem regionVirtualBondWeight_edgeLabelPerm (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    (σ : Equiv.Perm (Fin (A.bondDim e))) (μ : RegionBoundaryConfig A R)
    (α : RegionVertexVirtualConfig A R) :
    regionVirtualBondWeight A R μ (regionVertexEdgeLabelPerm A R e σ α) =
      regionVirtualBondWeight A R μ α := by
  classical
  unfold regionVirtualBondWeight
  simp only [Finset.sum_apply, ite_apply, Pi.single_apply, Pi.zero_apply]
  conv_lhs => rw [← Equiv.sum_comp (regionIncidentEdgeLabelPerm A R e σ)]
  apply Finset.sum_congr rfl
  intro η _
  rw [regionIncidentBoundaryLabel_edgeLabelPerm A R e hfirst hsecond σ,
    regionIncidentVertexConfig_edgeLabelPerm]
  simp only [(regionVertexEdgeLabelPerm A R e σ).injective.eq_iff]

/-- The actual virtual coefficient vanishes if an internal edge has
unequal endpoint labels. Source: the virtual Bell-bond constraint of
CPGSV21, Section IV.C.1, lines 2017–2028. -/
theorem regionVirtualBondWeight_eq_zero_of_internal_off_diagonal
    (A : Tensor Γ d) (R : Finset V) (e : Edge Γ)
    (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R) (μ : RegionBoundaryConfig A R)
    (α : RegionVertexVirtualConfig A R)
    (hne : α ⟨e.1.1, hfirst⟩ ⟨e, Or.inl rfl⟩ ≠
      α ⟨e.1.2, hsecond⟩ ⟨e, Or.inr rfl⟩) :
    regionVirtualBondWeight A R μ α = 0 := by
  classical
  have hn (η : RegionIncidentConfig A R) : regionIncidentVertexConfig A R η ≠ α := by
    intro h
    apply hne
    have h₁ := congrFun (congrFun h ⟨e.1.1, hfirst⟩) ⟨e, Or.inl rfl⟩
    have h₂ := congrFun (congrFun h ⟨e.1.2, hsecond⟩) ⟨e, Or.inr rfl⟩
    exact h₁.symm.trans h₂
  simp [regionVirtualBondWeight, ite_apply, hn]

/-- Every vector in the genuine regional virtual bond range has the
simultaneous internal-label permutation symmetry.
Source: linear consequence of the virtual Bell-bond contraction in
CPGSV21, Section IV.C.1, lines 2017–2028. -/
theorem regionVirtualBondMap_range_edgeLabelPerm (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    (σ : Equiv.Perm (Fin (A.bondDim e))) {q : RegionVertexVirtualConfig A R → ℂ}
    (hq : q ∈ (regionVirtualBondMap A R).range) (α : RegionVertexVirtualConfig A R) :
    q (regionVertexEdgeLabelPerm A R e σ α) = q α := by
  obtain ⟨x, rfl⟩ := hq
  simp only [regionVirtualBondMap, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, regionVirtualBondWeight_edgeLabelPerm A R e hfirst hsecond σ]

/-- Every vector in the genuine regional virtual bond range vanishes
at an inconsistent internal endpoint pair.
Source: linear consequence of the Bell-bond contraction in CPGSV21,
Section IV.C.1, lines 2017–2028. -/
theorem regionVirtualBondMap_range_eq_zero_of_internal_off_diagonal
    (A : Tensor Γ d) (R : Finset V) (e : Edge Γ)
    (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    {q : RegionVertexVirtualConfig A R → ℂ} (hq : q ∈ (regionVirtualBondMap A R).range)
    (α : RegionVertexVirtualConfig A R)
    (hne : α ⟨e.1.1, hfirst⟩ ⟨e, Or.inl rfl⟩ ≠
      α ⟨e.1.2, hsecond⟩ ⟨e, Or.inr rfl⟩) : q α = 0 := by
  obtain ⟨x, rfl⟩ := hq
  simp only [regionVirtualBondMap, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply,
    regionVirtualBondWeight_eq_zero_of_internal_off_diagonal A R e hfirst hsecond _ α hne,
    smul_zero, Finset.sum_const_zero]

private theorem assembleDependentRegionConfig_restrict (A : Tensor Γ d) (R : Finset V)
    (ξ : RegionVertexVirtualConfig A Finset.univ) :
    assembleDependentRegionConfig R
      (fun w => ξ ⟨w.1, Finset.mem_univ w.1⟩)
      (fun w => ξ ⟨w.1, Finset.mem_univ w.1⟩) = ξ := by
  funext w
  simp only [assembleDependentRegionConfig]
  split_ifs <;> rfl

private theorem regionVertexEdgeLabelPerm_assemble (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    (σ : Equiv.Perm (Fin (A.bondDim e))) (α : RegionVertexVirtualConfig A R)
    (τ : RegionVertexVirtualConfig A (Finset.univ \ R)) :
    regionVertexEdgeLabelPerm A Finset.univ e σ (assembleDependentRegionConfig R α τ) =
      assembleDependentRegionConfig R (regionVertexEdgeLabelPerm A R e σ α) τ := by
  classical
  funext w f
  by_cases hw : w.1 ∈ R
  · simp only [regionVertexEdgeLabelPerm, Equiv.piCongrRight_apply, Pi.map_apply,
      assembleDependentRegionConfig, hw, dite_true]
  · have hfe : f.1 ≠ e := by
      intro h
      rcases f.2 with hf | hf
      · rw [h] at hf
        exact hw (hf ▸ hfirst)
      · rw [h] at hf
        exact hw (hf ▸ hsecond)
    simp only [regionVertexEdgeLabelPerm, Equiv.piCongrRight_apply, Pi.map_apply,
      assembleDependentRegionConfig, hw, dite_false,
      edgeLabelPerm_apply_of_ne A e f.1 σ hfe]

/-- Regional virtual support implies simultaneous internal-bond label
permutation symmetry of the global independent-vertex coefficient vector.
Source: the actual virtual Bell-bond constraints of CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem vertexVirtual_edgeLabelPerm_of_regionSlices (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    {ξ : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hξ : ∀ τ : RegionVertexVirtualConfig A (Finset.univ \ R),
      dependentRegionSlice R τ ξ ∈ (regionVirtualBondMap A R).range)
    (σ : Equiv.Perm (Fin (A.bondDim e))) (α : RegionVertexVirtualConfig A Finset.univ) :
    ξ (regionVertexEdgeLabelPerm A Finset.univ e σ α) = ξ α := by
  let β : RegionVertexVirtualConfig A R := fun w => α ⟨w.1, Finset.mem_univ w.1⟩
  let τ : RegionVertexVirtualConfig A (Finset.univ \ R) :=
    fun w => α ⟨w.1, Finset.mem_univ w.1⟩
  have ha : assembleDependentRegionConfig R β τ = α :=
    assembleDependentRegionConfig_restrict A R α
  have h := regionVirtualBondMap_range_edgeLabelPerm A R e hfirst hsecond σ (hξ τ) β
  change ξ (assembleDependentRegionConfig R (regionVertexEdgeLabelPerm A R e σ β) τ) =
    ξ (assembleDependentRegionConfig R β τ) at h
  rw [← regionVertexEdgeLabelPerm_assemble A R e hfirst hsecond σ, ha] at h
  exact h

/-- Global virtual coefficients vanish on inconsistent internal endpoints
whenever all complementary regional slices lie in the actual virtual bond range.
Source: the actual Bell-bond constraint in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem vertexVirtual_eq_zero_of_regionSlices_off_diagonal (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    {ξ : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hξ : ∀ τ : RegionVertexVirtualConfig A (Finset.univ \ R),
      dependentRegionSlice R τ ξ ∈ (regionVirtualBondMap A R).range)
    (α : RegionVertexVirtualConfig A Finset.univ)
    (hne : α ⟨e.1.1, Finset.mem_univ _⟩ ⟨e, Or.inl rfl⟩ ≠
      α ⟨e.1.2, Finset.mem_univ _⟩ ⟨e, Or.inr rfl⟩) : ξ α = 0 := by
  let β : RegionVertexVirtualConfig A R := fun w => α ⟨w.1, Finset.mem_univ w.1⟩
  let τ : RegionVertexVirtualConfig A (Finset.univ \ R) :=
    fun w => α ⟨w.1, Finset.mem_univ w.1⟩
  have h := regionVirtualBondMap_range_eq_zero_of_internal_off_diagonal A R e
    hfirst hsecond (hξ τ) β hne
  change ξ (assembleDependentRegionConfig R β τ) = 0 at h
  rwa [assembleDependentRegionConfig_restrict] at h

/-- A simultaneous vertex-label permutation changes exactly one endpoint
pair under the original graph coordinate equivalence.
Source: the independent virtual pair of CPGSV21, lines 2017–2028. -/
theorem fullRegionVertexConfigEquivEdgePair_edgeLabelPerm (A : Tensor Γ d)
    (e : Edge Γ) (σ : Equiv.Perm (Fin (A.bondDim e)))
    (α : RegionVertexVirtualConfig A Finset.univ) :
    fullRegionVertexConfigEquivEdgePair A (regionVertexEdgeLabelPerm A Finset.univ e σ α) =
      Function.update (fullRegionVertexConfigEquivEdgePair A α) e
        (σ ((fullRegionVertexConfigEquivEdgePair A α e).1),
          σ ((fullRegionVertexConfigEquivEdgePair A α e).2)) := by
  classical
  funext f
  by_cases hf : f = e
  · subst f
    rw [Function.update_self]
    change (edgeLabelPerm A e σ e _, edgeLabelPerm A e σ e _) = _
    simp only [edgeLabelPerm_apply_self]
    rfl
  · rw [Function.update_of_ne hf]
    change (edgeLabelPerm A e σ f _, edgeLabelPerm A e σ f _) = _
    simp only [edgeLabelPerm_apply_of_ne A e f σ hf]
    rfl

/-- In global endpoint-pair coordinates, every inconsistent internal
bond coefficient vanishes under the actual regional virtual conditions.
Source: the Bell-bond constraints of CPGSV21, lines 2017–2044. -/
theorem edgePair_eq_zero_of_regionSlices_off_diagonal (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    {ξ : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hξ : ∀ τ : RegionVertexVirtualConfig A (Finset.univ \ R),
      dependentRegionSlice R τ ξ ∈ (regionVirtualBondMap A R).range)
    (ζ : EdgePairVirtualConfig A) (hne : (ζ e).1 ≠ (ζ e).2) :
    fullRegionVertexVectorEquivEdgePair A ξ ζ = 0 := by
  let α := (fullRegionVertexConfigEquivEdgePair A).symm ζ
  change ξ α = 0
  have hp := congrFun ((fullRegionVertexConfigEquivEdgePair A).apply_symm_apply ζ) e
  change (α ⟨e.1.1, Finset.mem_univ _⟩ ⟨e, Or.inl rfl⟩,
    α ⟨e.1.2, Finset.mem_univ _⟩ ⟨e, Or.inr rfl⟩) = ζ e at hp
  apply vertexVirtual_eq_zero_of_regionSlices_off_diagonal A R e hfirst hsecond hξ α
  simpa only [← congrArg Prod.fst hp, ← congrArg Prod.snd hp] using hne

/-- Simultaneously replacing the two equal endpoint labels of an internal
bond leaves every global coefficient unchanged under actual regional virtual
support conditions. Source: CPGSV21, lines 2017–2044. -/
theorem edgePair_diagonal_update_eq_of_regionSlices (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    {ξ : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hξ : ∀ τ : RegionVertexVirtualConfig A (Finset.univ \ R),
      dependentRegionSlice R τ ξ ∈ (regionVirtualBondMap A R).range)
    (ζ : EdgePairVirtualConfig A) (a b : Fin (A.bondDim e)) :
    fullRegionVertexVectorEquivEdgePair A ξ (Function.update ζ e (a, a)) =
      fullRegionVertexVectorEquivEdgePair A ξ (Function.update ζ e (b, b)) := by
  classical
  let α := (fullRegionVertexConfigEquivEdgePair A).symm (Function.update ζ e (a, a))
  let σ := Equiv.swap a b
  have hα : regionVertexEdgeLabelPerm A Finset.univ e σ α =
      (fullRegionVertexConfigEquivEdgePair A).symm (Function.update ζ e (b, b)) := by
    apply (fullRegionVertexConfigEquivEdgePair A).injective
    rw [fullRegionVertexConfigEquivEdgePair_edgeLabelPerm, Equiv.apply_symm_apply]
    simp only [Equiv.apply_symm_apply, Function.update_self, σ, Equiv.swap_apply_left,
      Function.update_idem]
  have h := vertexVirtual_edgeLabelPerm_of_regionSlices A R e hfirst hsecond hξ σ α
  rw [hα] at h
  exact h.symm

/-- Every internal edge has the genuine Bell-vector slice condition in
global pair coordinates when the original regional virtual slice conditions
hold. No positivity or injectivity assumption is needed.
Source: the independent-bond step of CPGSV21, lines 2017–2044. -/
theorem virtualBondSlice_mem_span_of_regionVirtualSlices (A : Tensor Γ d) (R : Finset V)
    (e : Edge Γ) (hfirst : e.1.1 ∈ R) (hsecond : e.1.2 ∈ R)
    {ξ : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hξ : ∀ τ : RegionVertexVirtualConfig A (Finset.univ \ R),
      dependentRegionSlice R τ ξ ∈ (regionVirtualBondMap A R).range)
    (ζ : EdgePairVirtualConfig A) :
    virtualBondSlice A.bondDim e ζ (fullRegionVertexVectorEquivEdgePair A ξ) ∈
      Submodule.span ℂ {virtualBondBell A.bondDim e} := by
  classical
  apply Submodule.mem_span_singleton.mpr
  refine ⟨fullRegionVertexVectorEquivEdgePair A ξ
    (Function.update ζ e ((ζ e).1, (ζ e).1)), funext fun p => ?_⟩
  change _ * virtualBondBell A.bondDim e p =
    fullRegionVertexVectorEquivEdgePair A ξ (Function.update ζ e p)
  by_cases hp : p.1 = p.2
  · simp only [virtualBondBell, hp, ite_true, mul_one]
    have hdiag : p = (p.1, p.1) := Prod.ext rfl hp.symm
    rw [hdiag]
    exact edgePair_diagonal_update_eq_of_regionSlices A R e hfirst hsecond hξ ζ _ _
  · simp only [virtualBondBell, hp, ite_false, mul_zero]
    exact (edgePair_eq_zero_of_regionSlices_off_diagonal A R e hfirst hsecond hξ
      (Function.update ζ e p) (by simpa only [Function.update_self] using hp)).symm

/-- The actual two-vertex virtual support condition forces the Bell
constraint on the edge joining those vertices. Source: the nearest-neighbour
virtual-bond step of CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem virtualBondSlice_mem_span_of_twoVertexRegionSlices (A : Tensor Γ d)
    (e : Edge Γ) {ξ : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hξ : ∀ τ : RegionVertexVirtualConfig A (Finset.univ \ {e.1.1, e.1.2}),
      dependentRegionSlice {e.1.1, e.1.2} τ ξ ∈
        (regionVirtualBondMap A {e.1.1, e.1.2}).range)
    (ζ : EdgePairVirtualConfig A) :
    virtualBondSlice A.bondDim e ζ (fullRegionVertexVectorEquivEdgePair A ξ) ∈
      Submodule.span ℂ {virtualBondBell A.bondDim e} := by
  apply virtualBondSlice_mem_span_of_regionVirtualSlices A {e.1.1, e.1.2} e
    (by simp) (by simp) hξ ζ

/-- Regional virtual conditions whose regions contain both endpoints of
every edge imply all independent Bell-bond conditions on the original graph.
Source: the simultaneous virtual-pair conditions in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem edgePair_mem_virtualBondGroundSpace_of_vertexVirtualParentGroundSpace
    {ι : Type*} (A : Tensor Γ d) (R : ι → Finset V)
    (hcover : ∀ e : Edge Γ, ∃ i, e.1.1 ∈ R i ∧ e.1.2 ∈ R i)
    {ξ : RegionVertexVirtualConfig A Finset.univ → ℂ}
    (hξ : ξ ∈ vertexVirtualParentGroundSpace A R) :
    fullRegionVertexVectorEquivEdgePair A ξ ∈ virtualBondGroundSpace A.bondDim := by
  rw [mem_virtualBondGroundSpace_iff]
  intro e ζ
  obtain ⟨i, hfirst, hsecond⟩ := hcover e
  exact virtualBondSlice_mem_span_of_regionVirtualSlices A (R i) e hfirst hsecond
    ((mem_vertexVirtualParentGroundSpace_iff A R ξ).mp hξ i) ζ

end TNLean.PEPS
