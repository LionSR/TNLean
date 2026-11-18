/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.BlockRangeCoincidence
import TNLean.PEPS.Examples.HoneycombPlaquette
import TNLean.PEPS.OpenRegionContraction

/-!
# Injectivity of one honeycomb face

For the concrete six-site face on the (6 × 4) honeycomb torus, the
open-region coefficient matrix has column Gram matrix (I / 64).
-/

open scoped BigOperators
open ManyBody (Edge)

namespace TNLean.PEPS

theorem hadamardEntry_columnGram (i j : Fin 2) :
    ∑ s : Fin 2, star (hadamardEntry s i) * hadamardEntry s j =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_two, hadamardEntry, Complex.invSqrtTwo_mul_self]

end TNLean.PEPS

namespace TNLean.PEPS.HoneycombFace
private instance : Fact (1 < 6) := ⟨by decide⟩
private instance : Fact (1 < 4) := ⟨by decide⟩

noncomputable def faceSpin (x : Fin 6 → Fin 2) (v : Site) : Fin 2 :=
  if h : ∃ i, vertex i = v then x h.choose else 0

private theorem faceSpin_vertex (x : Fin 6 → Fin 2) (i : Fin 6) :
    faceSpin x (vertex i) = x i := by
  unfold faceSpin
  split
  next h => rw [distinct_sites _ _ h.choose_spec]
  next h => exact (h ⟨i, rfl⟩).elim

private theorem localGram (i : Fin 6) (b c : Fin 2) :
    ∑ s : Fin 2, star (graphStateLeg graph (vertex i) (outer i) b s) *
      graphStateLeg graph (vertex i) (outer i) c s = if b = c then 1 else 0 := by
  unfold graphStateLeg
  split
  · exact hadamardEntry_columnGram b c
  · fin_cases b <;> fin_cases c <;> norm_num [Fin.sum_univ_two]

private theorem internalGram (a b : Fin 2) :
    star (hadamardEntry a b) * hadamardEntry a b = (2 : ℂ)⁻¹ := by
  fin_cases a <;> fin_cases b <;> norm_num [hadamardEntry, Complex.invSqrtTwo_mul_self]

theorem contraction_columnGram (b c : Fin 6 → Fin 2) :
    ∑ x : Fin 6 → Fin 2, star (sixBondContraction graph inner outer vertex (faceSpin x) b) *
      sixBondContraction graph inner outer vertex (faceSpin x) c =
        (2 : ℂ)⁻¹ ^ 6 * (if b = c then 1 else 0) := by
  classical
  simp only [contraction, faceSpin_vertex, map_mul,
    show ∀ z : ℂ, star z = (starRingEnd ℂ) z by intro z; rfl, map_prod]
  conv_lhs =>
    enter [2, x]
    rw [show ∀ a b c d : ℂ, (a * b) * (c * d) = (a * c) * (b * d) by
      intros; ring]
  simp only [← Finset.prod_mul_distrib,
    ← show ∀ z : ℂ, star z = (starRingEnd ℂ) z by intro z; rfl, internalGram,
     Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun i s =>
    star (graphStateLeg graph (vertex i) (outer i) (b i) s) *
      graphStateLeg graph (vertex i) (outer i) (c i) s)]
  simp_rw [localGram]
  by_cases h : b = c
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [ite_eq_right h, mul_zero]
    rw [Finset.prod_eq_zero (i := i) (f := fun j => if b j = c j then (1 : ℂ) else 0)
      (Finset.mem_univ i) (ite_eq_right hi), mul_zero]

end TNLean.PEPS.HoneycombFace

namespace TNLean.PEPS.HoneycombFace

def faceRegion : Finset Site := Finset.univ.image vertex
abbrev Internal := {e : Edge graph // e.1.1 ∈ faceRegion ∧ e.1.2 ∈ faceRegion}
abbrev Boundary := {e : Edge graph // IsRegionBoundaryEdge faceRegion e}

set_option maxRecDepth 20000

def internalIndex (i : Fin 6) : Internal :=
  ⟨inner i, (by decide : ∀ j, (inner j).1.1 ∈ faceRegion ∧ (inner j).1.2 ∈ faceRegion) i⟩

def boundaryIndex (i : Fin 6) : Boundary :=
  ⟨outer i, (by decide : ∀ j, IsRegionBoundaryEdge faceRegion (outer j)) i⟩

noncomputable def internalEquiv : Fin 6 ≃ Internal :=
  Equiv.ofBijective internalIndex ⟨by
    exact (by decide : ∀ i j, internalIndex i = internalIndex j → i = j), by
    exact (by decide : ∀ e : Internal, ∃ i, internalIndex i = e)⟩

noncomputable def boundaryEquiv : Fin 6 ≃ Boundary :=
  Equiv.ofBijective boundaryIndex ⟨by
    exact (by decide : ∀ i j, boundaryIndex i = boundaryIndex j → i = j), by
    exact (by decide : ∀ e : Boundary, ∃ i, boundaryIndex i = e)⟩

abbrev Incident := {e : Edge graph // IsRegionIncidentEdge faceRegion e}

def incidentIndex : Fin 6 ⊕ Fin 6 → Incident
  | .inl i => ⟨inner i, Or.inl (internalIndex i).2.1⟩
  | .inr i => ⟨outer i, isRegionBoundaryEdge_touches _ (boundaryIndex i).2⟩

noncomputable def incidentEquiv : Fin 6 ⊕ Fin 6 ≃ Incident :=
  Equiv.ofBijective incidentIndex ⟨by
    exact (by decide : ∀ i j, incidentIndex i = incidentIndex j → i = j), by
    exact (by decide : ∀ e : Incident, ∃ i, incidentIndex i = e)⟩

abbrev Bits := Fin 6 → Fin 2

noncomputable def configEquiv :
    RegionIncidentConfig (graphStatePEPS graph) faceRegion ≃ Bits × Bits :=
  (Equiv.arrowCongr incidentEquiv.symm (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem regionMatrix_reindexed (s : RegionPhysicalConfig (d := 2) faceRegion)
    (b : RegionBoundaryConfig (graphStatePEPS graph) faceRegion) :
    openRegionCoefficientMatrix (graphStatePEPS graph) faceRegion s b =
      ∑ x : Bits, regionIncidentWeight (graphStatePEPS graph) faceRegion
        (configEquiv.symm (x, fun i => b (boundaryEquiv i))) s := by
  classical
  unfold openRegionCoefficientMatrix openRegionWeight
  rw [← configEquiv.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  let t : Bits := fun i => b (boundaryEquiv i)
  have readOuter (y : Bits) (i : Fin 6) :
      regionIncidentBoundaryLabel _ _ (configEquiv.symm (x, y)) (boundaryEquiv i) = y i := by
    change Sum.elim x y (incidentEquiv.symm (incidentEquiv (.inr i))) = y i
    rw [Equiv.symm_apply_apply]
    rfl
  have h (y : Bits) : regionIncidentBoundaryLabel _ _ (configEquiv.symm (x, y)) = b ↔
      y = t := by
    constructor
    · intro he
      exact funext fun i => (readOuter y i).symm.trans (congrFun he (boundaryEquiv i))
    · intro he
      subst y
      funext e
      obtain ⟨i, rfl⟩ := boundaryEquiv.surjective e
      exact readOuter t i
  simp_rw [h]
  simp
  rfl

end TNLean.PEPS.HoneycombFace

namespace TNLean.PEPS.HoneycombFace

abbrev RSite := {v : Site // v ∈ faceRegion}
abbrev PairIdx := (w : RSite) × IncidentEdge graph w.1
abbrev Role := (Fin 6 ⊕ Fin 6) ⊕ Fin 6

def rowSite (i : Fin 6) : RSite := ⟨vertex i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩

noncomputable def rowEquiv : Fin 6 ≃ RSite :=
  Equiv.ofBijective rowSite ⟨fun _ _ h => distinct_sites _ _ (congrArg Subtype.val h), by
    exact (by decide : ∀ v : RSite, ∃ i, rowSite i = v)⟩

def rolePair : Role → PairIdx
  | .inl (.inl i) =>
    ⟨⟨(inner i).1.1, (internalIndex i).2.1⟩, ⟨inner i, Or.inl rfl⟩⟩
  | .inl (.inr i) =>
    ⟨⟨(inner i).1.2, (internalIndex i).2.2⟩, ⟨inner i, Or.inr rfl⟩⟩
  | .inr i => ⟨rowSite i, ⟨outer i, (by decide : ∀ j,
      (outer j).1.1 = vertex j ∨ (outer j).1.2 = vertex j) i⟩⟩

noncomputable def roleEquiv : Role ≃ PairIdx :=
  Equiv.ofBijective rolePair ⟨by
    exact (by decide : ∀ i j, rolePair i = rolePair j → i = j), by
    exact (by decide : ∀ p : PairIdx, ∃ i, rolePair i = p)⟩

private theorem readInner (x b : Bits) (i : Fin 6) :
    configEquiv.symm (x,b) (incidentEquiv (.inl i)) = x i := by
  change Sum.elim x b (incidentEquiv.symm (incidentEquiv (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem readBoundary (x b : Bits) (i : Fin 6) :
    configEquiv.symm (x,b) (incidentEquiv (.inr i)) = b i := by
  change Sum.elim x b (incidentEquiv.symm (incidentEquiv (.inr i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def rowConfig (s : Bits) : RegionPhysicalConfig (d := 2) faceRegion :=
  fun v => faceSpin s v.1

theorem weight_regroup (x b s : Bits) :
    regionIncidentWeight (graphStatePEPS graph) faceRegion (configEquiv.symm (x,b)) (rowConfig s) =
      (∏ i, graphStateLeg graph (inner i).1.1 (inner i) (x i) (faceSpin s (inner i).1.1) *
        graphStateLeg graph (inner i).1.2 (inner i) (x i) (faceSpin s (inner i).1.2)) *
      ∏ i, graphStateLeg graph (vertex i) (outer i) (b i) (faceSpin s (vertex i)) := by
  let f (p : PairIdx) := graphStateLeg graph p.1.1 p.2.1
    (configEquiv.symm (x,b) ⟨p.2.1, isRegionIncidentEdge_of_regionVertex _ p.1 p.2⟩)
    (faceSpin s p.1.1)
  change (∏ w, ∏ e, f ⟨w,e⟩) = _
  rw [← Fintype.prod_sigma, ← roleEquiv.prod_comp f, Fintype.prod_sum_type,
    Fintype.prod_sum_type, Finset.prod_mul_distrib]
  change ((∏ i, graphStateLeg _ _ _ (configEquiv.symm (x,b) (incidentEquiv (.inl i))) _) *
    (∏ i, graphStateLeg _ _ _ (configEquiv.symm (x,b) (incidentEquiv (.inl i))) _)) *
    (∏ i, graphStateLeg _ _ _ (configEquiv.symm (x,b) (incidentEquiv (.inr i))) _) = _
  simp_rw [readInner, readBoundary]
  rfl

noncomputable def rows : Bits ≃ RegionPhysicalConfig (d := 2) faceRegion :=
  Equiv.arrowCongr rowEquiv (Equiv.refl _)

private theorem rows_eq (s : Bits) : rows s = rowConfig s := by
  funext v
  obtain ⟨i,rfl⟩ := rowEquiv.surjective v
  change s (rowEquiv.symm (rowEquiv i)) = faceSpin s (vertex i)
  rw [Equiv.symm_apply_apply, faceSpin_vertex]

noncomputable abbrev Mat := openRegionCoefficientMatrix (graphStatePEPS graph) faceRegion

theorem region_entry (s : Bits) (b : RegionBoundaryConfig (graphStatePEPS graph) faceRegion) :
    Mat (rows s) b = sixBondContraction graph inner outer vertex (faceSpin s)
      (fun i => b (boundaryEquiv i)) := by
  rw [rows_eq]
  apply (regionMatrix_reindexed _ b).trans
  exact Finset.sum_congr rfl fun x _ => weight_regroup x _ s

/-- The concrete face matrix has orthogonal columns, each of squared norm `1 / 64`. -/
theorem actual_columnGram (b c : RegionBoundaryConfig (graphStatePEPS graph) faceRegion) :
    ∑ s, star (Mat s b) * Mat s c = (2 : ℂ)⁻¹ ^ 6 * (if b = c then 1 else 0) := by
  classical
  rw [← rows.sum_comp]
  simp_rw [region_entry]
  apply (contraction_columnGram (fun i => b (boundaryEquiv i)) (fun i => c (boundaryEquiv i))).trans
  congr 2
  apply propext
  constructor
  · intro h
    funext e
    obtain ⟨i,rfl⟩ := boundaryEquiv.surjective e
    exact congrFun h i
  · rintro rfl
    rfl

/-- The open-region map of the checked six-site face is injective. -/
theorem actual_injective :
    Function.Injective (openRegionMap (graphStatePEPS graph) faceRegion) := by
  classical
  intro x y h
  funext b
  have extract (z : RegionBoundaryConfig (graphStatePEPS graph) faceRegion → ℂ) :
      ∑ s, star (Mat s b) * (openRegionMap (graphStatePEPS graph) faceRegion z) s =
        z b * ((2 : ℂ)⁻¹ ^ 6) := by
    simp_rw [openRegionMap_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ c, z c * (∑ s, star (Mat s b) * Mat s c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        change _ * (z c * Mat s c) = _
        ring
      _ = _ := by simp_rw [actual_columnGram]; simp
  have he := extract x
  rw [h, extract y] at he
  exact mul_right_cancel₀ (by norm_num : (2 : ℂ)⁻¹ ^ 6 ≠ 0) he.symm

end TNLean.PEPS.HoneycombFace
