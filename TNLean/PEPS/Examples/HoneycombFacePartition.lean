import TNLean.PEPS.Examples.HoneycombPlaquetteInjectivity

/-! # Four injective six-site blocks of the concrete honeycomb torus -/

namespace TNLean.PEPS.HoneycombFace

def offset : Fin 4 → Site := ![(0,0), (0,2), (3,1), (3,3)]

def shift (k : Fin 4) (v : Site) : Site :=
  (v.1 + (offset k).1, v.2 + (offset k).2)

def cellSite (p : Fin 4 × Fin 6) : Site := shift p.1 (vertex p.2)

theorem cellPartition : Function.Bijective cellSite := by
  constructor
  · exact (by decide : ∀ p q, cellSite p = cellSite q → p = q)
  · exact (by decide : ∀ v, ∃ p, cellSite p = v)

set_option maxRecDepth 20000 in
theorem translatedIncidence : ∀ (k : Fin 4) (i : Fin 6) (w : Site),
    graph.Adj (cellSite (k,i)) w ↔ w = cellSite (k,i-1) ∨ w = cellSite (k,i+1) ∨
      w = shift k (exterior i) := by decide

theorem exteriorOffCell : ∀ (k : Fin 4) (i j : Fin 6),
    shift k (exterior i) ≠ cellSite (k,j) := by decide

set_option maxRecDepth 20000 in
theorem shiftAdj : ∀ (k : Fin 4) (v w : Site),
    graph.Adj (shift k v) (shift k w) ↔ graph.Adj v w := by decide

open ManyBody (Edge)
open scoped BigOperators

namespace Cell
private instance : Fact (1 < 6) := ⟨by decide⟩
private instance : Fact (1 < 4) := ⟨by decide⟩

def vertex (k : Fin 4) (i : Fin 6) := cellSite (k,i)
theorem distinct_sites (k : Fin 4) (i j : Fin 6) (h : vertex k i = vertex k j) : i = j :=
  congrArg Prod.snd (cellPartition.1 h)

private def orderedBond (a b : Site) (h : graph.Adj a b) : Edge graph :=
  if hab : a < b then ⟨(a,b), hab, h⟩
  else ⟨(b,a), lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm h.ne), h.symm⟩

def inner (k : Fin 4) (i : Fin 6) :=
  orderedBond _ _ ((translatedIncidence k i _).2 (Or.inr (Or.inl rfl)))
def outer (k : Fin 4) (i : Fin 6) :=
  orderedBond _ _ ((translatedIncidence k i _).2 (Or.inr (Or.inr rfl)))

private abbrev contraction (k : Fin 4) := @sixBondContraction_factor Site _ graph (inner k)
      (outer k) (vertex k)
noncomputable def faceSpin (k : Fin 4) (x : Fin 6 → Fin 2) (v : Site) : Fin 2 :=
  if h : ∃ i, (vertex k) i = v then x h.choose else 0

private theorem faceSpin_vertex (k : Fin 4) (x : Fin 6 → Fin 2) (i : Fin 6) :
    (faceSpin k) x ((vertex k) i) = x i := by
  unfold faceSpin
  split
  next h => rw [(distinct_sites k) _ _ h.choose_spec]
  next h => exact (h ⟨i, rfl⟩).elim

private theorem localGram (k : Fin 4) (i : Fin 6) (b c : Fin 2) :
    ∑ s : Fin 2, star (graphStateLeg graph ((vertex k) i) ((outer k) i) b s) *
      graphStateLeg graph ((vertex k) i) ((outer k) i) c s = if b = c then 1 else 0 := by
  unfold graphStateLeg
  split
  · exact hadamardEntry_columnGram b c
  · fin_cases b <;> fin_cases c <;> norm_num [Fin.sum_univ_two]

private theorem internalGram (a b : Fin 2) :
    star (hadamardEntry a b) * hadamardEntry a b = (2 : ℂ)⁻¹ := by
  fin_cases a <;> fin_cases b <;> norm_num [hadamardEntry, Complex.invSqrtTwo_mul_self]

theorem contraction_columnGram (k : Fin 4) (b c : Fin 6 → Fin 2) :
    ∑ x : Fin 6 → Fin 2, star (sixBondContraction graph (inner k) (outer k) (vertex k)
      ((faceSpin k) x) b) *
      sixBondContraction graph (inner k) (outer k) (vertex k) ((faceSpin k) x) c =
        (2 : ℂ)⁻¹ ^ 6 * (if b = c then 1 else 0) := by
  classical
  simp only [(contraction k), (faceSpin_vertex k), map_mul,
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
    star (graphStateLeg graph ((vertex k) i) ((outer k) i) (b i) s) *
      graphStateLeg graph ((vertex k) i) ((outer k) i) (c i) s)]
  simp_rw [(localGram k)]
  by_cases h : b = c
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [ite_eq_right h, mul_zero]
    rw [Finset.prod_eq_zero (i := i) (f := fun j => if b j = c j then (1 : ℂ) else 0)
      (Finset.mem_univ i) (ite_eq_right hi), mul_zero]





def faceRegion (k : Fin 4) : Finset Site := Finset.univ.image (vertex k)
abbrev Internal (k : Fin 4) := {e : Edge graph // e.1.1 ∈ (faceRegion k) ∧ e.1.2 ∈ (faceRegion k)}
abbrev Boundary (k : Fin 4) := {e : Edge graph // IsRegionBoundaryEdge (faceRegion k) e}

set_option maxRecDepth 20000

def internalIndex (k : Fin 4) (i : Fin 6) : (Internal k) :=
  ⟨(inner k) i, (by fin_cases k <;> decide : ∀ j, ((inner k) j).1.1 ∈ (faceRegion k) ∧ ((inner
      k) j).1.2 ∈ (faceRegion k)) i⟩

def boundaryIndex (k : Fin 4) (i : Fin 6) : (Boundary k) :=
  ⟨(outer k) i, (by fin_cases k <;> decide : ∀ j, IsRegionBoundaryEdge (faceRegion k) ((outer
      k) j)) i⟩

noncomputable def internalEquiv (k : Fin 4) : Fin 6 ≃ (Internal k) :=
  Equiv.ofBijective (internalIndex k) ⟨by
    exact (by fin_cases k <;> decide : ∀ i j, (internalIndex k) i = (internalIndex k) j → i = j), by
    exact (by fin_cases k <;> decide : ∀ e : (Internal k), ∃ i, (internalIndex k) i = e)⟩

noncomputable def boundaryEquiv (k : Fin 4) : Fin 6 ≃ (Boundary k) :=
  Equiv.ofBijective (boundaryIndex k) ⟨by
    exact (by fin_cases k <;> decide : ∀ i j, (boundaryIndex k) i = (boundaryIndex k) j → i = j), by
    exact (by fin_cases k <;> decide : ∀ e : (Boundary k), ∃ i, (boundaryIndex k) i = e)⟩

abbrev Incident (k : Fin 4) := {e : Edge graph // IsRegionIncidentEdge (faceRegion k) e}

def incidentIndex (k : Fin 4) : Fin 6 ⊕ Fin 6 → (Incident k)
  | .inl i => ⟨(inner k) i, Or.inl ((internalIndex k) i).2.1⟩
  | .inr i => ⟨(outer k) i, isRegionBoundaryEdge_touches _ ((boundaryIndex k) i).2⟩

noncomputable def incidentEquiv (k : Fin 4) : Fin 6 ⊕ Fin 6 ≃ (Incident k) :=
  Equiv.ofBijective (incidentIndex k) ⟨by
    exact (by fin_cases k <;> decide : ∀ i j, (incidentIndex k) i = (incidentIndex k) j → i = j), by
    exact (by fin_cases k <;> decide : ∀ e : (Incident k), ∃ i, (incidentIndex k) i = e)⟩


noncomputable def configEquiv (k : Fin 4) :
    RegionIncidentConfig (graphStatePEPS graph) (faceRegion k) ≃ Bits × Bits :=
  (Equiv.arrowCongr (incidentEquiv k).symm (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem regionMatrix_reindexed (k : Fin 4) (s : RegionPhysicalConfig (d := 2) (faceRegion k))
    (b : RegionBoundaryConfig (graphStatePEPS graph) (faceRegion k)) :
    openRegionCoefficientMatrix (graphStatePEPS graph) (faceRegion k) s b =
      ∑ x : Bits, regionIncidentWeight (graphStatePEPS graph) (faceRegion k)
        ((configEquiv k).symm (x, fun i => b ((boundaryEquiv k) i))) s := by
  classical
  unfold openRegionCoefficientMatrix openRegionWeight
  rw [← (configEquiv k).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  let t : Bits := fun i => b ((boundaryEquiv k) i)
  have readOuter (y : Bits) (i : Fin 6) :
      regionIncidentBoundaryLabel _ _ ((configEquiv k).symm (x, y)) ((boundaryEquiv k) i) = y i
      := by
    change Sum.elim x y ((incidentEquiv k).symm ((incidentEquiv k) (.inr i))) = y i
    rw [Equiv.symm_apply_apply]
    rfl
  have h (y : Bits) : regionIncidentBoundaryLabel _ _ ((configEquiv k).symm (x, y)) = b ↔
      y = t := by
    constructor
    · intro he
      exact funext fun i => (readOuter y i).symm.trans (congrFun he ((boundaryEquiv k) i))
    · intro he
      subst y
      funext e
      obtain ⟨i, rfl⟩ := (boundaryEquiv k).surjective e
      exact readOuter t i
  simp_rw [h]
  simp
  rfl





abbrev RSite (k : Fin 4) := {v : Site // v ∈ (faceRegion k)}
abbrev PairIdx (k : Fin 4) := (w : (RSite k)) × IncidentEdge graph w.1

def rowSite (k : Fin 4) (i : Fin 6) : (RSite k) := ⟨(vertex k) i, Finset.mem_image_of_mem _
      (Finset.mem_univ i)⟩

noncomputable def rowEquiv (k : Fin 4) : Fin 6 ≃ (RSite k) :=
  Equiv.ofBijective (rowSite k) ⟨fun _ _ h => (distinct_sites k) _ _ (congrArg Subtype.val h), by
    exact (by fin_cases k <;> decide : ∀ v : (RSite k), ∃ i, (rowSite k) i = v)⟩

def rolePair (k : Fin 4) : Role → (PairIdx k)
  | .inl (.inl i) =>
    ⟨⟨((inner k) i).1.1, ((internalIndex k) i).2.1⟩, ⟨(inner k) i, Or.inl rfl⟩⟩
  | .inl (.inr i) =>
    ⟨⟨((inner k) i).1.2, ((internalIndex k) i).2.2⟩, ⟨(inner k) i, Or.inr rfl⟩⟩
  | .inr i => ⟨(rowSite k) i, ⟨(outer k) i, (by fin_cases k <;> decide : ∀ j,
      ((outer k) j).1.1 = (vertex k) j ∨ ((outer k) j).1.2 = (vertex k) j) i⟩⟩

noncomputable def roleEquiv (k : Fin 4) : Role ≃ (PairIdx k) :=
  Equiv.ofBijective (rolePair k) ⟨by
    exact (by fin_cases k <;> decide : ∀ i j, (rolePair k) i = (rolePair k) j → i = j), by
    exact (by fin_cases k <;> decide : ∀ p : (PairIdx k), ∃ i, (rolePair k) i = p)⟩

private theorem readInner (k : Fin 4) (x b : Bits) (i : Fin 6) :
    (configEquiv k).symm (x,b) ((incidentEquiv k) (.inl i)) = x i := by
  change Sum.elim x b ((incidentEquiv k).symm ((incidentEquiv k) (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem readBoundary (k : Fin 4) (x b : Bits) (i : Fin 6) :
    (configEquiv k).symm (x,b) ((incidentEquiv k) (.inr i)) = b i := by
  change Sum.elim x b ((incidentEquiv k).symm ((incidentEquiv k) (.inr i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def rowConfig (k : Fin 4) (s : Bits) : RegionPhysicalConfig (d := 2) (faceRegion k) :=
  fun v => (faceSpin k) s v.1

theorem weight_regroup (k : Fin 4) (x b s : Bits) :
    regionIncidentWeight (graphStatePEPS graph) (faceRegion k) ((configEquiv k).symm (x,b))
      ((rowConfig k) s) =
      (∏ i, graphStateLeg graph ((inner k) i).1.1 ((inner k) i) (x i) ((faceSpin k) s ((inner
      k) i).1.1) *
        graphStateLeg graph ((inner k) i).1.2 ((inner k) i) (x i) ((faceSpin k) s ((inner k)
      i).1.2)) *
      ∏ i, graphStateLeg graph ((vertex k) i) ((outer k) i) (b i) ((faceSpin k) s ((vertex k)
      i)) := by
  let f (p : (PairIdx k)) := graphStateLeg graph p.1.1 p.2.1
    ((configEquiv k).symm (x,b) ⟨p.2.1, isRegionIncidentEdge_of_regionVertex _ p.1 p.2⟩)
    ((faceSpin k) s p.1.1)
  change (∏ w, ∏ e, f ⟨w,e⟩) = _
  rw [← Fintype.prod_sigma, ← (roleEquiv k).prod_comp f, Fintype.prod_sum_type,
    Fintype.prod_sum_type, Finset.prod_mul_distrib]
  change ((∏ i, graphStateLeg _ _ _ ((configEquiv k).symm (x,b) ((incidentEquiv k) (.inl i))) _) *
    (∏ i, graphStateLeg _ _ _ ((configEquiv k).symm (x,b) ((incidentEquiv k) (.inl i))) _)) *
    (∏ i, graphStateLeg _ _ _ ((configEquiv k).symm (x,b) ((incidentEquiv k) (.inr i))) _) = _
  simp_rw [(readInner k), (readBoundary k)]
  rfl

noncomputable def rows (k : Fin 4) : Bits ≃ RegionPhysicalConfig (d := 2) (faceRegion k) :=
  Equiv.arrowCongr (rowEquiv k) (Equiv.refl _)

private theorem rows_eq (k : Fin 4) (s : Bits) : (rows k) s = (rowConfig k) s := by
  funext v
  obtain ⟨i,rfl⟩ := (rowEquiv k).surjective v
  change s ((rowEquiv k).symm ((rowEquiv k) i)) = (faceSpin k) s ((vertex k) i)
  rw [Equiv.symm_apply_apply, (faceSpin_vertex k)]

noncomputable abbrev Mat (k : Fin 4) := openRegionCoefficientMatrix (graphStatePEPS graph)
      (faceRegion k)

theorem region_entry (k : Fin 4) (s : Bits) (b : RegionBoundaryConfig (graphStatePEPS graph)
      (faceRegion k)) :
    (Mat k) ((rows k) s) b = sixBondContraction graph (inner k) (outer k) (vertex k) ((faceSpin
      k) s)
      (fun i => b ((boundaryEquiv k) i)) := by
  rw [(rows_eq k)]
  apply ((regionMatrix_reindexed k) _ b).trans
  exact Finset.sum_congr rfl fun x _ => (weight_regroup k) x _ s

/-- The concrete face matrix has orthogonal columns, each of squared norm `1 / 64`. -/
theorem actual_columnGram (k : Fin 4) (b c : RegionBoundaryConfig (graphStatePEPS graph)
      (faceRegion k)) :
    ∑ s, star ((Mat k) s b) * (Mat k) s c = (2 : ℂ)⁻¹ ^ 6 * (if b = c then 1 else 0) := by
  classical
  rw [← (rows k).sum_comp]
  simp_rw [(region_entry k)]
  apply ((contraction_columnGram k) (fun i => b ((boundaryEquiv k) i)) (fun i => c
      ((boundaryEquiv k) i))).trans
  congr 2
  apply propext
  constructor
  · intro h
    funext e
    obtain ⟨i,rfl⟩ := (boundaryEquiv k).surjective e
    exact congrFun h i
  · rintro rfl
    rfl

/-- The open-region map of the checked six-site face is injective. -/
theorem actual_injective (k : Fin 4) :
    Function.Injective (openRegionMap (graphStatePEPS graph) (faceRegion k)) := by
  classical
  intro x y h
  funext b
  have extract (z : RegionBoundaryConfig (graphStatePEPS graph) (faceRegion k) → ℂ) :
      ∑ s, star ((Mat k) s b) * (openRegionMap (graphStatePEPS graph) (faceRegion k) z) s =
        z b * ((2 : ℂ)⁻¹ ^ 6) := by
    simp_rw [openRegionMap_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ c, z c * (∑ s, star ((Mat k) s b) * (Mat k) s c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        change _ * (z c * (Mat k) s c) = _
        ring
      _ = _ := by simp_rw [(actual_columnGram k)]; simp
  have he := extract x
  rw [h, extract y] at he
  exact mul_right_cancel₀ (by norm_num : (2 : ℂ)⁻¹ ^ 6 ≠ 0) he.symm



theorem injective_partition : Function.Bijective cellSite ∧
    ∀ k, Function.Injective (openRegionMap (graphStatePEPS graph) (faceRegion k)) :=
  ⟨cellPartition, actual_injective⟩

end Cell
end TNLean.PEPS.HoneycombFace
