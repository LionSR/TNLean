import TNLean.PEPS.Examples.HoneycombStripEdges
import TNLean.PEPS.Examples.HoneycombPlaquetteInjectivity

/-! Open - region contraction on compatible strip cells. -/
open ManyBody (Edge)
open TNLean.PEPS
open scoped BigOperators
namespace HoneycombStrip
variable {a b : ℕ} [NeZero (2 * b)] [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)]
  [Fact (2 < 6 * a)] (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b)
abbrev Bits := Fin 6 → Fin 2
abbrev Inc := {e : Edge (Graph a b) // IsRegionIncidentEdge (region k) e}
noncomputable def incident : Fin 6 ⊕ Fin 6 ≃ Inc k := by
  let f : Fin 6 ⊕ Fin 6 → Inc k := Sum.elim
    (fun i => ⟨(internalEquiv ha hb k i).1, Or.inl (internalEquiv ha hb k i).2.1⟩)
    (fun i => ⟨(crossingEquiv ha hb k i).1, isRegionBoundaryEdge_touches _ (crossingEquiv ha hb
      k i).2⟩)
  apply Equiv.ofBijective f
  constructor
  · rintro (i | i) (j | j) h
    · exact congrArg Sum.inl ((internalEquiv ha hb k).injective (Subtype.ext (congrArg (fun z :
      Inc k => z.1) h)))
    · have he := (internalEquiv ha hb k i).2
      have hc := (crossingEquiv ha hb k j).2
      have eq : (internalEquiv ha hb k i).1 = (crossingEquiv ha hb k j).1 := congrArg Subtype.val h
      rw [← eq] at hc
      rcases hc with h'|h' <;> simp_all [IsInner]
    · have he := (internalEquiv ha hb k j).2
      have hc := (crossingEquiv ha hb k i).2
      have eq : (crossingEquiv ha hb k i).1 = (internalEquiv ha hb k j).1 := congrArg Subtype.val h
      rw [eq] at hc
      rcases hc with h'|h' <;> simp_all [IsInner]
    · exact congrArg Sum.inr ((crossingEquiv ha hb k).injective (Subtype.ext (congrArg (fun z :
      Inc k => z.1) h)))
  · rintro ⟨e, he⟩
    by_cases hi : IsInner k e
    · obtain ⟨i, eq⟩ := (internalEquiv ha hb k).surjective ⟨e, hi⟩
      exact ⟨.inl i, Subtype.ext (congrArg (fun z : {e : Edge (Graph a b) // IsInner k e} =>
        z.1) eq)⟩
    · obtain ⟨i, eq⟩ := (crossingEquiv ha hb k).surjective ⟨e, he.isRegionBoundaryEdge hi⟩
      exact ⟨.inr i, Subtype.ext (congrArg (fun z : {e : Edge (Graph a b) //
        IsRegionBoundaryEdge (region k) e} => z.1) eq)⟩

noncomputable def assign :
    RegionIncidentConfig (graphStatePEPS (Graph a b)) (region k) ≃ Bits × Bits :=
  (Equiv.arrowCongr (incident ha hb k).symm (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem matrix_sum (s : RegionPhysicalConfig (d := 2) (region k))
    (mu : RegionBoundaryConfig (graphStatePEPS (Graph a b)) (region k)) :
    openRegionCoefficientMatrix (graphStatePEPS (Graph a b)) (region k) s mu =
      ∑ x : Bits, regionIncidentWeight (graphStatePEPS (Graph a b)) (region k)
        ((assign ha hb k).symm (x, fun i => mu ((crossingEquiv ha hb k) i))) s := by
  classical
  unfold openRegionCoefficientMatrix openRegionWeight
  rw [← (assign ha hb k).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  let t : Bits := fun i => mu ((crossingEquiv ha hb k) i)
  have readOuter (y : Bits) (i : Fin 6) :
      regionIncidentBoundaryLabel _ _ ((assign ha hb k).symm (x, y)) ((crossingEquiv ha hb k)
        i) = y i := by
    change Sum.elim x y ((incident ha hb k).symm ((incident ha hb k) (.inr i))) = y i
    rw [Equiv.symm_apply_apply]
    rfl
  have h (y : Bits) : regionIncidentBoundaryLabel _ _ ((assign ha hb k).symm (x, y)) = mu ↔
      y = t := by
    constructor
    · intro he
      exact funext fun i => (readOuter y i).symm.trans (congrFun he ((crossingEquiv ha hb k) i))
    · intro he
      subst y
      funext e
      obtain ⟨i, rfl⟩ := (crossingEquiv ha hb k).surjective e
      exact readOuter t i
  simp_rw [h]
  simp
  rfl

private noncomputable def label (x y : Bits) (e : Edge (Graph a b)) : Fin 2 := by
  classical
  exact if h : IsRegionIncidentEdge (region k) e then ((assign ha hb k).symm (x, y) : Inc k →
    Fin 2) ⟨e, h⟩ else 0

private theorem labIn (x y : Bits) (i : Fin 6) :
    label ha hb k x y (innerBond k i) = x i := by
  have h := (incident ha hb k (.inl i)).2
  unfold label
  apply (dite_eq_left (α := Fin 2) (show IsRegionIncidentEdge (region k) (innerBond k i) from
    h)).trans
  change Sum.elim x y ((incident ha hb k).symm (incident ha hb k (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem labOut (x y : Bits) (i : Fin 6) :
    label ha hb k x y (outerBond k i) = y i := by
  have h := (incident ha hb k (.inr i)).2
  unfold label
  apply (dite_eq_left (α := Fin 2) (show IsRegionIncidentEdge (region k) (outerBond k i) from
    h)).trans
  change Sum.elim x y ((incident ha hb k).symm (incident ha hb k (.inr i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem weight_product (x y : Bits) (s : ZMod (6 * a) × ZMod (2 * b) → Fin 2) :
    regionIncidentWeight (graphStatePEPS (Graph a b)) (region k)
      ((assign ha hb k).symm (x, y)) (fun v => s v.1) =
      (∏ i, graphStateLeg _ (point k i) (innerBond k i) (x i) (s (point k i)) *
        graphStateLeg _ (point k (i + 1)) (innerBond k i) (x i) (s (point k (i + 1)))) *
      ∏ i, graphStateLeg _ (point k i) (outerBond k i) (y i) (s (point k i)) := by
  classical
  let g v e := graphStateLeg (Graph a b) v e (label ha hb k x y e) (s v)
  calc
    _ = ∏ v : {v // v ∈ region k}, ∏ e : IncidentEdge (Graph a b) v.1, g v.1 e.1 := by
      unfold regionIncidentWeight
      apply Finset.prod_congr rfl
      intro v _
      apply Finset.prod_congr rfl
      intro e _
      simp [g, label, isRegionIncidentEdge_of_regionVertex (region k) v e, graphStatePEPS]
    _ = _ := by
      rw [prod_reindex ha hb]
      have d0 (i : Fin 6) : dart k i 0 = innerBond k (i - 1) := rfl
      have d1 (i : Fin 6) : dart k i 1 = innerBond k i := rfl
      have d2 (i : Fin 6) : dart k i 2 = outerBond k i := rfl
      simp only [Fin.prod_univ_three, d0, d1, d2,
        Finset.prod_mul_distrib]
      have shift : (∏ i : Fin 6, g (point k i) (innerBond k (i - 1))) =
          ∏ i : Fin 6, g (point k (i + 1)) (innerBond k i) := by
        simpa using (Equiv.prod_comp (Equiv.addRight (1 : Fin 6))
          (fun i => g (point k i) (innerBond k (i - 1)))).symm
      simp only [g] at shift ⊢
      simp only [labIn, labOut] at shift ⊢
      rw [shift]
      ring

noncomputable def sites : Fin 6 ≃ {v // v ∈ region k} :=
  Equiv.ofBijective (fun i => ⟨point k i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    ⟨fun _ _ h => point_inj k (congrArg Subtype.val h), by
      rintro ⟨w, hw⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨j, rfl⟩⟩

noncomputable def rows : Bits ≃ RegionPhysicalConfig (d := 2) (region k) :=
  Equiv.arrowCongr (sites k) (Equiv.refl _)

noncomputable def spin (z : Bits) (v : ZMod (6 * a) × ZMod (2 * b)) : Fin 2 := by
  classical
  exact if h : v ∈ region k then rows k z ⟨v, h⟩ else 0

omit [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
private theorem spin_site (z : Bits) (i : Fin 6) : spin k z (point k i) = z i := by
  have h := (sites k i).2
  unfold spin
  rw [dite_eq_left (show point k i ∈ region k from h)]
  change z ((sites k).symm (sites k i)) = _
  rw [Equiv.symm_apply_apply]

noncomputable abbrev mat := openRegionCoefficientMatrix (graphStatePEPS (Graph a b)) (region k)

theorem entry (z : Bits) (mu : RegionBoundaryConfig (graphStatePEPS (Graph a b)) (region k)) :
    mat k (rows k z) mu = sixBondContraction (Graph a b) (innerBond k) (outerBond k)
      (point k) (spin k z) (fun i => mu (crossingEquiv ha hb k i)) := by
  apply (matrix_sum ha hb k _ mu).trans
  apply Finset.sum_congr rfl
  intro x _
  let y : Bits := fun i => mu (crossingEquiv ha hb k i)
  have hr : rows k z = fun v => spin k z v.1 := by
    funext v
    simp [spin, v.2]
  rw [hr]
  apply (weight_product ha hb k x y (spin k z)).trans
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  unfold innerBond sortBond
  split
  · rfl
  · exact mul_comm _ _

private theorem localGram (i : Fin 6) (u v : Fin 2) :
    ∑ t : Fin 2, star (graphStateLeg _ (point k i) (outerBond k i) u t) *
      graphStateLeg _ (point k i) (outerBond k i) v t = if u = v then 1 else 0 := by
  unfold graphStateLeg
  split
  · exact hadamardEntry_columnGram u v
  · fin_cases u <;> fin_cases v <;> norm_num [Fin.sum_univ_two]

private theorem internalGram (u v : Fin 2) :
    star (hadamardEntry u v) * hadamardEntry u v = (2 : ℂ)⁻¹ := by
  fin_cases u <;> fin_cases v <;> norm_num [hadamardEntry, Complex.invSqrtTwo_mul_self]

theorem contractionGram (u v : Fin 6 → Fin 2) :
    ∑ x : Fin 6 → Fin 2, star (sixBondContraction (Graph a b) (innerBond k) (outerBond k)
      (point k) (spin k x) u) *
      sixBondContraction (Graph a b) (innerBond k) (outerBond k) (point k) (spin k x) v =
        (2 : ℂ)⁻¹ ^ 6 * (if u = v then 1 else 0) := by
  classical
  simp only [sixBondContraction_factor, spin_site, map_mul,
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
    star (graphStateLeg (Graph a b) (point k i) (outerBond k i) (u i) s) *
      graphStateLeg (Graph a b) (point k i) (outerBond k i) (v i) s)]
  simp_rw [localGram]
  by_cases h : u = v
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [ite_eq_right h, mul_zero]
    rw [Finset.prod_eq_zero (i := i) (f := fun j => if u j = v j then (1 : ℂ) else 0)
      (Finset.mem_univ i) (ite_eq_right hi), mul_zero]

include ha hb
theorem actual_columnGram (mu nu : RegionBoundaryConfig (graphStatePEPS (Graph a b)) (region k)) :
    ∑ s, star (mat k s mu) * mat k s nu = (2 : ℂ)⁻¹ ^ 6 * (if mu = nu then 1 else 0) := by
  classical
  rw [← (rows k).sum_comp]
  simp_rw [entry ha hb k]
  apply (contractionGram k (fun i => mu (crossingEquiv ha hb k i)) (fun i => nu (crossingEquiv
    ha hb k i))).trans
  congr 2
  apply propext
  constructor
  · intro h
    funext e
    obtain ⟨i, rfl⟩ := (crossingEquiv ha hb k).surjective e
    exact congrFun h i
  · rintro rfl
    rfl

theorem actual_injective :
    Function.Injective (openRegionMap (graphStatePEPS (Graph a b)) (region k)) := by
  classical
  intro x y h
  funext mu
  have extract (z : RegionBoundaryConfig (graphStatePEPS (Graph a b)) (region k) → ℂ) :
      ∑ s, star (mat k s mu) * (openRegionMap (graphStatePEPS (Graph a b)) (region k) z) s =
        z mu * ((2 : ℂ)⁻¹ ^ 6) := by
    simp_rw [openRegionMap_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ c, z c * (∑ s, star (mat k s mu) * mat k s c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        change _ * (z c * mat k s c) = _
        ring
      _ = _ := by simp_rw [actual_columnGram ha hb k]; simp
  have he := extract x
  rw [h, extract y] at he
  exact mul_right_cancel₀ (by norm_num : (2 : ℂ)⁻¹ ^ 6 ≠ 0) he.symm


/-- Every site belongs to exactly one staggered cell, and every cell's open - region map
is injective. -/
theorem injective_cover :
    (∀ v : ZMod (6 * a) × ZMod (2 * b), ∃! c : Cell a b, v ∈ region c) ∧
      ∀ c : Cell a b, Function.Injective (openRegionMap (graphStatePEPS (Graph a b))
        (region c)) := by
  constructor
  · intro v
    let p := partition.symm (⟨v.1.val, ZMod.val_lt v.1⟩, ⟨v.2.val, ZMod.val_lt v.2⟩)
    obtain ⟨i, hi⟩ : ∃ i, off i = p.2 :=
      (by decide : ∀ t : Offset, ∃ i, off i = t) p.2
    have matchPoint (c : Cell a b) (j : Fin 6) :
        point c j = v ↔ (c, off j) = p := by
      have he := point_val c j
      have hp := partition.apply_symm_apply
        (⟨v.1.val, ZMod.val_lt v.1⟩, ⟨v.2.val, ZMod.val_lt v.2⟩)
      constructor
      · intro h
        apply partition.injective
        rw [hp]
        apply Prod.ext <;> apply Fin.ext
        · exact congrArg Prod.fst (he.symm.trans (by rw [h]))
        · exact congrArg Prod.snd (he.symm.trans (by rw [h]))
      · intro h
        rw [h, hp] at he
        exact Prod.ext (ZMod.val_injective _ (congrArg Prod.fst he))
          (ZMod.val_injective _ (congrArg Prod.snd he))
    refine ⟨p.1, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (matchPoint _ _).2 ?_⟩, ?_⟩
    · exact Prod.ext rfl hi
    · intro c hc
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      exact congrArg Prod.fst ((matchPoint _ _).1 hj)
  · exact fun c => actual_injective ha hb c

end HoneycombStrip
