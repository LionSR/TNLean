/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.GraphStateCutAlgebra

/-! # Physical and virtual coordinates of a graph-state cut -/

open scoped BigOperators
open ManyBody (Edge)

namespace TNLean.PEPS.GraphStateCut

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V) (R : Finset V)

abbrev Crossing := {e : Edge G // IsRegionBoundaryEdge R e}
abbrev Internal := {e : Edge G // e.1.1 ∈ R ∧ e.1.2 ∈ R}
abbrev Touching := {e : Edge G // IsRegionIncidentEdge R e}

/-- The unique endpoint of a crossing edge lying in the region. -/
def inside (e : Crossing G R) : R :=
  if h : e.1.1.1 ∈ R then ⟨_, h⟩ else ⟨e.1.1.2, e.2.resolve_left (fun t => h t.1) |>.2⟩

abbrev Free := {v : R // v ∉ Set.range (inside G R)}

/-- Distinct crossing edges with distinct inside endpoints supply independent physical sites. -/
noncomputable def sites (h : Function.Injective (inside G R)) :
    Crossing G R ⊕ Free G R ≃ R := by
  classical
  exact ((Equiv.ofInjective _ h).sumCongr (Equiv.refl _)).trans (Equiv.sumCompl _)

noncomputable def physicalRows (h : Function.Injective (inside G R)) :
    RegionPhysicalConfig (d := 2) R ≃ (Crossing G R → Fin 2) × (Free G R → Fin 2) :=
  (Equiv.arrowCongr (sites G R h).symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem read_crossing (h : Function.Injective (inside G R))
    (s : RegionPhysicalConfig (d := 2) R) (e : Crossing G R) :
    (physicalRows G R h s).1 e = s (inside G R e) := rfl

theorem read_free (h : Function.Injective (inside G R))
    (s : RegionPhysicalConfig (d := 2) R) (v : Free G R) :
    (physicalRows G R h s).2 v = s v.1 := rfl

def internalTouch (i : Internal G R) : Touching G R := ⟨i.1, .inl i.2.1⟩
def crossTouch (e : Crossing G R) : Touching G R := ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩

noncomputable def splitEdges : Internal G R ⊕ Crossing G R ≃ Touching G R :=
  Equiv.ofBijective (Sum.elim (internalTouch G R) (crossTouch G R)) (by
    constructor
    · intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : Touching G R => z.1) hij))
        | inr j =>
          have eq : i.1 = j.1 := congrArg (fun z : Touching G R => z.1) hij
          have hj := j.2
          have hi := i.2
          rw [eq] at hi
          exact False.elim (hj.elim (fun q => q.2 hi.2) (fun q => q.1 hi.1))
      | inr i =>
        cases j with
        | inr j => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : Touching G R => z.1) hij))
        | inl j =>
          have eq : i.1 = j.1 := congrArg (fun z : Touching G R => z.1) hij
          have hi := i.2
          have hj := j.2
          rw [eq] at hi
          exact False.elim (hi.elim (fun q => q.2 hj.2) (fun q => q.1 hj.1))
    · rintro ⟨e, he⟩
      by_cases h : e.1.1 ∈ R ∧ e.1.2 ∈ R
      · exact ⟨.inl ⟨e,h⟩, rfl⟩
      · exact ⟨.inr ⟨e,he.isRegionBoundaryEdge h⟩, rfl⟩)

variable [Fintype V] [DecidableRel G.Adj]

noncomputable def assignments : RegionIncidentConfig (graphStatePEPS G) R ≃
    (Internal G R → Fin 2) × (Crossing G R → Fin 2) :=
  (Equiv.arrowCongr (splitEdges G R).symm (Equiv.refl (Fin 2))).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem matrix_internal_sum (s : RegionPhysicalConfig (d := 2) R)
    (u : Crossing G R → Fin 2) :
    openRegionCoefficientMatrix (graphStatePEPS G) R s u =
      ∑ x : Internal G R → Fin 2, regionIncidentWeight (graphStatePEPS G) R
        ((assignments G R).symm (x,u)) s := by
  classical
  unfold openRegionCoefficientMatrix openRegionWeight
  rw [← (assignments G R).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have read (y : Crossing G R → Fin 2) : regionIncidentBoundaryLabel _ _
      ((assignments G R).symm (x,y)) = (y : RegionBoundaryConfig (graphStatePEPS G) R) := by
    funext e
    change Sum.elim x y ((splitEdges G R).symm (splitEdges G R (.inr e))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have test (y : Crossing G R → Fin 2) : regionIncidentBoundaryLabel _ _ ((assignments G R).symm (x,y)) = u ↔ y = u := by
    rw [read]
    rfl
  simp_rw [test]
  simp

abbrev Dart := (v : R) × IncidentEdge G v.1

private def leftDart (i : Internal G R) : Dart G R :=
  ⟨⟨_, i.2.1⟩, ⟨i.1, Or.inl rfl⟩⟩

private def rightDart (i : Internal G R) : Dart G R :=
  ⟨⟨_, i.2.2⟩, ⟨i.1, Or.inr rfl⟩⟩

private def crossDart (e : Crossing G R) : Dart G R :=
  ⟨inside G R e, ⟨e.1, by unfold inside; split <;> simp⟩⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem dart_ext {a b : Dart G R} (hv : a.1.1 = b.1.1) (he : a.2.1 = b.2.1) :
    a = b := by
  obtain ⟨v,e⟩ := a
  obtain ⟨w,f⟩ := b
  obtain rfl : v = w := Subtype.ext hv
  obtain rfl : e = f := Subtype.ext he
  rfl

private def dartMap : (Internal G R ⊕ Internal G R) ⊕ Crossing G R → Dart G R :=
  Sum.elim (Sum.elim (leftDart G R) (rightDart G R)) (crossDart G R)

private def dartIndex (d : Dart G R) : (Internal G R ⊕ Internal G R) ⊕ Crossing G R :=
  if h : d.2.1.1.1 ∈ R ∧ d.2.1.1.2 ∈ R then
    if d.2.1.1.1 = d.1.1 then .inl (.inl ⟨_, h⟩) else .inl (.inr ⟨_, h⟩)
  else .inr ⟨_, (isRegionIncidentEdge_of_regionVertex R d.1 d.2).isRegionBoundaryEdge h⟩

private def darts : (Internal G R ⊕ Internal G R) ⊕ Crossing G R ≃ Dart G R where
  toFun := dartMap G R
  invFun := dartIndex G R
  left_inv := by
    rintro ((i|i)|e)
    · simp [dartMap, dartIndex, leftDart, i.2]
    · simp [dartMap, dartIndex, rightDart, i.2, i.1.2.1.ne]
    · have hn : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) :=
        fun q => e.2.elim (fun p => p.2 q.2) (fun p => p.1 q.1)
      simp [dartMap, dartIndex, crossDart, hn]
  right_inv d := by
    unfold dartIndex
    split
    · split
      · apply dart_ext G R
        · assumption
        · rfl
      · apply dart_ext G R
        · exact d.2.2.resolve_left (by assumption)
        · rfl
    · apply dart_ext G R
      · change ((inside G R _).1) = _
        unfold inside
        split
        · exact d.2.2.resolve_right (by intro eq; grind)
        · exact d.2.2.resolve_left (by intro eq; grind)
      · rfl

/-- Regroup all vertex legs into two factors per internal edge and one per crossing. -/
theorem weight_edges (x : Internal G R → Fin 2) (u : Crossing G R → Fin 2)
    (s : V → Fin 2) :
    regionIncidentWeight (graphStatePEPS G) R ((assignments G R).symm (x,u)) (fun v => s v.1) =
      (∏ i : Internal G R, graphStateLeg G i.1.1.1 i.1 (x i) (s i.1.1.1) *
        graphStateLeg G i.1.1.2 i.1 (x i) (s i.1.1.2)) *
      ∏ e : Crossing G R, graphStateLeg G (inside G R e).1 e.1 (u e) (s (inside G R e).1) := by
  classical
  let weight (d : Dart G R) := graphStateLeg G d.1.1 d.2.1
    (((assignments G R).symm (x,u)) ⟨_, isRegionIncidentEdge_of_regionVertex R d.1 d.2⟩) (s d.1.1)
  change (∏ v, ∏ e, weight ⟨v,e⟩) = _
  rw [← Fintype.prod_sigma, ← (darts G R).prod_comp weight, Fintype.prod_sum_type,
    Fintype.prod_sum_type, Finset.prod_mul_distrib]
  have readI (i : Internal G R) : ((assignments G R).symm (x,u)) (internalTouch G R i) = x i := by
    change Sum.elim x u ((splitEdges G R).symm (splitEdges G R (.inl i))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have readB (e : Crossing G R) : ((assignments G R).symm (x,u)) (crossTouch G R e) = u e := by
    change Sum.elim x u ((splitEdges G R).symm (splitEdges G R (.inr e))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hl (i : Internal G R) : weight (darts G R (.inl (.inl i))) =
      graphStateLeg G i.1.1.1 i.1 (x i) (s i.1.1.1) :=
    congrArg (fun t => graphStateLeg G i.1.1.1 i.1 t (s i.1.1.1)) (readI i)
  have hr (i : Internal G R) : weight (darts G R (.inl (.inr i))) =
      graphStateLeg G i.1.1.2 i.1 (x i) (s i.1.1.2) :=
    congrArg (fun t => graphStateLeg G i.1.1.2 i.1 t (s i.1.1.2)) (readI i)
  have hb (e : Crossing G R) : weight (darts G R (.inr e)) =
      graphStateLeg G (inside G R e).1 e.1 (u e) (s (inside G R e).1) :=
    congrArg (fun t => graphStateLeg G (inside G R e).1 e.1 t (s (inside G R e).1)) (readB e)
  simp_rw [hl, hr, hb]

theorem matrix_entry (s : V → Fin 2) (u : Crossing G R → Fin 2) :
    openRegionCoefficientMatrix (graphStatePEPS G) R (fun v => s v.1) u =
      entry G (fun i : Internal G R => i.1) (fun e : Crossing G R => e.1)
        (fun e => (inside G R e).1) s (fun e => s (inside G R e).1) u := by
  classical
  rw [matrix_internal_sum]
  exact Finset.sum_congr rfl (fun x _ => weight_edges G R x u s)

private noncomputable def extendRow (s : RegionPhysicalConfig (d := 2) R) (v : V) : Fin 2 :=
  if h : v ∈ R then s ⟨v,h⟩ else 0

noncomputable abbrev cutMatrix := openRegionCoefficientMatrix (graphStatePEPS G) R

open scoped Classical in
theorem cutGram (h : Function.Injective (inside G R)) (u v : RegionBoundaryConfig (graphStatePEPS G) R) :
    ∑ s, star (cutMatrix G R s u) * cutMatrix G R s v =
      (2 : ℂ) ^ Fintype.card (Free G R) * (2 : ℂ)⁻¹ ^ Fintype.card (Internal G R) *
      (if u = v then 1 else 0) := by
  classical
  let rows := physicalRows G R h
  let spin (y : Free G R → Fin 2) (x : Crossing G R → Fin 2) := extendRow R (rows.symm (x,y))
  have eval (y x) (w : RegionBoundaryConfig (graphStatePEPS G) R) :
      cutMatrix G R (rows.symm (x,y)) w =
        entry G (fun i : Internal G R => i.1) (fun e : Crossing G R => e.1)
          (fun e => (inside G R e).1) (spin y x) x w := by
    have extR (z : R) : spin y x z.1 = rows.symm (x,y) z := by simp [spin, extendRow, z.2]
    have read (e : Crossing G R) : spin y x (inside G R e).1 = x e := by
      rw [extR]
      exact congrFun (congrArg Prod.fst (rows.apply_symm_apply (x,y))) e
    simpa only [read, extR] using matrix_entry G R (spin y x) w
  rw [← rows.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [eval]
  exact columnGram G _ _ _ spin u v

open scoped Classical in
theorem openRegionMap_injective (h : Function.Injective (inside G R)) :
    Function.Injective (openRegionMap (graphStatePEPS G) R) := by
  classical
  intro x y eq
  funext u
  let c := (2 : ℂ) ^ Fintype.card (Free G R) * (2 : ℂ)⁻¹ ^ Fintype.card (Internal G R)
  have extract (z : RegionBoundaryConfig (graphStatePEPS G) R → ℂ) :
      ∑ s, star (cutMatrix G R s u) * (openRegionMap (graphStatePEPS G) R z) s = z u * c := by
    simp_rw [openRegionMap_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ v, z v * (∑ s, star (cutMatrix G R s u) * cutMatrix G R s v) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        change _ * (z v * cutMatrix G R s v) = _
        ring
      _ = _ := by
        simp_rw [cutGram G R h]
        simp [c]
  have ex := extract x
  rw [eq, extract y] at ex
  exact mul_right_cancel₀ (by dsimp [c]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)) : c ≠ 0) ex.symm

end TNLean.PEPS.GraphStateCut
