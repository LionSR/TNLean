import TNLean.PEPS.Examples.HoneycombStripIncidence
import TNLean.PEPS.OpenRegionContraction

/-! Ordered bonds and reindexing for compatible honeycomb strip cells. -/

open ManyBody (Edge)
open TNLean.PEPS
open scoped Sym2 BigOperators

namespace HoneycombStrip
variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

def sortBond (x y : V) (h : G.Adj x y) : Edge G :=
  if p : x < y then ⟨(x, y), p, h⟩ else ⟨(y, x), lt_of_le_of_ne (le_of_not_gt p) h.ne.symm, h.symm⟩

def forgetOrder (e : Edge G) := s(e.1.1, e.1.2)

theorem sorted_pair (x y : V) (h : G.Adj x y) : forgetOrder (sortBond x y h) = s(x, y) := by
  unfold sortBond
  split
  · rfl
  · exact Sym2.eq_iff.mpr (.inr ⟨rfl, rfl⟩)

theorem ordered_unique : Function.Injective (forgetOrder (G := G)) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have he := e.2.1
    have hf := f.2.1
    rw [h.1, h.2] at he
    exact (lt_asymm he hf).elim

variable {a b : ℕ} [NeZero (2 * b)] [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)]
  [Fact (2 < 6 * a)]
abbrev Graph (a b : ℕ) [NeZero (6 * a)] [NeZero (2 * b)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] :=
  honeycombGraph (6 * a) (2 * b)

def region (k : Cell a b) := Finset.univ.image (point k)

def innerBond (k : Cell a b) (i : Fin 6) : Edge (Graph a b) :=
  sortBond _ _ ((incidence k i _).mpr (.inr (.inl rfl)))

def outerBond (k : Cell a b) (i : Fin 6) : Edge (Graph a b) :=
  sortBond _ _ ((incidence k i _).mpr (.inr (.inr rfl)))

def dart (k : Cell a b) (i : Fin 6) (r : Fin 3) : Edge (Graph a b) :=
  ![innerBond k (i - 1), innerBond k i, outerBond k i] r

private theorem dart_bij (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) (i : Fin 6) :
    ∃ f : Fin 3 ≃ IncidentEdge (Graph a b) (point k i), ∀ r, (f r).1 = dart k i r := by
  let n : Fin 3 → _ := ![point k (i - 1), point k (i + 1), embed k (extPos i)]
  have hn (r : Fin 3) : (Graph a b).Adj (point k i) (n r) := by
    apply (incidence ..).2
    fin_cases r <;> simp [n, Matrix.cons_val]
  let f (r : Fin 3) : IncidentEdge (Graph a b) (point k i) :=
    ⟨sortBond _ _ (hn r), by unfold sortBond; split <;> simp⟩
  have hf (r) : forgetOrder (f r).1 = s(point k i, n r) := sorted_pair _ _ (hn r)
  have hninj : Function.Injective n := by
    have hd : i - 1 ≠ i + 1 := (by decide : ∀ j : Fin 6, j - 1 ≠ j + 1) i
    have h1 := exteriorOffCell ha hb k i (i - 1)
    have h2 := exteriorOffCell ha hb k i (i + 1)
    intro r t h
    fin_cases r <;> fin_cases t <;> simp_all [n, Matrix.cons_val, (point_inj k).eq_iff, ne_comm]
  have inj : Function.Injective f := by
    intro r t h
    apply hninj
    have he := congrArg (fun z : IncidentEdge (Graph a b) (point k i) => forgetOrder z.1) h
    rw [hf, hf] at he
    rcases Sym2.eq_iff.mp he with q | q
    · exact q.2
    · exact q.2.trans q.1
  have surj : Function.Surjective f := by
    rintro ⟨e, he⟩
    have aux (w) (hw : (Graph a b).Adj (point k i) w)
        (hs : forgetOrder e = s(point k i, w)) : ∃ r, f r = ⟨e, he⟩ := by
      obtain ⟨r, hr⟩ : ∃ r, n r = w := by
        rcases (incidence k i w).mp hw with h | h | h
        · exact ⟨0, h.symm⟩
        · exact ⟨1, h.symm⟩
        · exact ⟨2, h.symm⟩
      exact ⟨r, Subtype.ext (ordered_unique ((hf r).trans (hr ▸ hs.symm)))⟩
    rcases he with h | h
    · apply aux e.1.2 (h ▸ e.2.2)
      simp [forgetOrder, h]
    · apply aux e.1.1 (h ▸ e.2.2.symm)
      exact Sym2.eq_iff.mpr (.inr ⟨rfl, h⟩)
  refine ⟨Equiv.ofBijective f ⟨inj, surj⟩, fun r => ordered_unique ?_⟩
  change forgetOrder (f r).1 = _
  rw [hf]
  fin_cases r <;> simp [dart, innerBond, outerBond, n, Matrix.cons_val, sorted_pair]

omit [NeZero (2 * b)] [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
private theorem inside (k : Cell a b) (i : Fin 6) : point k i ∈ region k :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

omit [NeZero (2 * b)] [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
private theorem beyond (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) (i : Fin 6) :
    embed k (extPos i) ∉ region k := by
  rintro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  exact exteriorOffCell ha hb k i j hj.symm

abbrev IsInner (k : Cell a b) (e : Edge (Graph a b)) :=
  e.1.1 ∈ region k ∧ e.1.2 ∈ region k

private theorem inner_ok (k : Cell a b) (i : Fin 6) : IsInner k (innerBond k i) := by
  unfold IsInner innerBond sortBond
  split <;> exact ⟨inside .., inside ..⟩

private theorem outer_ok (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) (i : Fin 6) :
    IsRegionBoundaryEdge (region k) (outerBond k i) := by
  unfold IsRegionBoundaryEdge outerBond sortBond
  split
  · exact .inl ⟨inside .., beyond ha hb k i⟩
  · exact .inr ⟨beyond ha hb k i, inside ..⟩

omit [Fact (2 < 6 * a)] in
private theorem separate (k : Cell a b) (e : Edge (Graph a b)) (h : IsInner k e) :
    ¬ IsRegionBoundaryEdge (region k) e := by
  rintro (h'|h')
  · exact h'.2 h.2
  · exact h'.1 h.1

private theorem cover (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) (e : Edge (Graph a b))
    (h : IsRegionIncidentEdge (region k) e) :
    (∃ i, innerBond k i = e) ∨ (∃ i, outerBond k i = e) := by
  obtain ⟨i, hi⟩ : ∃ i, e.1.1 = point k i ∨ e.1.2 = point k i := by
    rcases h with h | h <;> obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    · exact ⟨i, .inl hi.symm⟩
    · exact ⟨i, .inr hi.symm⟩
  obtain ⟨f, hf⟩ := dart_bij ha hb k i
  obtain ⟨r, hr⟩ := f.surjective ⟨e, hi⟩
  have eq := (hf r).symm.trans (congrArg Subtype.val hr)
  fin_cases r
  · exact .inl ⟨_, eq⟩
  · exact .inl ⟨_, eq⟩
  · exact .inr ⟨_, eq⟩

noncomputable def internalEquiv (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) :
    Fin 6 ≃ {e : Edge (Graph a b) // IsInner k e} :=
  Equiv.ofBijective (fun i => ⟨innerBond k i, inner_ok k i⟩) ⟨by
    intro i j h
    apply edgeIndex k
    simpa [innerBond, sorted_pair, edgeAt] using congrArg (fun z => forgetOrder z.1) h, by
    rintro ⟨e, he⟩
    rcases cover ha hb k e (.inl he.1) with ⟨i, rfl⟩|⟨i, rfl⟩
    · exact ⟨i, rfl⟩
    · exact (separate k _ he (outer_ok ha hb k i)).elim⟩

noncomputable def crossingEquiv (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) :
    Fin 6 ≃ {e : Edge (Graph a b) // IsRegionBoundaryEdge (region k) e} :=
  Equiv.ofBijective (fun i => ⟨outerBond k i, outer_ok ha hb k i⟩) ⟨by
    intro i j h
    apply cutIndex ha hb k
    simpa [outerBond, sorted_pair, cutAt] using congrArg (fun z => forgetOrder z.1) h, by
    rintro ⟨e, he⟩
    rcases cover ha hb k e (isRegionBoundaryEdge_touches _ he) with ⟨i, rfl⟩|⟨i, rfl⟩
    · exact (separate k _ (inner_ok k i) he).elim
    · exact ⟨i, rfl⟩⟩

theorem prod_reindex {M : Type*} [CommMonoid M] (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b)
    (g : ZMod (6 * a) × ZMod (2 * b) → Edge (Graph a b) → M) :
    (∏ v : {v // v ∈ region k}, ∏ e : IncidentEdge (Graph a b) v.1, g v.1 e.1) =
      ∏ i : Fin 6, ∏ r : Fin 3, g (point k i) (dart k i r) := by
  let v : Fin 6 ≃ {v // v ∈ region k} :=
    Equiv.ofBijective (fun i => ⟨point k i, inside k i⟩) ⟨fun _ _ h =>
      point_inj k (congrArg Subtype.val h), by
      rintro ⟨w, hw⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨j, rfl⟩⟩
  rw [← v.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨f, hf⟩ := dart_bij ha hb k i
  change (∏ e : IncidentEdge (Graph a b) (point k i), g _ e.1) = _
  rw [← f.prod_comp]
  simp only [hf]
  rfl

end HoneycombStrip
