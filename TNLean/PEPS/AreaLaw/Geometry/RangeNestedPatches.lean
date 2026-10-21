/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.NestedPatches

/-!
# Nested square patches for interactions of range `R`

The polynomial-PEPS manuscript selects the nested radii `u + 2 j` for nearest-neighbour
interactions. For interactions of range `R` we space the radii by
`s_R = 2 ⌈R / 2⌉`, which is `2` for `1 ≤ R ≤ 2` and lies between `R` and `R + 1`.

The sup-norm distance from the center changes by at most one along an edge, so the
sites of a support of graph range `R` have radial distances in an interval of length `R`.
A selected square splits such a support only when its radius lies in that interval, and
two selected radii are at least `s_R ≥ R` apart. Hence each support of range `R` is split
by at most one selected square. A split support contains a site in the layer
`r - R < ‖x - c‖∞ ≤ r` of the splitting square, and this layer has at most
`R (8 r + 4)` sites. With `m = ⌊u / s_R⌋ + 1` equal weights `κ / m`, the resulting
coefficient `R (16 u + 4) m (κ / m)²` is at most `18 s_R R κ²`.

At `R = 1` the selected family is the source family of `NestedPatches`.

**Extension beyond the source:** the source treats nearest-neighbour interactions only;
the range-`R` spacing, the single-split statement for range-`R` supports and the layer
count are not in the source.

These are geometry and scalar arithmetic statements: no Hamiltonian, filter or state is
involved.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `03-patches.tex`, lines 53–66, 213–228, 323–336, read with
  interactions of range `R`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

open scoped BigOperators

/-- The radius spacing `s_R = 2 ⌈R / 2⌉` for interactions of range `R`. -/
def rangePatchSpacing (R : ℕ) : ℕ := 2 * ((R + 1) / 2)

/-- The spacing is at least the range. -/
theorem le_rangePatchSpacing (R : ℕ) : R ≤ rangePatchSpacing R := by
  unfold rangePatchSpacing
  omega

/-- The spacing exceeds the range by at most one. -/
theorem rangePatchSpacing_le (R : ℕ) : rangePatchSpacing R ≤ R + 1 := by
  unfold rangePatchSpacing
  omega

/-- For a positive range the spacing is at least two. -/
theorem two_le_rangePatchSpacing {R : ℕ} (hR : 1 ≤ R) : 2 ≤ rangePatchSpacing R := by
  unfold rangePatchSpacing
  omega

/-- The nearest-neighbour spacing is the source spacing two. -/
@[simp] theorem rangePatchSpacing_one : rangePatchSpacing 1 = 2 := rfl

/-- The number `⌊u / s_R⌋ + 1` of nested patches at range `R`. -/
noncomputable def rangeNestedPatchCount (R : ℕ) (u : ℝ) : ℕ :=
  ⌊u / rangePatchSpacing R⌋₊ + 1

/-- The zero-based selected radius `u + s_R j` at range `R`. -/
def rangeNestedPatchRadius (R : ℕ) (u : ℝ) (j : ℕ) : ℝ := u + rangePatchSpacing R * j

/-- The sampled patch at the selected radius at range `R`. -/
noncomputable def rangeNestedPatch (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (R : ℕ) (u : ℝ)
    (j : ℕ) : Finset (Site Λ) :=
  closedSquareSample Λ c (rangeNestedPatchRadius R u j)

/-- At range one the patch count is the source count. -/
@[simp] theorem rangeNestedPatchCount_one (u : ℝ) :
    rangeNestedPatchCount 1 u = nestedPatchCount u := by
  simp [rangeNestedPatchCount, nestedPatchCount]

/-- At range one the selected radii are the source radii. -/
@[simp] theorem rangeNestedPatchRadius_one (u : ℝ) (j : ℕ) :
    rangeNestedPatchRadius 1 u j = nestedPatchRadius u j := by
  simp [rangeNestedPatchRadius, nestedPatchRadius]

/-- At range one the selected patches are the source patches. -/
@[simp] theorem rangeNestedPatch_one (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (u : ℝ) (j : ℕ) :
    rangeNestedPatch Λ c 1 u j = nestedPatch Λ c u j := by
  simp [rangeNestedPatch, nestedPatch]

/-- There is at least one selected radius. -/
theorem rangeNestedPatchCount_pos (R : ℕ) (u : ℝ) : 0 < rangeNestedPatchCount R u :=
  Nat.succ_pos _

/-- The count exceeds `u / s_R`. -/
theorem div_lt_rangeNestedPatchCount (R : ℕ) (u : ℝ) :
    u / rangePatchSpacing R < (rangeNestedPatchCount R u : ℝ) := by
  simpa [rangeNestedPatchCount] using Nat.lt_floor_add_one (u / rangePatchSpacing R)

/-- Each selected radius is at least the base radius. -/
theorem le_rangeNestedPatchRadius (R : ℕ) (u : ℝ) (j : ℕ) :
    u ≤ rangeNestedPatchRadius R u j := by
  unfold rangeNestedPatchRadius
  exact le_add_of_nonneg_right (by positivity)

/-- Every selected radius is at most twice the base radius. -/
theorem rangeNestedPatchRadius_le_two_mul {R : ℕ} {u : ℝ} (hu : 0 ≤ u) {j : ℕ}
    (hj : j < rangeNestedPatchCount R u) : rangeNestedPatchRadius R u j ≤ 2 * u := by
  unfold rangeNestedPatchRadius
  have hj' : (j : ℝ) ≤ (⌊u / rangePatchSpacing R⌋₊ : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp hj
  rcases (Nat.zero_le (rangePatchSpacing R)).eq_or_lt with hs | hs
  · rw [← hs]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    linarith
  · have hs' : (0 : ℝ) < rangePatchSpacing R := by exact_mod_cast hs
    have hf := Nat.floor_le (div_nonneg hu hs'.le)
    have h : (rangePatchSpacing R : ℝ) * j ≤ u := by
      calc
        _ ≤ (rangePatchSpacing R : ℝ) * (u / rangePatchSpacing R) :=
          mul_le_mul_of_nonneg_left (hj'.trans hf) hs'.le
        _ = u := mul_div_cancel₀ u hs'.ne'
    linarith

/-- Distinct selected radii are at least `s_R` apart. -/
theorem rangeNestedPatchRadius_add_spacing_le {R : ℕ} {u : ℝ} {i j : ℕ} (hij : i < j) :
    rangeNestedPatchRadius R u i + rangePatchSpacing R ≤ rangeNestedPatchRadius R u j := by
  have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  have hs : (0 : ℝ) ≤ rangePatchSpacing R := Nat.cast_nonneg _
  unfold rangeNestedPatchRadius
  nlinarith

/-- Selected patches are nested, even when clipping makes some of them equal. -/
theorem rangeNestedPatch_mono (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (R : ℕ) (u : ℝ)
    {i j : ℕ} (hij : i ≤ j) : rangeNestedPatch Λ c R u i ⊆ rangeNestedPatch Λ c R u j := by
  apply closedSquareSample_mono
  unfold rangeNestedPatchRadius
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hs : (0 : ℝ) ≤ rangePatchSpacing R := Nat.cast_nonneg _
  nlinarith

/-- Radial distances of the endpoints of a walk differ by at most its length.
Source: polynomial-PEPS `03-patches.tex`, lines 215–217, iterated along a walk. -/
theorem abs_squareRadius_sub_le_length {Λ : Finset (ℤ × ℤ)} (c : ℝ × ℝ) {x y : Site Λ}
    (p : (domainGraph Λ).Walk x y) :
    |squareRadius c x.1 - squareRadius c y.1| ≤ p.length := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ |squareRadius c _ - squareRadius c _| + |squareRadius c _ - squareRadius c _| :=
          abs_sub_le _ _ _
        _ ≤ 1 + _ := add_le_add (abs_squareRadius_sub_le_one_of_adj hadj) ih
        _ = _ := add_comm _ _

/-- Radial distances within a support of graph range `R` differ by at most `R`. -/
theorem abs_squareRadius_sub_le_of_isAdmissibleSupport {Λ : Finset (ℤ × ℤ)} (c : ℝ × ℝ)
    {R : ℕ} {X : Finset (Site Λ)} (hX : IsAdmissibleSupport Λ R X) {x y : Site Λ}
    (hx : x ∈ X) (hy : y ∈ X) : |squareRadius c x.1 - squareRadius c y.1| ≤ R := by
  obtain ⟨p, hp⟩ := hX.2 x hx y hy
  exact (abs_squareRadius_sub_le_length c p).trans (by exact_mod_cast hp)

/-- A support whose radial distances differ by at most `R` is split by at most one
selected square: it cannot both meet a smaller square and leave a larger one. -/
theorem rangeNestedPatch_split_unique {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ} {R : ℕ} {u : ℝ}
    {X : Finset (Site Λ)}
    (hX : ∀ x ∈ X, ∀ y ∈ X, |squareRadius c x.1 - squareRadius c y.1| ≤ R) {i j : ℕ}
    (hi : (∃ v ∈ X, v ∈ rangeNestedPatch Λ c R u i) ∧
      ∃ v ∈ X, v ∉ rangeNestedPatch Λ c R u i)
    (hj : (∃ v ∈ X, v ∈ rangeNestedPatch Λ c R u j) ∧
      ∃ v ∈ X, v ∉ rangeNestedPatch Λ c R u j) : i = j := by
  wlog hij : i < j generalizing i j
  · rcases lt_trichotomy i j with h | h | h
    · exact this hi hj h
    · exact h
    · exact (this hj hi h).symm
  obtain ⟨z, hzX, hz⟩ := hi.1
  obtain ⟨y, hyX, hy⟩ := hj.2
  rw [rangeNestedPatch, mem_closedSquareSample_iff_radius] at hz hy
  have hgap := rangeNestedPatchRadius_add_spacing_le (R := R) (u := u) hij
  have hR : (R : ℝ) ≤ rangePatchSpacing R := by exact_mod_cast le_rangePatchSpacing R
  have hzy := (abs_le.mp (hX y hyX z hzX)).2
  linarith

/-- The sites with `r - R < ‖x - c‖∞ ≤ r`, the inner layer of width `R` of a closed
square. -/
noncomputable def squareLayer (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (r : ℝ) (R : ℕ) :
    Finset (Site Λ) := by
  classical
  exact Finset.univ.filter fun x ↦ r - R < squareRadius c x.1 ∧ squareRadius c x.1 ≤ r

@[simp] theorem mem_squareLayer {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ} {r : ℝ} {R : ℕ}
    {x : Site Λ} :
    x ∈ squareLayer Λ c r R ↔ r - R < squareRadius c x.1 ∧ squareRadius c x.1 ≤ r := by
  classical
  simp [squareLayer]

/-- A support with radial spread at most `R` that meets a closed square and leaves it has
each of its sites inside the square in the inner layer of width `R`. -/
theorem mem_squareLayer_of_split {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ} {r : ℝ} {R : ℕ}
    {X : Finset (Site Λ)}
    (hX : ∀ x ∈ X, ∀ y ∈ X, |squareRadius c x.1 - squareRadius c y.1| ≤ R)
    {x y : Site Λ} (hxX : x ∈ X) (hx : x ∈ closedSquareSample Λ c r) (hyX : y ∈ X)
    (hy : y ∉ closedSquareSample Λ c r) : x ∈ squareLayer Λ c r R := by
  rw [mem_closedSquareSample_iff_radius] at hx hy
  have hxy := (abs_le.mp (hX y hyX x hxX)).2
  exact mem_squareLayer.mpr ⟨by linarith, hx⟩

private theorem card_Ioc_floor_sub_le (a : ℝ) (R : ℕ) :
    (Finset.Ioc ⌊a - R⌋ ⌊a⌋).card ≤ R := by
  rw [Int.card_Ioc, Int.floor_sub_natCast]
  omega

private theorem card_Ico_ceil_add_le (a : ℝ) (R : ℕ) :
    (Finset.Ico ⌈a⌉ ⌈a + R⌉).card ≤ R := by
  rw [Int.card_Ico, Int.ceil_add_natCast]
  omega

/-- The inner layer of width `R` of a closed square of radius `r ≥ 0` has at most
`R (8 r + 4)` sites. It lies in four strips, each with at most `R` lattice lines of at
most `2 r + 1` sites. -/
theorem card_squareLayer_le (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r)
    (R : ℕ) : ((squareLayer Λ c r R).card : ℝ) ≤ R * (8 * r + 4) := by
  classical
  let I₁ := Finset.Icc ⌈c.1 - r⌉ ⌊c.1 + r⌋
  let I₂ := Finset.Icc ⌈c.2 - r⌉ ⌊c.2 + r⌋
  let A₁ := Finset.Ioc ⌊c.1 + r - R⌋ ⌊c.1 + r⌋
  let B₁ := Finset.Ico ⌈c.1 - r⌉ ⌈c.1 - r + R⌉
  let A₂ := Finset.Ioc ⌊c.2 + r - R⌋ ⌊c.2 + r⌋
  let B₂ := Finset.Ico ⌈c.2 - r⌉ ⌈c.2 - r + R⌉
  have hsub : (squareLayer Λ c r R).card ≤
      (A₁ ×ˢ I₂ ∪ B₁ ×ˢ I₂ ∪ I₁ ×ˢ A₂ ∪ I₁ ×ˢ B₂).card := by
    apply Finset.card_le_card_of_injOn Subtype.val _ Subtype.val_injective.injOn
    intro x hx
    obtain ⟨hlo, hhi⟩ := mem_squareLayer.mp hx
    have hsq : x ∈ closedSquareSample Λ c r := mem_closedSquareSample_iff_radius.mpr hhi
    obtain ⟨h₁, h₂⟩ := mem_closedSquareSample.mp hsq
    have hI₁ : x.1.1 ∈ I₁ := (mem_closedSquareSample_iff_int.mp hsq).1
    have hI₂ : x.1.2 ∈ I₂ := (mem_closedSquareSample_iff_int.mp hsq).2
    rw [abs_le] at h₁ h₂
    simp only [squareRadius, lt_max_iff, lt_abs] at hlo
    simp only [Finset.coe_union, Finset.coe_product, Set.mem_union, Set.mem_prod,
      Finset.mem_coe, A₁, B₁, A₂, B₂, Finset.mem_Ioc, Finset.mem_Ico, Int.floor_lt,
      Int.le_floor, Int.ceil_le, Int.lt_ceil]
    rcases hlo with (h | h) | (h | h)
    · exact Or.inl (Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, hI₂⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨by linarith, by linarith⟩, hI₂⟩))
    · exact Or.inl (Or.inr ⟨hI₁, ⟨by linarith, by linarith⟩⟩)
    · exact Or.inr ⟨hI₁, ⟨by linarith, by linarith⟩⟩
  have hunion : (A₁ ×ˢ I₂ ∪ B₁ ×ˢ I₂ ∪ I₁ ×ˢ A₂ ∪ I₁ ×ˢ B₂).card ≤
      A₁.card * I₂.card + B₁.card * I₂.card + I₁.card * A₂.card + I₁.card * B₂.card := by
    simp only [← Finset.card_product]
    repeat first | apply (Finset.card_union_le _ _).trans | gcongr
  have hA₁ : (A₁.card : ℝ) ≤ R := by
    exact_mod_cast (show A₁.card ≤ R by
      simpa only [A₁, add_sub_assoc', add_sub_cancel_right] using
        card_Ioc_floor_sub_le (c.1 + r) R)
  have hB₁ : (B₁.card : ℝ) ≤ R := by exact_mod_cast card_Ico_ceil_add_le (c.1 - r) R
  have hA₂ : (A₂.card : ℝ) ≤ R := by exact_mod_cast card_Ioc_floor_sub_le (c.2 + r) R
  have hB₂ : (B₂.card : ℝ) ≤ R := by exact_mod_cast card_Ico_ceil_add_le (c.2 - r) R
  have hI₁ := card_integerInterval_le c.1 r hr
  have hI₂ := card_integerInterval_le c.2 r hr
  have hreal : ((squareLayer Λ c r R).card : ℝ) ≤
      (A₁.card : ℝ) * I₂.card + (B₁.card : ℝ) * I₂.card + (I₁.card : ℝ) * A₂.card +
        (I₁.card : ℝ) * B₂.card := by
    exact_mod_cast hsub.trans hunion
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hI : (0 : ℝ) ≤ 2 * r + 1 := by linarith
  calc
    _ ≤ _ := hreal
    _ ≤ (R : ℝ) * (2 * r + 1) + R * (2 * r + 1) + (2 * r + 1) * R + (2 * r + 1) * R := by
      gcongr
    _ = _ := by ring

/-- The inner layer of width `R` of each selected square has at most `R (16 u + 4)` sites. -/
theorem card_squareLayer_rangeNestedPatch_le (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) {R : ℕ}
    {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : j < rangeNestedPatchCount R u) :
    ((squareLayer Λ c (rangeNestedPatchRadius R u j) R).card : ℝ) ≤ R * (16 * u + 4) := by
  have h := card_squareLayer_le Λ c (hu.trans (le_rangeNestedPatchRadius R u j)) R
  have hr := rangeNestedPatchRadius_le_two_mul hu hj
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  calc
    _ ≤ _ := h
    _ ≤ (R : ℝ) * (8 * (2 * u) + 4) := by gcongr
    _ = _ := by ring

/-- The scalar budget of the range-`R` family: with `m` equal weights `κ / m`,
`(16 u + 4) m (κ / m)² ≤ 18 s_R κ²` for every positive range. -/
theorem rangeNestedPatch_quadratic_budget {R : ℕ} (hR : 1 ≤ R) (u κ : ℝ) :
    (16 * u + 4) * ∑ _j : Fin (rangeNestedPatchCount R u),
      (κ / (rangeNestedPatchCount R u : ℝ)) ^ 2 ≤ 18 * rangePatchSpacing R * κ ^ 2 := by
  set m := rangeNestedPatchCount R u
  set s := rangePatchSpacing R
  have hm : (0 : ℝ) < m := by exact_mod_cast rangeNestedPatchCount_pos R u
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast rangeNestedPatchCount_pos R u
  have hs : (2 : ℝ) ≤ s := by exact_mod_cast two_le_rangePatchSpacing hR
  have hlt : u / s < m := div_lt_rangeNestedPatchCount R u
  have hu' : u < s * m := by
    rw [div_lt_iff₀ (by linarith)] at hlt
    linarith
  have hbound : 16 * u + 4 ≤ 18 * s * m := by nlinarith
  have hsum : (∑ _j : Fin m, (κ / (m : ℝ)) ^ 2) = κ ^ 2 / (m : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum]
  calc
    (16 * u + 4) * (κ ^ 2 / (m : ℝ)) = ((16 * u + 4) / (m : ℝ)) * κ ^ 2 := by ring
    _ ≤ (18 * s) * κ ^ 2 :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ hm).mpr hbound) (sq_nonneg κ)

end TNLean.PEPS.AreaLaw.Geometry
