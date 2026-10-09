/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionDiamondCounting
import TNLean.PEPS.AreaLaw.FiniteDomain
import QICLean.Entropy.SupportedMarginalTails

/-!
# Safe integer rectangles and nested contours around a cut

An integer rectangle is a product of two finite nonempty integer intervals; its size is the
larger number of sites along an axis. For a cut `A` of a finite induced domain, let `Z` be the
set of endpoints of the edges crossing `A`. A rectangle `Q` is safe if its sup-norm distance to
`Z` exceeds `D₀ · size Q`. Physical regions are the intersections of `A` with ambient
rectangles; holes and several components of the domain are allowed.

Inside a safe rectangle no admissible support meeting `A` leaves `A`: otherwise a walk of
length at most `R` inside the domain would cross an edge of the cut near `Q`. Consequently an
admissible support split by the region `A ∩ Q₀^{+d}` has ambient sup-norm diameter at most `R`
across the boundary of the rectangle `Q₀^{+d}`. Two contours `A ∩ Q₀^{+d}` and `A ∩ Q₀^{+d'}`
with `d + R ≤ d'` are therefore never split by the same support, and the supports split by one
contour meet a boundary layer of `Q₀^{+d}` of width `R + 1`, which has at most
`4 (R + 1) (size Q₀ + 2 d)` lattice points.

## Main definitions

* `IntRect`, `IntRect.size`, `IntRect.dilate`: integer rectangles, their size and `Q^{+d}`.
* `supDist`: the sup-norm distance of two lattice points.
* `IsSafe`: the safety condition of a rectangle for a cut.
* `rectRegion`: the physical region `A ∩ Q`.

## Main results

* `IntRect.toFinset_dilate`: `Q^{+d}` is the ambient dilation of `Q`.
* `subset_of_isSafe`: an admissible support meeting `A` inside a safe rectangle lies in `A`.
* `not_splits_two_contours`: the single-split property of the contours.
* `card_crossingTerms_rectRegion_le`: the crossing count `≤ 8 (R + 1) μ_R (size Q₀ + d)`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  the definitions before Lemma 3.2 and the proof of Lemma 3.2 (`lem:initial-buffer`),
  `02-initial.tex`, lines 220–239 and 263–293, `eq:initial-contour-budget`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-! ### Ambient distances -/

/-- Nearest-neighbor edges of an induced domain have ambient displacement one. -/
theorem latticeL1Distance_le_one_of_adj {Λ : Finset (ℤ × ℤ)} {x y : Site Λ}
    (h : (domainGraph Λ).Adj x y) : latticeL1Distance x.1 y.1 ≤ 1 := by
  simp only [domainGraph] at h
  simp only [latticeL1Distance]
  omega

/-- The sup-norm distance of two lattice points. Source: `02-initial.tex`, line 225,
`dist_∞`. -/
def supDist (a b : ℤ × ℤ) : ℕ := max (a.1 - b.1).natAbs (a.2 - b.2).natAbs

/-- The sup-norm distance is bounded by the lattice path distance. -/
theorem supDist_le_latticeL1Distance (a b : ℤ × ℤ) : supDist a b ≤ latticeL1Distance a b := by
  simp only [supDist, latticeL1Distance]
  omega

/-- A walk of length at most `R` in an induced domain moves its endpoints by sup-norm distance
at most `R`. -/
theorem supDist_le_of_walk {Λ : Finset (ℤ × ℤ)} {x y : Site Λ} {R : ℕ}
    (p : (domainGraph Λ).Walk x y) (hp : p.length ≤ R) : supDist x.1 y.1 ≤ R :=
  (supDist_le_latticeL1Distance _ _).trans
    ((latticeL1Distance_le_walk_length Subtype.val
      (fun _ _ h ↦ latticeL1Distance_le_one_of_adj h) p).trans hp)

/-! ### Integer rectangles -/

/-- An integer rectangle `[x₀, x₁] × [y₀, y₁]`, a product of two finite nonempty integer
intervals. Source: `02-initial.tex`, lines 222–223. -/
structure IntRect where
  /-- The left end of the horizontal interval. -/
  x₀ : ℤ
  /-- The right end of the horizontal interval. -/
  x₁ : ℤ
  /-- The lower end of the vertical interval. -/
  y₀ : ℤ
  /-- The upper end of the vertical interval. -/
  y₁ : ℤ
  hx : x₀ ≤ x₁
  hy : y₀ ≤ y₁

namespace IntRect

variable (Q : IntRect)

/-- The lattice points of a rectangle. -/
def toFinset : Finset (ℤ × ℤ) := Finset.Icc Q.x₀ Q.x₁ ×ˢ Finset.Icc Q.y₀ Q.y₁

/-- Membership in the rectangle is given by its four coordinate inequalities. -/
theorem mem_toFinset {Q : IntRect} {p : ℤ × ℤ} :
    p ∈ Q.toFinset ↔ Q.x₀ ≤ p.1 ∧ p.1 ≤ Q.x₁ ∧ Q.y₀ ≤ p.2 ∧ p.2 ≤ Q.y₁ := by
  simp [toFinset, and_assoc]

/-- The size of a rectangle, the larger number of sites along an axis.
Source: `02-initial.tex`, lines 223–224. -/
def size : ℕ := max (Q.x₁ + 1 - Q.x₀).toNat (Q.y₁ + 1 - Q.y₀).toNat

/-- A nonempty integer rectangle has size at least one. -/
theorem one_le_size : 1 ≤ Q.size := by
  have := Q.hx
  simp only [size]
  omega

/-- The number of horizontal sites is bounded by the rectangle size. -/
theorem width_le_size : Q.x₁ + 1 - Q.x₀ ≤ Q.size := by
  have := Q.hx
  simp only [size]
  omega

/-- The number of vertical sites is bounded by the rectangle size. -/
theorem height_le_size : Q.y₁ + 1 - Q.y₀ ≤ Q.size := by
  have := Q.hy
  simp only [size]
  omega

/-- The dilated rectangle `Q^{+d} = Q + ([-d, d]² ∩ ℤ²)`. Source: `02-initial.tex`,
lines 229–231. -/
def dilate (d : ℕ) : IntRect where
  x₀ := Q.x₀ - d
  x₁ := Q.x₁ + d
  y₀ := Q.y₀ - d
  y₁ := Q.y₁ + d
  hx := by have := Q.hx; omega
  hy := by have := Q.hy; omega

/-- Membership in the dilation is given by the expanded coordinate intervals. -/
theorem mem_dilate {Q : IntRect} {d : ℕ} {p : ℤ × ℤ} :
    p ∈ (Q.dilate d).toFinset ↔
      Q.x₀ - d ≤ p.1 ∧ p.1 ≤ Q.x₁ + d ∧ Q.y₀ - d ≤ p.2 ∧ p.2 ≤ Q.y₁ + d :=
  mem_toFinset

/-- The dilated rectangle is the ambient sup-norm dilation of the rectangle. -/
theorem toFinset_dilate (d : ℕ) : (Q.dilate d).toFinset = ambientDilation Q.toFinset d := by
  ext p
  rw [mem_dilate]
  simp only [ambientDilation, Finset.mem_biUnion, mem_toFinset, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(max Q.x₀ (min Q.x₁ p.1), max Q.y₀ (min Q.y₁ p.2)), ?_, ?_⟩
    · have := Q.hx; have := Q.hy
      simp only
      omega
    · simp only
      omega
  · rintro ⟨x, ⟨hx1, hx2, hx3, hx4⟩, ⟨h1, h2⟩, h3, h4⟩
    omega

/-- Dilation by zero leaves the rectangle unchanged. -/
@[simp] theorem dilate_zero : Q.dilate 0 = Q := by
  cases Q; simp [dilate]

/-- Successive dilations add their radii. -/
theorem dilate_dilate (d e : ℕ) : (Q.dilate d).dilate e = Q.dilate (d + e) := by
  simp only [dilate, Nat.cast_add, mk.injEq]
  omega

/-- The lattice points of a dilation increase with its radius. -/
theorem toFinset_dilate_mono {d e : ℕ} (h : d ≤ e) :
    (Q.dilate d).toFinset ⊆ (Q.dilate e).toFinset := by
  intro p hp
  rw [mem_dilate] at hp ⊢
  have : (d : ℤ) ≤ e := by exact_mod_cast h
  omega

/-- A point at sup-norm distance at most `k` from a point of `Q^{+d}` lies in `Q^{+(d+k)}`. -/
theorem mem_dilate_of_supDist_le {Q : IntRect} {d k : ℕ} {p p' : ℤ × ℤ}
    (hp : p ∈ (Q.dilate d).toFinset) (hk : supDist p p' ≤ k) :
    p' ∈ (Q.dilate (d + k)).toFinset := by
  rw [mem_dilate] at hp ⊢
  simp only [supDist] at hk
  push_cast
  omega

end IntRect

/-! ### Safety and physical regions -/

/-- **Safe rectangles.** The sup-norm distance from `Q` to every endpoint of an edge crossing
`A` exceeds `D₀ · size Q`; with no crossing edge the condition is vacuous.
Source: `02-initial.tex`, lines 220–228. -/
def IsSafe (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (D₀ : ℕ) (Q : IntRect) : Prop :=
  ∀ e ∈ edgeBoundary Λ A, ∀ z ∈ e, ∀ p ∈ Q.toFinset, D₀ * Q.size < supDist p z.1

/-- The physical region `A ∩ Q` of an ambient rectangle. Source: `02-initial.tex`,
lines 232–233. -/
def rectRegion {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ)) (Q : IntRect) : Finset (Site Λ) :=
  A.filter fun x ↦ x.1 ∈ Q.toFinset

/-- The physical rectangle region consists of cut sites lying in the rectangle. -/
theorem mem_rectRegion {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {Q : IntRect} {x : Site Λ} :
    x ∈ rectRegion A Q ↔ x ∈ A ∧ x.1 ∈ Q.toFinset :=
  Finset.mem_filter

/-- The physical rectangle region increases with the dilation radius. -/
theorem rectRegion_dilate_mono {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ)) (Q : IntRect)
    {d e : ℕ} (h : d ≤ e) : rectRegion A (Q.dilate d) ⊆ rectRegion A (Q.dilate e) := by
  intro x hx
  rw [mem_rectRegion] at hx ⊢
  exact ⟨hx.1, Q.toFinset_dilate_mono h hx.2⟩

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {D₀ R : ℕ} {Q : IntRect}

/-- **Supports near a safe rectangle stay in the cut.** If `Q` is safe with `R < D₀`, an
admissible support of range `R` with a site of `A` in `Q` lies wholly in `A`: otherwise a walk
of length at most `R` from that site leaves `A` and crosses an edge of the cut at sup-norm
distance at most `R` from `Q`. Source: `02-initial.tex`, lines 270–276. -/
theorem subset_of_isSafe (hsafe : IsSafe Λ A D₀ Q) (hR : R < D₀) {S : Finset (Site Λ)}
    (hS : IsAdmissibleSupport Λ R S) {v : Site Λ} (hvS : v ∈ S) (hvA : v ∈ A)
    (hvQ : v.1 ∈ Q.toFinset) : S ⊆ A := by
  classical
  intro w hwS
  by_contra hwA
  obtain ⟨p, hp⟩ := hS.2 v hvS w hwS
  obtain ⟨u, u', -, -, he, p', hp'⟩ := exists_edgeBoundary_of_walk p hvA hwA
  have hdist := supDist_le_of_walk p' (hp'.trans hp)
  have := hsafe _ he u (Sym2.mem_mk_left _ _) v.1 hvQ
  have hsize := Q.one_le_size
  have : D₀ ≤ D₀ * Q.size := Nat.le_mul_of_pos_right D₀ hsize
  omega

/-- A support split by a region meets it and its complement. -/
def Splits (D S : Finset (Site Λ)) : Prop := (∃ v ∈ S, v ∈ D) ∧ ∃ v ∈ S, v ∉ D

/-- **A support split by a contour lies across the rectangle boundary.** If `Q₀^{+d} ⊆ Q` with
`Q` safe and `R < D₀`, and an admissible support is split by `A ∩ Q₀^{+d}`, then it lies in `A`,
has a site in `Q₀^{+d}`, and has a site outside `Q₀^{+d}`. -/
theorem exists_of_splits_rectRegion (hsafe : IsSafe Λ A D₀ Q) (hR : R < D₀) {Q₀ : IntRect}
    {d : ℕ} (hQ : (Q₀.dilate d).toFinset ⊆ Q.toFinset) {S : Finset (Site Λ)}
    (hS : IsAdmissibleSupport Λ R S) (hsplit : Splits (rectRegion A (Q₀.dilate d)) S) :
    S ⊆ A ∧ (∃ v ∈ S, v.1 ∈ (Q₀.dilate d).toFinset) ∧ ∃ w ∈ S, w.1 ∉ (Q₀.dilate d).toFinset := by
  obtain ⟨⟨v, hvS, hv⟩, ⟨w, hwS, hw⟩⟩ := hsplit
  rw [mem_rectRegion] at hv hw
  have hSA := subset_of_isSafe hsafe hR hS hvS hv.1 (hQ hv.2)
  exact ⟨hSA, ⟨v, hvS, hv.2⟩, ⟨w, hwS, fun h ↦ hw ⟨hSA hwS, h⟩⟩⟩

/-- **Single split.** If `Q₀^{+d'} ⊆ Q` with `Q` safe, `R < D₀` and `d + R ≤ d'`, no admissible
support is split by both `A ∩ Q₀^{+d}` and `A ∩ Q₀^{+d'}`: the ambient diameter of a support is
at most its graph diameter `R`, smaller than the margin between the two rectangles.
Source: `02-initial.tex`, lines 280–286. -/
theorem not_splits_two_contours (hsafe : IsSafe Λ A D₀ Q) (hR : R < D₀) {Q₀ : IntRect}
    {d d' : ℕ} (hdd : d + R ≤ d') (hQ : (Q₀.dilate d').toFinset ⊆ Q.toFinset)
    {S : Finset (Site Λ)} (hS : IsAdmissibleSupport Λ R S)
    (h1 : Splits (rectRegion A (Q₀.dilate d)) S) (h2 : Splits (rectRegion A (Q₀.dilate d')) S) :
    False := by
  obtain ⟨-, -, w, hwS, hw⟩ := exists_of_splits_rectRegion hsafe hR hQ hS h2
  obtain ⟨v, hvS, hv⟩ := h1.1
  rw [mem_rectRegion] at hv
  obtain ⟨p, hp⟩ := hS.2 v hvS w hwS
  exact hw (Q₀.toFinset_dilate_mono hdd
    (IntRect.mem_dilate_of_supDist_le hv.2 (supDist_le_of_walk p hp)))

/-! ### Counting the supports split by one contour -/

/-- The boundary layer `Q^{+d} \ Q^{+(d-k)}` of a rectangle has at most `4 k (size Q + 2 d)`
lattice points, for `k ≤ d`. -/
theorem card_dilate_sdiff_le (Q : IntRect) {d k : ℕ} (hk : k ≤ d) :
    ((Q.dilate d).toFinset \ (Q.dilate (d - k)).toFinset).card ≤ 4 * k * (Q.size + 2 * d) := by
  have hsub := Q.toFinset_dilate_mono (Nat.sub_le d k)
  rw [Finset.card_sdiff_of_subset hsub]
  simp only [IntRect.toFinset, IntRect.dilate, Finset.card_product, Int.card_Icc]
  have hw := Q.width_le_size
  have hh := Q.height_le_size
  have hx := Q.hx
  have hy := Q.hy
  have hkd : ((d - k : ℕ) : ℤ) = d - k := by push_cast [hk]; ring
  rw [hkd]
  set W := Q.x₁ + 1 - Q.x₀
  set H := Q.y₁ + 1 - Q.y₀
  have e1 : (Q.x₁ + d + 1 - (Q.x₀ - d)).toNat = (W + 2 * d).toNat := by congr 1; ring
  have e2 : (Q.y₁ + d + 1 - (Q.y₀ - d)).toNat = (H + 2 * d).toNat := by congr 1; ring
  have e3 : (Q.x₁ + (d - k) + 1 - (Q.x₀ - (d - k))).toNat = (W + 2 * d - 2 * k).toNat := by
    congr 1; ring
  have e4 : (Q.y₁ + (d - k) + 1 - (Q.y₀ - (d - k))).toNat = (H + 2 * d - 2 * k).toNat := by
    congr 1; ring
  rw [e1, e2, e3, e4]
  have hkz : (k : ℤ) ≤ d := by exact_mod_cast hk
  zify
  rw [Nat.cast_sub (by
    apply Nat.mul_le_mul <;> omega)]
  push_cast
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
    Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  nlinarith

/-- At most `μ_R = 2^{v_R - 1}` admissible supports of range `R` contain a given site, with
`v_R = 1 + 2 R (R + 1)`. Source: `01-preliminaries.tex`, lines 95–102. -/
theorem card_admissibleSupport_containing_le (v : Site Λ) :
    (Finset.univ.filter fun X : AdmissibleSupport Λ R ↦ v ∈ X.1).card ≤
      2 ^ ((1 + 2 * R * (R + 1)) - 1) := by
  classical
  have h := card_supports_containing_le_diamond (G := domainGraph Λ) Subtype.val
    Subtype.val_injective (fun _ _ h ↦ latticeL1Distance_le_one_of_adj h)
    (Finset.univ.image fun X : AdmissibleSupport Λ R ↦ X.1) R (by
      intro S hS a ha x hx
      obtain ⟨X, -, rfl⟩ := Finset.mem_image.mp hS
      exact X.2.2 a ha x hx) v
  refine le_trans ?_ h
  rw [Finset.filter_image, Finset.card_image_of_injective _ Subtype.val_injective]

/-- **The crossing count of one contour.** Let `Q` be safe with `R < D₀`, and let
`Q₀^{+d} ⊆ Q` with `R + 1 ≤ d`. At most `8 (R + 1) μ_R (size Q₀ + d)` admissible supports are
split by `A ∩ Q₀^{+d}`, where `μ_R = 2^{v_R - 1}` bounds the number of admissible supports
containing a site and `v_R = 1 + 2 R (R + 1)`. Missing sites of the domain only decrease the
count. Source: `02-initial.tex`, lines 276–293, `eq:initial-contour-budget`. -/
theorem card_crossingTerms_rectRegion_le (hsafe : IsSafe Λ A D₀ Q) (hR : R < D₀) {Q₀ : IntRect}
    {d : ℕ} (hd : R + 1 ≤ d) (hQ : (Q₀.dilate d).toFinset ⊆ Q.toFinset) :
    (Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1)
        (rectRegion A (Q₀.dilate d))).card ≤
      8 * (R + 1) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) * (Q₀.size + d) := by
  classical
  set layer : Finset (ℤ × ℤ) := (Q₀.dilate d).toFinset \ (Q₀.dilate (d - (R + 1))).toFinset
  set sites : Finset (Site Λ) := Finset.univ.filter fun v ↦ v.1 ∈ layer
  set μ := 2 ^ ((1 + 2 * R * (R + 1)) - 1)
  -- every split support has a site in the layer
  have hcover : Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1)
      (rectRegion A (Q₀.dilate d)) ⊆
        sites.biUnion fun v ↦ Finset.univ.filter fun X : AdmissibleSupport Λ R ↦ v ∈ X.1 := by
    intro X hX
    simp only [Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨-, ⟨v, hvS, hv⟩, ⟨w, hwS, hw⟩⟩ := exists_of_splits_rectRegion hsafe hR hQ X.2 hX
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, sites, layer,
      Finset.mem_sdiff]
    refine ⟨v, ⟨hv, fun hv' ↦ hw ?_⟩, hvS⟩
    obtain ⟨p, hp⟩ := X.2.2 v hvS w hwS
    exact Q₀.toFinset_dilate_mono (by omega)
      (IntRect.mem_dilate_of_supDist_le hv' (supDist_le_of_walk p hp))
  -- sites of the layer
  have hsites : sites.card ≤ layer.card := by
    refine Finset.card_le_card_of_injOn Subtype.val (fun v hv ↦ ?_) Subtype.val_injective.injOn
    exact (Finset.mem_filter.mp hv).2
  have hlayer := card_dilate_sdiff_le Q₀ hd
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ sites.card * μ :=
        Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦ card_admissibleSupport_containing_le v
    _ ≤ 4 * (R + 1) * (Q₀.size + 2 * d) * μ := Nat.mul_le_mul_right _ (hsites.trans hlayer)
    _ ≤ 4 * (R + 1) * (2 * (Q₀.size + d)) * μ := by
        gcongr
        omega
    _ = 8 * (R + 1) * μ * (Q₀.size + d) := by ring

end TNLean.PEPS.AreaLaw
