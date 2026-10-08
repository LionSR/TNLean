/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicTrueVertices

/-!
# Small-patch covers of the dyadic distribution protocol

Every homogenization and removal of a point treatment, every direct repainting of a square of side
`n ≤ K₀ t`, and every hole resizing is implemented by small-patch rewrites. Their geometric
hypotheses are: each outer patch footprint meets at most two owners outside the inner holes, a
fixed number of patches covers the changed region and the affected outer holes, and the outer
patches avoid every untouched hole. This file proves the geometric facts behind these hypotheses
and behind the choice of the constants `K₀` and `ε₀`:

* the abstract compactness argument: if no three closed label regions with the inner holes
  removed meet, there is a positive footprint radius below which no footprint meets three of them,
  uniformly over a parameter set when the joint sets are compact; for one guide whose true vertices
  lie in open inner holes this is the two-owner condition. The instantiation on the scaled guide
  families of the protocol, which makes the footprint radius uniform in the scale, is not proved
  here;
* square nets: a net of mesh `u` covers a bounded set by a number of patches bounded in terms of
  its radius over `u`, with outer patches within `3u` of the set;
* the hole radius `h_n / n` of a direct repainting lies in `[ε₀ / max(K₀, 1), ε₀]`, and the two
  radii of a resizing differ only when `n < t`, by a factor between one and two;
* the true vertices of a guide that is uniform on `n`-blocks are grid corners, a direct repainting
  of one block changes the true-vertex status and the incident labels only at its four corners,
  and every other grid corner is at sup distance at least `n` from the block;
* toward the choice of `K₀`: distinct grid corners are at sup distance at least `n`, so for
  `n > 20 t` the tenfold enlargements of the treated squares are disjoint and contain no other grid
  corner, and lie in the charts about either endpoint of an edge where the band interfaces are
  straight rays; a ray of the edge construction meets the rim of the treated square about either
  endpoint in one point, and rays of normal ratios at least `1/2` apart meet it at points at
  distance at least `t / 2000`;
* at level `n = 1` with `ε₀ < 1/4`, an outer hole about a grid corner contains no lattice site.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the scales and holes
  (lines 102–133), the choice of `K₀` (lines 341–351), the small-patch covers (lines 447–570), and
  the final level (lines 669–673).
-/

namespace TNLean.PEPS.Approximation

open Set Metric SquareEdge

/-! ### The compactness observation -/

/-- For one triple of compact sets without a common point, there is a positive lower bound on
`max(|y₁ - y₂|, |y₁ - y₃|)` over points `yᵢ` of the three sets. -/
theorem exists_pos_le_max_dist_of_inter_eq_empty {X : Type*} [MetricSpace X] {F₁ F₂ F₃ : Set X}
    (h₁ : IsCompact F₁) (h₂ : IsCompact F₂) (h₃ : IsCompact F₃) (h : F₁ ∩ F₂ ∩ F₃ = ∅) :
    ∃ d > 0, ∀ y₁ ∈ F₁, ∀ y₂ ∈ F₂, ∀ y₃ ∈ F₃, d ≤ max (dist y₁ y₂) (dist y₁ y₃) := by
  set K := F₁ ×ˢ (F₂ ×ˢ F₃)
  have hK : IsCompact K := h₁.prod (h₂.prod h₃)
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun y₁ hy₁ y₂ hy₂ y₃ hy₃ => ?_⟩
    have : (y₁, y₂, y₃) ∈ K := ⟨hy₁, hy₂, hy₃⟩
    rw [hK0] at this
    exact this.elim
  · have hc : Continuous fun q : X × X × X => max (dist q.1 q.2.1) (dist q.1 q.2.2) := by
      fun_prop
    obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn hKne hc.continuousOn
    refine ⟨max (dist q.1 q.2.1) (dist q.1 q.2.2), ?_, fun y₁ hy₁ y₂ hy₂ y₃ hy₃ =>
      hmin (show (y₁, y₂, y₃) ∈ K from ⟨hy₁, hy₂, hy₃⟩)⟩
    by_contra hle
    push Not at hle
    have e₁ : q.1 = q.2.1 := dist_le_zero.1 ((le_max_left _ _).trans hle)
    have e₂ : q.1 = q.2.2 := dist_le_zero.1 ((le_max_right _ _).trans hle)
    obtain ⟨hq1, hq2, hq3⟩ := hq
    have : q.1 ∈ F₁ ∩ F₂ ∩ F₃ := ⟨⟨hq1, e₁ ▸ hq2⟩, e₂ ▸ hq3⟩
    rw [h] at this
    exact this

/-- **The abstract compactness argument.** Let finitely many compact sets `F c` be such that no
three with distinct labels have a common point. Then there is a footprint radius `δ > 0` such that
no closed ball of radius `δ` meets three of them with distinct labels.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:453–462`. -/
theorem exists_footprint_two_owners {X ι : Type*} [MetricSpace X] [Finite ι] {F : ι → Set X}
    (hF : ∀ c, IsCompact (F c))
    (h3 : ∀ c₁ c₂ c₃, c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ → F c₁ ∩ F c₂ ∩ F c₃ = ∅) :
    ∃ δ > 0, ∀ (x : X) (c₁ c₂ c₃ : ι), c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      ¬ ((closedBall x δ ∩ F c₁).Nonempty ∧ (closedBall x δ ∩ F c₂).Nonempty ∧
        (closedBall x δ ∩ F c₃).Nonempty) := by
  classical
  have key : ∀ τ : ι × ι × ι, ∃ d > 0, τ.1 ≠ τ.2.1 → τ.1 ≠ τ.2.2 → τ.2.1 ≠ τ.2.2 →
      ∀ y₁ ∈ F τ.1, ∀ y₂ ∈ F τ.2.1, ∀ y₃ ∈ F τ.2.2, d ≤ max (dist y₁ y₂) (dist y₁ y₃) := by
    rintro ⟨c₁, c₂, c₃⟩
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
    · obtain ⟨d, hd0, hdle⟩ := exists_pos_le_max_dist_of_inter_eq_empty (hF c₁) (hF c₂) (hF c₃)
        (h3 c₁ c₂ c₃ hd.1 hd.2.1 hd.2.2)
      exact ⟨d, hd0, fun _ _ _ => hdle⟩
    · exact ⟨1, one_pos, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hd⟩
  choose d hd0 hd using key
  -- a positive lower bound for the finitely many `d τ`
  obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ τ, m ≤ d τ := by
    rcases isEmpty_or_nonempty (ι × ι × ι) with hτ | hτ
    · exact ⟨1, one_pos, fun τ => hτ.elim τ⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min d
      exact ⟨d τ₀, hd0 τ₀, hτ₀⟩
  refine ⟨m / 3, by positivity, fun x c₁ c₂ c₃ h12 h13 h23 ⟨⟨y₁, hy₁, hF₁⟩, ⟨y₂, hy₂, hF₂⟩,
    ⟨y₃, hy₃, hF₃⟩⟩ => ?_⟩
  have hle := (hm (c₁, c₂, c₃)).trans (hd (c₁, c₂, c₃) h12 h13 h23 y₁ hF₁ y₂ hF₂ y₃ hF₃)
  rw [mem_closedBall] at hy₁ hy₂ hy₃
  have h12' : dist y₁ y₂ < m := by linarith [dist_triangle_right y₁ y₂ x]
  have h13' : dist y₁ y₃ < m := by linarith [dist_triangle_right y₁ y₃ x]
  exact absurd hle (not_le.2 (max_lt h12' h13'))

/-- **The compactness argument with parameters.** If the joint sets `F c` of a parameter and a
point are compact, and no three with distinct labels have a common point, then one footprint
radius `δ > 0` works for every value of the parameter: no closed ball of radius `δ` meets three
slices with distinct labels at the same parameter. The compactness of the joint sets is a
hypothesis here; the source derives it for its radius parameters at lines 465–468.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–469`. -/
theorem exists_footprint_two_owners_param {Λ X ι : Type*} [MetricSpace Λ] [MetricSpace X]
    [Finite ι] {F : ι → Set (Λ × X)} (hF : ∀ c, IsCompact (F c))
    (h3 : ∀ c₁ c₂ c₃, c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ → F c₁ ∩ F c₂ ∩ F c₃ = ∅) :
    ∃ δ > 0, ∀ (lam : Λ) (x : X) (c₁ c₂ c₃ : ι), c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      ¬ ((∃ y, (lam, y) ∈ F c₁ ∧ dist y x ≤ δ) ∧ (∃ y, (lam, y) ∈ F c₂ ∧ dist y x ≤ δ) ∧
        (∃ y, (lam, y) ∈ F c₃ ∧ dist y x ≤ δ)) := by
  obtain ⟨δ, hδ, H⟩ := exists_footprint_two_owners hF h3
  refine ⟨δ, hδ, fun lam x c₁ c₂ c₃ h12 h13 h23 ⟨⟨y₁, h₁, d₁⟩, ⟨y₂, h₂, d₂⟩, ⟨y₃, h₃, d₃⟩⟩ =>
    H (lam, x) c₁ c₂ c₃ h12 h13 h23 ⟨⟨_, ?_, h₁⟩, ⟨_, ?_, h₂⟩, ⟨_, ?_, h₃⟩⟩⟩ <;>
    simpa [mem_closedBall, Prod.dist_eq] using ‹_›

/-- **The two-owner condition of a guide.** Let a guide take finitely many values, and let every
true vertex of it in the compact working neighborhood `W` lie in an open inner hole square
`ball h r` with `h ∈ H`. Then there is a footprint radius `δ > 0` such that every closed footprint
of radius `δ` meets at most two labels at its points of `W` outside the open inner holes.

This is the test for one fixed guide and one working neighborhood; its uniformity over the scaled
guide families of the protocol is not proved here.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:453–462, 475–479`. -/
theorem exists_footprint_two_owners_guide {ι : Type*} {f : ℝ × ℝ → ι} (hfin : (range f).Finite)
    {W : Set (ℝ × ℝ)} (hW : IsCompact W) {H : Set (ℝ × ℝ)} {r : ℝ}
    (hH : ∀ c ∈ W, IsTrueVertex f c → ∃ h ∈ H, c ∈ ball h r) :
    ∃ δ > 0, ∀ (x : ℝ × ℝ) (p₁ p₂ p₃ : ℝ × ℝ),
      p₁ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
      p₂ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
      p₃ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
      f p₁ = f p₂ ∨ f p₁ = f p₃ ∨ f p₂ = f p₃ := by
  have : Finite (range f) := hfin.to_subtype
  set O := ⋃ h ∈ H, ball h r
  have hO : IsOpen O := isOpen_biUnion fun _ _ => isOpen_ball
  let F : range f → Set (ℝ × ℝ) := fun c => closure (f ⁻¹' {c.1}) ∩ W ∩ Oᶜ
  have hF : ∀ c, IsCompact (F c) := fun c =>
    (hW.inter_left isClosed_closure).inter_right hO.isClosed_compl
  have h3 : ∀ c₁ c₂ c₃ : range f, c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      F c₁ ∩ F c₂ ∩ F c₃ = ∅ := by
    intro c₁ c₂ c₃ h12 h13 h23
    refine eq_empty_of_forall_notMem ?_
    rintro y ⟨⟨⟨⟨hy₁, hyW⟩, hyO⟩, ⟨⟨hy₂, -⟩, -⟩⟩, ⟨⟨hy₃, -⟩, -⟩⟩
    obtain ⟨h, hh, hyh⟩ := hH y hyW ⟨c₁.1, c₂.1, c₃.1, Subtype.coe_ne_coe.2 h12,
      Subtype.coe_ne_coe.2 h13, Subtype.coe_ne_coe.2 h23, hy₁, hy₂, hy₃⟩
    exact hyO (mem_biUnion hh hyh)
  obtain ⟨δ, hδ, Hδ⟩ := exists_footprint_two_owners hF h3
  refine ⟨δ, hδ, fun x p₁ p₂ p₃ ⟨⟨b₁, w₁⟩, o₁⟩ ⟨⟨b₂, w₂⟩, o₂⟩ ⟨⟨b₃, w₃⟩, o₃⟩ => ?_⟩
  have mem (p : ℝ × ℝ) (hw : p ∈ W) (ho : p ∉ O) : p ∈ F ⟨f p, p, rfl⟩ :=
    ⟨⟨subset_closure rfl, hw⟩, ho⟩
  by_contra hne
  push Not at hne
  exact Hδ x ⟨f p₁, p₁, rfl⟩ ⟨f p₂, p₂, rfl⟩ ⟨f p₃, p₃, rfl⟩
    (fun h => hne.1 (congrArg Subtype.val h)) (fun h => hne.2.1 (congrArg Subtype.val h))
    (fun h => hne.2.2 (congrArg Subtype.val h))
    ⟨⟨p₁, b₁, mem p₁ w₁ o₁⟩, ⟨p₂, b₂, mem p₂ w₂ o₂⟩, ⟨p₃, b₃, mem p₃ w₃ o₃⟩⟩

/-! ### Square nets of patches -/

/-- Every point is within sup distance less than `u` of a point of the square net `u ℤ²`; the net
points are the block corners `(u k₁, u k₂)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:491–494`. -/
theorem exists_blockCorner_dist_lt {u : ℝ} (hu : 0 < u) (p : ℝ × ℝ) :
    ∃ k : ℤ × ℤ, dist p (blockCorner u k) < u := by
  refine ⟨blockIndex u p, ?_⟩
  have key (x : ℝ) : |x - u * ⌊x / u⌋| < u := by
    have h1 := Int.floor_le (x / u)
    have h2 := Int.lt_floor_add_one (x / u)
    rw [le_div_iff₀ hu] at h1
    rw [div_lt_iff₀ hu] at h2
    rw [abs_lt]
    constructor <;> nlinarith
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt (key p.1) (key p.2)

/-- The integers `k` with `|u k - c| ≤ ρ` lie in an interval with at most `2 ρ / u + 1` elements. -/
private theorem card_Icc_le {u : ℝ} (hu : 0 < u) (c : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((Finset.Icc ⌈(c - ρ) / u⌉ ⌊(c + ρ) / u⌋).card : ℝ) ≤ 2 * ρ / u + 1 := by
  rw [Int.card_Icc]
  have h1 := Int.le_ceil ((c - ρ) / u)
  have h2 := Int.floor_le ((c + ρ) / u)
  have hq : (c + ρ) / u - (c - ρ) / u = 2 * ρ / u := by ring
  have hpos : 0 ≤ 2 * ρ / u := by positivity
  rcases le_or_gt 0 (⌊(c + ρ) / u⌋ + 1 - ⌈(c - ρ) / u⌉) with h | h
  · have := Int.toNat_of_nonneg h
    have hc : ((⌊(c + ρ) / u⌋ + 1 - ⌈(c - ρ) / u⌉).toNat : ℝ) =
        ((⌊(c + ρ) / u⌋ + 1 - ⌈(c - ρ) / u⌉ : ℤ) : ℝ) := by exact_mod_cast this
    rw [hc]
    push_cast
    linarith
  · rw [Int.toNat_of_nonpos h.le]
    push_cast
    linarith

private theorem mem_Icc_of_abs_le {u : ℝ} (hu : 0 < u) {c ρ : ℝ} {k : ℤ} (h : |u * k - c| ≤ ρ) :
    k ∈ Finset.Icc ⌈(c - ρ) / u⌉ ⌊(c + ρ) / u⌋ := by
  rw [abs_le] at h
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hu, le_div_iff₀ hu]
  constructor <;> linarith

/-- **Counting net points.** The points of the square net `u ℤ²` within sup distance `ρ` of a
point lie in a finite set of at most `(2 ρ / u + 1) ^ 2` indices.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:498–499`. -/
theorem exists_finset_blockCorner_dist_le {u : ℝ} (hu : 0 < u) (o : ℝ × ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ s : Finset (ℤ × ℤ), (∀ k, dist (blockCorner u k) o ≤ ρ → k ∈ s) ∧
      (s.card : ℝ) ≤ (2 * ρ / u + 1) ^ 2 := by
  refine ⟨Finset.Icc ⌈(o.1 - ρ) / u⌉ ⌊(o.1 + ρ) / u⌋ ×ˢ Finset.Icc ⌈(o.2 - ρ) / u⌉
    ⌊(o.2 + ρ) / u⌋, fun k hk => ?_, ?_⟩
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff] at hk
    exact Finset.mem_product.2 ⟨mem_Icc_of_abs_le hu hk.1, mem_Icc_of_abs_le hu hk.2⟩
  · rw [Finset.card_product, Nat.cast_mul, sq]
    exact mul_le_mul (card_Icc_le hu _ hρ) (card_Icc_le hu _ hρ) (Nat.cast_nonneg _)
      (by positivity)

/-- **A net of small patches.** A set `K` inside the closed sup ball of radius `ρ` about `o` is
covered by the inner squares of radius `u` of at most `(2 (ρ + u) / u + 1) ^ 2` patches centered
on the net `u ℤ²`, all centers within `u` of `K`. For a fixed ratio `ν`, with `u = ν t` and
`ρ = O(t)`, the number of patches is bounded independently of `t`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:491–499, 520–521`. -/
theorem exists_netCover {u : ℝ} (hu : 0 < u) {K : Set (ℝ × ℝ)} {o : ℝ × ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hK : K ⊆ closedBall o ρ) :
    ∃ s : Finset (ℤ × ℤ), (s.card : ℝ) ≤ (2 * (ρ + u) / u + 1) ^ 2 ∧
      (∀ y ∈ K, ∃ k ∈ s, dist y (blockCorner u k) < u) ∧
      ∀ k ∈ s, ∃ y ∈ K, dist (blockCorner u k) y < u := by
  classical
  obtain ⟨s₀, hs₀, hcard⟩ := exists_finset_blockCorner_dist_le hu o (add_nonneg hρ hu.le)
  refine ⟨s₀.filter fun k => ∃ y ∈ K, dist (blockCorner u k) y < u,
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) hcard, fun y hy => ?_,
    fun k hk => (Finset.mem_filter.1 hk).2⟩
  obtain ⟨k, hk⟩ := exists_blockCorner_dist_lt hu y
  refine ⟨k, Finset.mem_filter.2 ⟨hs₀ k ?_, y, hy, by rwa [dist_comm]⟩, hk⟩
  have := mem_closedBall.1 (hK hy)
  linarith [dist_triangle (blockCorner u k) y o, dist_comm (blockCorner u k) y]

/-- An outer patch square of radius `2 u` about a center within `u` of `K` lies in the open
neighborhood of radius `3 u` of `K`; so it avoids every hole at distance at least `3 u` from `K`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:494–497, 521–525`. -/
theorem closedBall_two_mul_subset_thickening_three_mul {X : Type*} [PseudoMetricSpace X]
    {K : Set X} {x y : X} {u : ℝ} (hy : y ∈ K) (hxy : dist x y < u) :
    closedBall x (2 * u) ⊆ thickening (3 * u) K :=
  fun z hz => mem_thickening_iff.2 ⟨y, hy, by
    linarith [dist_triangle z x y, mem_closedBall.1 hz]⟩

/-! ### Hole radii -/

/-- **The hole radius of a direct repainting** `eq:geometry-small-radius`. For `0 < n ≤ K₀ t` the
ratio `h_n / n` lies in the interval `[ε₀ / max(K₀, 1), ε₀]`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-small-radius`,
`06-geometry.tex:511–516`. -/
theorem holeRadius_div_mem_Icc {ε₀ n t K₀ : ℝ} (hε : 0 ≤ ε₀) (hn : 0 < n) (ht : 0 < t)
    (hK : n ≤ K₀ * t) : holeRadius ε₀ n t / n ∈ Icc (ε₀ / max K₀ 1) ε₀ := by
  have hK0 : 0 < K₀ := by
    by_contra h
    push Not at h
    nlinarith
  have hM : 1 ≤ max K₀ 1 := le_max_right _ _
  rcases le_total n t with h | h
  · rw [holeRadius, min_eq_left h, mul_div_assoc, div_self hn.ne', mul_one]
    exact ⟨div_le_self hε hM, le_rfl⟩
  · rw [holeRadius, min_eq_right h]
    refine ⟨?_, ?_⟩
    · calc ε₀ / max K₀ 1 ≤ ε₀ / K₀ := div_le_div_of_nonneg_left hε hK0 (le_max_left _ _)
        _ ≤ ε₀ * t / n := by
          rw [div_le_div_iff₀ hK0 hn]
          nlinarith
    · rw [div_le_iff₀ hn]
      nlinarith

/-- **Hole resizing.** Entering level `n`, the radius passes from `ε₀ min(2n, t)` to
`ε₀ min(n, t)`. The two radii differ only when `n < t`, and the old one lies between one and two
times the new one.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:529–533`. -/
theorem holeRadius_resize {ε₀ n t : ℝ} (hε : 0 ≤ ε₀) (hn : 0 ≤ n) (ht : 0 ≤ t) :
    holeRadius ε₀ n t ≤ holeRadius ε₀ (2 * n) t ∧
      holeRadius ε₀ (2 * n) t ≤ 2 * holeRadius ε₀ n t ∧
      (holeRadius ε₀ (2 * n) t ≠ holeRadius ε₀ n t → n < t) := by
  unfold holeRadius
  refine ⟨mul_le_mul_of_nonneg_left (min_le_min_right _ (by linarith)) hε, ?_, fun h => ?_⟩
  · have : min (2 * n) t ≤ 2 * min n t := by
      rcases le_total n t with h | h
      · rw [min_eq_left h]; exact min_le_left _ _
      · rw [min_eq_right h]; exact (min_le_right _ _).trans (by linarith)
    nlinarith
  · by_contra hnt
    push Not at hnt
    exact h (by rw [min_eq_right hnt, min_eq_right (by linarith)])

/-! ### Grid corners -/

/-- Near a point that is not a multiple of `n`, the block index `⌊y / n⌋` is constant. -/
theorem floor_div_eventually_eq {n x : ℝ} (hn : 0 < n) (hx : ∀ a : ℤ, x ≠ n * a) :
    ∀ᶠ y in nhds x, ⌊y / n⌋ = ⌊x / n⌋ := by
  have h1 := Int.floor_le (x / n)
  have h2 := Int.lt_floor_add_one (x / n)
  have h1' : (⌊x / n⌋ : ℝ) < x / n := lt_of_le_of_ne h1 fun h => hx ⌊x / n⌋ (by
    rw [h, mul_div_cancel₀ _ hn.ne'])
  rw [lt_div_iff₀ hn] at h1'
  rw [div_lt_iff₀ hn] at h2
  filter_upwards [Ioo_mem_nhds h1' h2] with y hy
  rw [Int.floor_eq_iff, le_div_iff₀ hn, div_lt_iff₀ hn]
  exact ⟨hy.1.le, hy.2⟩

/-- Near any point, the block index `⌊y / n⌋` takes at most the two values `⌊x / n⌋` and
`⌊x / n⌋ - 1`. -/
private theorem floor_div_eventually_mem {n x : ℝ} (hn : 0 < n) :
    ∀ᶠ y in nhds x, ⌊y / n⌋ = ⌊x / n⌋ ∨ ⌊y / n⌋ = ⌊x / n⌋ - 1 := by
  have h1 := Int.floor_le (x / n)
  have h2 := Int.lt_floor_add_one (x / n)
  rw [le_div_iff₀ hn] at h1
  rw [div_lt_iff₀ hn] at h2
  have h1' : ((⌊x / n⌋ : ℝ) - 1) * n < x := by nlinarith
  filter_upwards [Ioo_mem_nhds h1' h2] with y hy
  have a : ⌊x / n⌋ - 1 ≤ ⌊y / n⌋ := by
    rw [Int.le_floor, le_div_iff₀ hn]; push_cast; exact hy.1.le
  have b : ⌊y / n⌋ < ⌊x / n⌋ + 1 := by
    rw [Int.floor_lt, div_lt_iff₀ hn]; push_cast; exact hy.2
  omega

/-- A labelling takes at most two values near `p`. Such a point is not a true vertex.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:109–111, 321–326`. -/
def LocallyTwo {X ι : Type*} [TopologicalSpace X] (f : X → ι) (p : X) : Prop :=
  ∃ P Q : ι, ∀ᶠ q in nhds p, f q ∈ ({P, Q} : Set ι)

section LocallyTwo

variable {X ι : Type*} [TopologicalSpace X] {f g : X → ι} {p : X}

theorem LocallyTwo.not_isTrueVertex (h : LocallyTwo f p) : ¬ IsTrueVertex f p := by
  obtain ⟨P, Q, h⟩ := h
  exact not_isTrueVertex_of_subset_pair (incidentLabels_subset h fun _ hq => hq)

theorem LocallyTwo.congr (h : LocallyTwo f p) (hfg : f =ᶠ[nhds p] g) : LocallyTwo g p := by
  obtain ⟨P, Q, h⟩ := h
  exact ⟨P, Q, by filter_upwards [h, hfg] with q hq e; rwa [← e]⟩

theorem locallyTwo_of_eventuallyEq_const {c : ι} (h : f =ᶠ[nhds p] fun _ => c) :
    LocallyTwo f p :=
  ⟨c, c, by filter_upwards [h] with q hq; simp [hq]⟩

end LocallyTwo

/-- **A block guide has at most two labels near every point other than a grid corner.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–322, 508`. -/
theorem locallyTwo_blockGuide {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι) {c : ℝ × ℝ}
    (hQ : ∀ Q : ℤ × ℤ, c ≠ blockCorner n Q) : LocallyTwo (blockGuide n lab) c := by
  have hc : (∀ a : ℤ, c.1 ≠ n * a) ∨ ∀ b : ℤ, c.2 ≠ n * b := by
    by_contra hc
    push Not at hc
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
    exact hQ (a, b) (Prod.ext ha hb)
  rcases hc with hc | hc
  · refine ⟨lab (⌊c.1 / n⌋, ⌊c.2 / n⌋), lab (⌊c.1 / n⌋, ⌊c.2 / n⌋ - 1), ?_⟩
    filter_upwards [continuous_fst.continuousAt.eventually (floor_div_eventually_eq hn hc),
      continuous_snd.continuousAt.eventually (floor_div_eventually_mem (x := c.2) hn)]
      with p h1 h2
    simp only [blockGuide, blockIndex, h1]
    rcases h2 with h2 | h2 <;> simp [h2]
  · refine ⟨lab (⌊c.1 / n⌋, ⌊c.2 / n⌋), lab (⌊c.1 / n⌋ - 1, ⌊c.2 / n⌋), ?_⟩
    filter_upwards
      [continuous_fst.continuousAt.eventually (floor_div_eventually_mem (x := c.1) hn),
        continuous_snd.continuousAt.eventually (floor_div_eventually_eq hn hc)] with p h1 h2
    simp only [blockGuide, blockIndex, h2]
    rcases h1 with h1 | h1 <;> simp [h1]

/-- **True vertices of a block guide are grid corners.** A guide uniform on the `n`-blocks has
its true vertices among the corners `(n a, n b)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–322, 508`. -/
theorem IsTrueVertex.eq_blockCorner {ι : Type*} {n : ℝ} (hn : 0 < n) {lab : ℤ × ℤ → ι}
    {c : ℝ × ℝ} (h : IsTrueVertex (blockGuide n lab) c) : ∃ Q : ℤ × ℤ, c = blockCorner n Q := by
  by_contra hQ
  push Not at hQ
  exact (locallyTwo_blockGuide hn lab hQ).not_isTrueVertex h

/-- The grid corner `Q` is one of the four corners of the block `S`. -/
def IsBlockCornerOf (S Q : ℤ × ℤ) : Prop :=
  (Q.1 = S.1 ∨ Q.1 = S.1 + 1) ∧ (Q.2 = S.2 ∨ Q.2 = S.2 + 1)

/-- A grid corner in the closed block `S` is one of its four corners. -/
theorem isBlockCornerOf_of_mem_closedSquare {n : ℝ} (hn : 0 < n) {S Q : ℤ × ℤ}
    (h : blockCorner n Q - blockCorner n S ∈ closedSquare n) : IsBlockCornerOf S Q := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 h
  simp only [blockCorner, Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  have a1 : (S.1 : ℝ) ≤ Q.1 := by nlinarith
  have a2 : (Q.1 : ℝ) ≤ S.1 + 1 := by nlinarith
  have a3 : (S.2 : ℝ) ≤ Q.2 := by nlinarith
  have a4 : (Q.2 : ℝ) ≤ S.2 + 1 := by nlinarith
  have b1 : S.1 ≤ Q.1 := by exact_mod_cast a1
  have b2 : Q.1 ≤ S.1 + 1 := by exact_mod_cast a2
  have b3 : S.2 ≤ Q.2 := by exact_mod_cast a3
  have b4 : Q.2 ≤ S.2 + 1 := by exact_mod_cast a4
  exact ⟨by omega, by omega⟩

/-- **Every other grid corner is far from the block.** A grid corner that is not a corner of the
block `S` is at sup distance at least `n` from every point of the closed block.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:521–524`. -/
theorem le_dist_blockCorner {n : ℝ} (hn : 0 < n) {S Q : ℤ × ℤ} (hQ : ¬ IsBlockCornerOf S Q)
    {p : ℝ × ℝ} (hp : p - blockCorner n S ∈ closedSquare n) : n ≤ dist p (blockCorner n Q) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hp
  simp only [blockCorner, Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [blockCorner]
  unfold IsBlockCornerOf at hQ
  rw [not_and_or] at hQ
  rcases hQ with hQ | hQ
  · refine le_max_of_le_left ?_
    rcases (show Q.1 ≤ S.1 - 1 ∨ S.1 + 2 ≤ Q.1 by omega) with h | h
    · have : (Q.1 : ℝ) ≤ S.1 - 1 := by exact_mod_cast h
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    · have : (S.1 : ℝ) + 2 ≤ Q.1 := by exact_mod_cast h
      rw [abs_of_nonpos (by nlinarith)]; nlinarith
  · refine le_max_of_le_right ?_
    rcases (show Q.2 ≤ S.2 - 1 ∨ S.2 + 2 ≤ Q.2 by omega) with h | h
    · have : (Q.2 : ℝ) ≤ S.2 - 1 := by exact_mod_cast h
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    · have : (S.2 : ℝ) + 2 ≤ Q.2 := by exact_mod_cast h
      rw [abs_of_nonpos (by nlinarith)]; nlinarith

/-- **A direct repainting changes true vertices only at the corners of the block.** Changing the
label of the block `S` of a block guide does not change the true-vertex status at any point other
than the four corners of `S`, nor the incident labels at any true vertex other than these corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:507–511`. -/
theorem isTrueVertex_blockGuide_update {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι)
    (S : ℤ × ℤ) (B : ι) {c : ℝ × ℝ}
    (hc : ∀ Q : ℤ × ℤ, c = blockCorner n Q → ¬ IsBlockCornerOf S Q) :
    (IsTrueVertex (blockGuide n (Function.update lab S B)) c ↔
        IsTrueVertex (blockGuide n lab) c) ∧
      (IsTrueVertex (blockGuide n lab) c →
        incidentLabels (blockGuide n (Function.update lab S B)) c =
          incidentLabels (blockGuide n lab) c) := by
  set K := (fun p => p - blockCorner n S) ⁻¹' closedSquare n
  have hK : IsClosed K := (isClosed_Icc.prod isClosed_Icc).preimage
    (continuous_id.sub continuous_const)
  by_cases hcK : c ∈ K
  · have no (lab' : ℤ × ℤ → ι) : ¬ IsTrueVertex (blockGuide n lab') c := fun h => by
      obtain ⟨Q, rfl⟩ := h.eq_blockCorner hn
      exact hc Q rfl (isBlockCornerOf_of_mem_closedSquare hn hcK)
    exact ⟨iff_of_false (no _) (no _), fun h => absurd h (no _)⟩
  · have heq : incidentLabels (blockGuide n (Function.update lab S B)) c =
        incidentLabels (blockGuide n lab) c := by
      refine incidentLabels_congr ?_
      filter_upwards [hK.isOpen_compl.mem_nhds hcK] with p hp
      have hne := blockIndex_ne_of_notMem_closedSquare hn S (p := p - blockCorner n S) hp
      rw [sub_add_cancel] at hne
      simp only [blockGuide, Function.update_of_ne hne]
    exact ⟨isTrueVertex_congr heq, fun _ => heq⟩

/-- Repainting the block `S` of the root square changes the block labels of a level only at `S`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–90`. -/
theorem levelLabels_insert {ι : Type*} {M : ℤ} (old new : ℤ × ℤ → ι) (ph : ι)
    (done : Set (ℤ × ℤ)) {S : ℤ × ℤ} (hS : InRoot M S) :
    levelLabels M old new ph (insert S done) =
      Function.update (levelLabels M old new ph done) S (new S) := by
  classical
  funext Q
  by_cases hQ : Q = S
  · subst hQ
    simp [levelLabels, hS]
  · rw [Function.update_of_ne hQ, levelLabels_insert_of_ne _ _ _ _ hQ]

/-- **True vertices during a level.** The direct repainting of the block `S` of the root square at
level `n` changes the true-vertex status and the incident labels of the main guide only at the
four corners of `S`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:507–511`. -/
theorem isTrueVertex_levelLabels_insert {ι : Type*} {n : ℝ} (hn : 0 < n) {M : ℤ}
    (old new : ℤ × ℤ → ι) (ph : ι) (done : Set (ℤ × ℤ)) {S : ℤ × ℤ} (hS : InRoot M S)
    {c : ℝ × ℝ} (hc : ∀ Q : ℤ × ℤ, c = blockCorner n Q → ¬ IsBlockCornerOf S Q) :
    (IsTrueVertex (blockGuide n (levelLabels M old new ph (insert S done))) c ↔
        IsTrueVertex (blockGuide n (levelLabels M old new ph done)) c) ∧
      (IsTrueVertex (blockGuide n (levelLabels M old new ph done)) c →
        incidentLabels (blockGuide n (levelLabels M old new ph (insert S done))) c =
          incidentLabels (blockGuide n (levelLabels M old new ph done)) c) := by
  rw [levelLabels_insert old new ph done hS]
  exact isTrueVertex_blockGuide_update hn _ S (new S) hc

/-- Distinct grid corners are at sup distance at least `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–322, 341–343`. -/
theorem le_dist_blockCorner_of_ne {n : ℝ} (hn : 0 < n) {Q Q' : ℤ × ℤ} (h : Q ≠ Q') :
    n ≤ dist (blockCorner n Q) (blockCorner n Q') := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [blockCorner]
  have key (a b : ℤ) (hab : a ≠ b) : n ≤ |n * a - n * b| := by
    rcases lt_or_gt_of_ne hab with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_of_nonpos (by nlinarith)]; nlinarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
  by_cases h1 : Q.1 = Q'.1
  · exact le_max_of_le_right (key _ _ fun h2 => h (Prod.ext h1 h2))
  · exact le_max_of_le_left (key _ _ h1)

/-! ### The choice of `K₀` -/

/-- **Separated treated squares.** For `n > 20 t`, the tenfold enlargements, of radius `10 t`, of
the treated squares about two distinct grid corners are disjoint, and such an enlargement contains
no grid corner other than its center.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:341–343`. -/
theorem disjoint_ball_blockCorner {n t : ℝ} (hn : 0 < n) (ht : 20 * t < n) {Q Q' : ℤ × ℤ}
    (h : Q ≠ Q') :
    Disjoint (ball (blockCorner n Q) (10 * t)) (ball (blockCorner n Q') (10 * t)) ∧
      blockCorner n Q' ∉ ball (blockCorner n Q) (10 * t) := by
  have hd := le_dist_blockCorner_of_ne hn h
  refine ⟨ball_disjoint_ball (by linarith), fun hm => ?_⟩
  rw [mem_ball, dist_comm] at hm
  linarith

/-- On the half of an edge next to its first endpoint, the band width is `s / 1000`. -/
theorem bandWidth_of_le_half {n s : ℝ} (hs : s ≤ n / 2) : bandWidth n s = s / 1000 := by
  rw [bandWidth, min_eq_left (by linarith)]

/-- On the half of an edge next to its second endpoint, the band width is `(n - s) / 1000`. -/
theorem bandWidth_of_half_le {n s : ℝ} (hs : n / 2 ≤ s) : bandWidth n s = (n - s) / 1000 := by
  rw [bandWidth, min_eq_right (by linarith)]

/-- **Straight-ray charts at the first endpoint.** In the open sup square of radius `n / 2` about
the first endpoint `s = 0` of an edge, a band `α < x < β` is the cone
`α s / 1000 < d < β s / 1000` with `s > 0`: its interfaces are straight rays from the endpoint.
In particular this holds in the tenfold enlargement of the treated square once `20 t ≤ n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:301–302, 341–343`. -/
theorem mem_edgeBand_iff_of_mem_ball {n : ℝ} {e : SquareEdge} {α β : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ ball (e.point n 0 0) (n / 2)) :
    p ∈ edgeBand n e α β ↔
      0 < e.par p ∧ α * (e.par p / 1000) < e.nor n p ∧ e.nor n p < β * (e.par p / 1000) := by
  have hs : |e.par p| < n / 2 := by
    have := e.abs_par_sub_le n p (e.point n 0 0)
    rw [par_point, sub_zero] at this
    exact this.trans_lt (mem_ball.1 hp)
  rw [abs_lt] at hs
  have hw := bandWidth_of_le_half (n := n) hs.2.le
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    rw [hw] at h3 h4
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    exact ⟨h1, by linarith, by rw [hw]; exact h3, by rw [hw]; exact h4⟩

/-- **Straight-ray charts at the second endpoint.** In the open sup square of radius `n / 2` about
the second endpoint `s = n` of an edge, a band `α < x < β` is the cone
`α (n - s) / 1000 < d < β (n - s) / 1000` with `s < n`: its interfaces are straight rays from the
endpoint.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:301–302, 341–343`. -/
theorem mem_edgeBand_iff_of_mem_ball_end {n : ℝ} {e : SquareEdge} {α β : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ ball (e.point n n 0) (n / 2)) :
    p ∈ edgeBand n e α β ↔ e.par p < n ∧ α * ((n - e.par p) / 1000) < e.nor n p ∧
      e.nor n p < β * ((n - e.par p) / 1000) := by
  have hs : |e.par p - n| < n / 2 := by
    have := e.abs_par_sub_le n p (e.point n n 0)
    rw [par_point] at this
    exact this.trans_lt (mem_ball.1 hp)
  rw [abs_lt] at hs
  have hw := bandWidth_of_half_le (n := n) (s := e.par p) (by linarith)
  constructor
  · rintro ⟨-, h2, h3, h4⟩
    rw [hw] at h3 h4
    exact ⟨h2, h3, h4⟩
  · rintro ⟨h2, h3, h4⟩
    exact ⟨by linarith, h2, by rw [hw]; exact h3, by rw [hw]; exact h4⟩

/-- **A ray meets the treated rim in one point, first endpoint.** A point of the curve `x = α`,
`|α| ≤ 8`, on the half of an edge next to its first endpoint and on the rim of the sup square of
radius `t` about that endpoint is the point with coordinates `s = t`, `d = α t / 1000`. So the
possible rim intersection points form a finite pattern after scaling by `t`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:344–347`. -/
theorem eq_point_of_mem_rim {n t α : ℝ} {e : SquareEdge} (hα : |α| ≤ 8) {p : ℝ × ℝ}
    (hpos : 0 < e.par p) (hhalf : e.par p ≤ n / 2)
    (hcurve : e.nor n p = α * bandWidth n (e.par p)) (hrim : dist p (e.point n 0 0) = t) :
    p = e.point n t (α * t / 1000) := by
  rw [bandWidth_of_le_half hhalf] at hcurve
  have hd : |e.nor n p| < e.par p := by
    rw [hcurve, abs_mul, abs_div, abs_of_pos hpos, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
    nlinarith [abs_nonneg α]
  rw [dist_point_zero, abs_of_pos hpos, max_eq_left (le_of_lt hd)] at hrim
  rw [← point_par_nor n e p, hcurve, hrim]
  ring_nf

/-- **A ray meets the treated rim in one point, second endpoint.** A point of the curve `x = α`,
`|α| ≤ 8`, on the half of an edge next to its second endpoint and on the rim of the sup square of
radius `t` about that endpoint is the point with coordinates `s = n - t`, `d = α t / 1000`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:344–347`. -/
theorem eq_point_of_mem_rim_end {n t α : ℝ} {e : SquareEdge} (hα : |α| ≤ 8) {p : ℝ × ℝ}
    (hlt : e.par p < n) (hhalf : n / 2 ≤ e.par p)
    (hcurve : e.nor n p = α * bandWidth n (e.par p)) (hrim : dist p (e.point n n 0) = t) :
    p = e.point n (n - t) (α * t / 1000) := by
  rw [bandWidth_of_half_le hhalf] at hcurve
  have hpos : 0 < n - e.par p := by linarith
  have hd : |e.nor n p| < n - e.par p := by
    rw [hcurve, abs_mul, abs_div, abs_of_pos hpos, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
    nlinarith [abs_nonneg α]
  rw [dist_point_end, abs_sub_comm, abs_of_pos hpos, max_eq_left (le_of_lt hd)] at hrim
  rw [← point_par_nor n e p, hcurve, ← hrim]
  ring_nf

/-- **Separation of the rim pattern of one edge.** Two rays `x = α` and `x = α'` of normal ratios
at least `1/2` apart meet the rim of the treated square of radius `t > 0` about an endpoint of the
edge at points with the same parallel coordinate `s` (`s = t` at the first endpoint, `s = n - t` at
the second) and at sup distance at least `t / 2000`. So the outer holes of radius `2 ε₀ t` about
them are disjoint once `ε₀ < 1/8000`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:346–351`. -/
theorem rim_separation {n s t α α' : ℝ} (e : SquareEdge) (ht : 0 < t) (hαα' : 1 / 2 ≤ |α - α'|)
    {ε₀ : ℝ} (hε : ε₀ < 1 / 8000) :
    t / 2000 ≤ dist (e.point n s (α * t / 1000)) (e.point n s (α' * t / 1000)) ∧
      Disjoint (closedBall (e.point n s (α * t / 1000)) (2 * ε₀ * t))
        (closedBall (e.point n s (α' * t / 1000)) (2 * ε₀ * t)) := by
  have hdist : dist (e.point n s (α * t / 1000)) (e.point n s (α' * t / 1000)) =
      |α - α'| * t / 1000 := by
    rw [dist_eq n e, par_point, par_point, nor_point, nor_point, sub_self, abs_zero,
      max_eq_right (abs_nonneg _),
      show α * t / 1000 - α' * t / 1000 = (α - α') * (t / 1000) by ring, abs_mul,
      abs_of_pos (by positivity : 0 < t / 1000)]
    ring
  have h1 : t / 2000 ≤ |α - α'| * t / 1000 := by nlinarith
  refine ⟨hdist ▸ h1, closedBall_disjoint_closedBall ?_⟩
  rw [hdist]
  nlinarith

/-! ### The final level -/

/-- **Trivial holes at the final level.** At level `n = 1`, with `ε₀ < 1/4`, an outer hole square
of radius `2 ε₀ < 1/2` about a grid corner contains no lattice site, so its encoding is trivial.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:669–672`. -/
theorem IsCellCenter.notMem_closedBall_blockCorner {p : ℝ × ℝ} (hp : IsCellCenter p)
    (Q : ℤ × ℤ) {r : ℝ} (hr : r < 1 / 2) : p ∉ closedBall (blockCorner 1 Q) r := by
  obtain ⟨i, j, rfl⟩ := hp
  intro h
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff] at h
  simp only [blockCorner, one_mul] at h
  have key (k a : ℤ) (hk : |(k : ℝ) + 1 / 2 - a| < 1 / 2) : False := by
    rw [abs_lt] at hk
    have h1 : (k : ℝ) < a := by linarith
    have h2 : (a : ℝ) < k + 1 := by linarith
    have h1' : k < a := by exact_mod_cast h1
    have h2' : a < k + 1 := by exact_mod_cast h2
    omega
  exact key i Q.1 (h.1.trans_lt hr)

end TNLean.PEPS.Approximation
