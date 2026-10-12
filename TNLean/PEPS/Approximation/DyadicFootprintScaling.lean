/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicSmallPatchCovers

/-!
# Footprint ratios uniform in the scale

The small-patch covers need a footprint radius `ν t` (near a mark) or `ν n` (direct repainting
and resizing) such that every closed footprint of that radius meets at most two owners outside the
inner holes, with one ratio `ν` for all scales. The source's patches have inner radius `u` and
outer squares of radius at most `2 u`, so the source's inner patch radius is `u = ν t / 2` (or
`ν n / 2`) for the ratio `ν` of this file. The source obtains `ν` from the compactness observation:
the scaled old and new guides form finitely many label-equality types, the radius parameters
range over compact intervals bounded away from zero, and the joint sets of a radius and a point
are closed because being outside an open square is a non-strict distance inequality. This file
proves this argument in the following form:

* the two-owner condition for a guide, a working set, hole centers, an inner radius and a
  footprint radius; it survives shrinking the footprint and identifying labels;
* it survives enlarging some of the inner holes, which covers configurations in which only some
  holes have been resized;
* it is invariant under the similarities `u ↦ v + s u`, `s > 0`, of the sup metric, which scale
  all radii by `s`;
* for one guide with finitely many values whose true vertices in a compact working set lie strictly
  inside the smallest inner holes, the joint sets of a radius in `[r₀, r₁]`, `0 < r₀`, and a point
  are compact, and one footprint radius works for every inner radius in that interval;
* consequently, for finitely many template guides, one ratio `ν > 0` works for every template,
  every relabelling, every scale `s > 0`, every center and every inner radius in `s [r₀, r₁]`, with
  footprint radius `ν s`.
* injective relabellings and homeomorphisms preserve true vertices, so a guide that agrees near a
  center with an injective relabelling of a similar image of a template inherits the template's
  two-owner condition, with holes at its own true vertices;
* a representative map of each label-equality type of a relabelling, through which the relabelling
  is injective;
* a block guide near a grid corner, in units of its side, is a relabelling of a block guide of side
  one labelled by the slots of a square window of blocks.

The guides of the protocol are identified with relabelled similar images of finitely many
templates in `TNLean.PEPS.Approximation.DyadicFootprintTemplates` (near a mark) and
`TNLean.PEPS.Approximation.DyadicBlockFootprints` (direct repaintings and resizings).

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the compactness observation
  and its uniformity (lines 447–479), the point covers (lines 481–505), the direct repainting
  (lines 507–527) and the resizing (lines 529–541).
-/

namespace TNLean.PEPS.Approximation

open Set Metric

/-! ### The two-owner condition -/

/-- The two-owner condition: every closed footprint of radius `δ` meets at most two labels of the
guide `f` at its points of the working set `W` outside the open inner holes `ball h r`, `h ∈ H`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:453–462, 481–485`. -/
def HasTwoOwnerFootprints {ι : Type*} (f : ℝ × ℝ → ι) (W H : Set (ℝ × ℝ)) (r δ : ℝ) : Prop :=
  ∀ x p₁ p₂ p₃ : ℝ × ℝ, p₁ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
    p₂ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
    p₃ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
    f p₁ = f p₂ ∨ f p₁ = f p₃ ∨ f p₂ = f p₃

section TwoOwner

variable {ι κ : Type*} {f : ℝ × ℝ → ι} {W H : Set (ℝ × ℝ)} {r δ : ℝ}

/-- The two-owner condition survives shrinking the footprint. -/
theorem HasTwoOwnerFootprints.mono {δ' : ℝ} (h : HasTwoOwnerFootprints f W H r δ) (hδ : δ' ≤ δ) :
    HasTwoOwnerFootprints f W H r δ' := fun x p₁ p₂ p₃ h₁ h₂ h₃ =>
  h x p₁ p₂ p₃ ⟨⟨closedBall_subset_closedBall hδ h₁.1.1, h₁.1.2⟩, h₁.2⟩
    ⟨⟨closedBall_subset_closedBall hδ h₂.1.1, h₂.1.2⟩, h₂.2⟩
    ⟨⟨closedBall_subset_closedBall hδ h₃.1.1, h₃.1.2⟩, h₃.2⟩

/-- **Enlarging some holes.** If the two-owner condition holds with inner radius `r`, it holds for
the points of the working set outside the holes `ball h (ρ h)`, `h ∈ H`, of any radii `ρ h ≥ r`.
This covers the intermediate configurations of a resizing, in which some holes already have their
new radius.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:538–540`. -/
theorem HasTwoOwnerFootprints.of_le_radii (h : HasTwoOwnerFootprints f W H r δ) {ρ : ℝ × ℝ → ℝ}
    (hρ : ∀ c ∈ H, r ≤ ρ c) (x p₁ p₂ p₃ : ℝ × ℝ)
    (h₁ : p₁ ∈ (closedBall x δ ∩ W) \ ⋃ c ∈ H, ball c (ρ c))
    (h₂ : p₂ ∈ (closedBall x δ ∩ W) \ ⋃ c ∈ H, ball c (ρ c))
    (h₃ : p₃ ∈ (closedBall x δ ∩ W) \ ⋃ c ∈ H, ball c (ρ c)) :
    f p₁ = f p₂ ∨ f p₁ = f p₃ ∨ f p₂ = f p₃ := by
  have sub : (⋃ c ∈ H, ball c r) ⊆ ⋃ c ∈ H, ball c (ρ c) :=
    iUnion₂_mono fun c hc => ball_subset_ball (hρ c hc)
  exact h x p₁ p₂ p₃ ⟨h₁.1, fun hm => h₁.2 (sub hm)⟩ ⟨h₂.1, fun hm => h₂.2 (sub hm)⟩
    ⟨h₃.1, fun hm => h₃.2 (sub hm)⟩

/-- **Identifying labels.** The two-owner condition survives any relabelling, injective or not:
identifying nominal labels can only merge owners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:315–318, 469–471`. -/
theorem HasTwoOwnerFootprints.relabel (h : HasTwoOwnerFootprints f W H r δ) (σ : ι → κ) :
    HasTwoOwnerFootprints (σ ∘ f) W H r δ := fun x p₁ p₂ p₃ h₁ h₂ h₃ => by
  rcases h x p₁ p₂ p₃ h₁ h₂ h₃ with e | e | e
  · exact Or.inl (congrArg σ e)
  · exact Or.inr (Or.inl (congrArg σ e))
  · exact Or.inr (Or.inr (congrArg σ e))

end TwoOwner

/-! ### Similarities of the sup metric -/

/-- The similarity `u ↦ v + s u` of the plane. -/
def similarity (v : ℝ × ℝ) (s : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := v + s • u

/-- A similarity of ratio `s > 0` multiplies sup distances by `s`. -/
theorem dist_similarity (v : ℝ × ℝ) {s : ℝ} (hs : 0 < s) (a b : ℝ × ℝ) :
    dist (similarity v s a) (similarity v s b) = s * dist a b := by
  rw [similarity, similarity, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hs]

/-- The similarity `u ↦ v + s u` undoes `q ↦ s⁻¹ (q - v)`. -/
theorem similarity_inv (v : ℝ × ℝ) {s : ℝ} (hs : s ≠ 0) (q : ℝ × ℝ) :
    similarity v s (s⁻¹ • (q - v)) = q := by
  rw [similarity, smul_smul, mul_inv_cancel₀ hs, one_smul, add_sub_cancel]

/-- **Invariance under similarities.** If a template guide `g` satisfies the two-owner condition
with working set `W`, hole centers `H`, inner radius `r` and footprint radius `δ`, then its image
`q ↦ g (s⁻¹ (q - v))` under the similarity `u ↦ v + s u`, `s > 0`, satisfies it with the image
working set and hole centers and the radii `s r` and `s δ`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–471, 486–491`. -/
theorem HasTwoOwnerFootprints.image_similarity {ι : Type*} {g : ℝ × ℝ → ι} {W H : Set (ℝ × ℝ)}
    {r δ : ℝ} (h : HasTwoOwnerFootprints g W H r δ) (v : ℝ × ℝ) {s : ℝ} (hs : 0 < s) :
    HasTwoOwnerFootprints (fun q => g (s⁻¹ • (q - v))) (similarity v s '' W)
      (similarity v s '' H) (s * r) (s * δ) := by
  have back (q : ℝ × ℝ) : similarity v s (s⁻¹ • (q - v)) = q := similarity_inv v hs.ne' q
  have key {x p : ℝ × ℝ} (hp : p ∈ (closedBall x (s * δ) ∩ similarity v s '' W) \
      (⋃ h ∈ similarity v s '' H, ball h (s * r))) :
      s⁻¹ • (p - v) ∈ (closedBall (s⁻¹ • (x - v)) δ ∩ W) \ (⋃ h ∈ H, ball h r) := by
    obtain ⟨⟨hpx, ⟨w, hw, rfl⟩⟩, hpo⟩ := hp
    have hw' : s⁻¹ • (similarity v s w - v) = w := by
      rw [similarity, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [hw']
    refine ⟨⟨?_, hw⟩, fun hmem => hpo ?_⟩
    · rw [mem_closedBall] at hpx ⊢
      rw [← back x, dist_similarity v hs] at hpx
      exact le_of_mul_le_mul_left hpx hs
    · simp only [mem_iUnion, mem_ball] at hmem ⊢
      obtain ⟨h, hh, hd⟩ := hmem
      refine ⟨similarity v s h, mem_image_of_mem _ hh, ?_⟩
      rw [dist_similarity v hs]
      exact mul_lt_mul_of_pos_left hd hs
  intro x p₁ p₂ p₃ h₁ h₂ h₃
  exact h _ _ _ _ (key h₁) (key h₂) (key h₃)

/-! ### Closed joint sets and the radius parameter -/

/-- **The joint sets of a radius and a point are compact.** For a guide `f`, a compact working set
`W`, hole centers `H` and a label `c`, the pairs `(r, y)` with `r ∈ [r₀, r₁]`, `y` in the closure of
the region of `c` and in `W`, and `y` outside every open inner hole `ball h r` form a compact set:
being outside an open square is the non-strict inequality `r ≤ dist y h`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–469`. -/
theorem isCompact_footprintJointSet {ι : Type*} (f : ℝ × ℝ → ι) {W : Set (ℝ × ℝ)}
    (hW : IsCompact W) (H : Set (ℝ × ℝ)) (r₀ r₁ : ℝ) (c : ι) :
    IsCompact {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc r₀ r₁ ∧ q.2 ∈ closure (f ⁻¹' {c}) ∩ W ∧
      ∀ h ∈ H, q.1 ≤ dist q.2 h} := by
  refine (isCompact_Icc.prod (hW.inter_left isClosed_closure)).of_isClosed_subset ?_
    fun q hq => ⟨hq.1, hq.2.1⟩
  have h1 : IsClosed {q : ℝ × (ℝ × ℝ) | q.1 ∈ Icc r₀ r₁} := isClosed_Icc.preimage continuous_fst
  have h2 : IsClosed {q : ℝ × (ℝ × ℝ) | q.2 ∈ closure (f ⁻¹' {c}) ∩ W} :=
    (isClosed_closure.inter hW.isClosed).preimage continuous_snd
  have h3 : IsClosed {q : ℝ × (ℝ × ℝ) | ∀ h ∈ H, q.1 ≤ dist q.2 h} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun h => isClosed_iInter fun _ =>
      isClosed_le continuous_fst (continuous_snd.dist continuous_const)
  exact h1.inter (h2.inter h3)

/-- **The two-owner condition uniform in the inner radius.** Let a guide take finitely many values,
let `W` be compact, `0 < r₀`, and let every true vertex of the guide in `W` lie in an open inner
hole `ball h r₀`, `h ∈ H`, of the smallest radius. Then one footprint radius `δ > 0` gives the
two-owner condition for every inner radius `r ∈ [r₀, r₁]`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:453–469`. -/
theorem exists_hasTwoOwnerFootprints_Icc {ι : Type*} {f : ℝ × ℝ → ι} (hfin : (range f).Finite)
    {W : Set (ℝ × ℝ)} (hW : IsCompact W) {H : Set (ℝ × ℝ)} {r₀ r₁ : ℝ}
    (hH : ∀ c ∈ W, IsTrueVertex f c → ∃ h ∈ H, c ∈ ball h r₀) :
    ∃ δ > 0, ∀ r ∈ Icc r₀ r₁, HasTwoOwnerFootprints f W H r δ := by
  have : Finite (range f) := hfin.to_subtype
  let F : range f → Set (ℝ × (ℝ × ℝ)) := fun c =>
    {q | q.1 ∈ Icc r₀ r₁ ∧ q.2 ∈ closure (f ⁻¹' {c.1}) ∩ W ∧ ∀ h ∈ H, q.1 ≤ dist q.2 h}
  have hF : ∀ c, IsCompact (F c) := fun c => isCompact_footprintJointSet f hW H r₀ r₁ c.1
  have h3 : ∀ c₁ c₂ c₃ : range f, c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      F c₁ ∩ F c₂ ∩ F c₃ = ∅ := by
    intro c₁ c₂ c₃ h12 h13 h23
    refine eq_empty_of_forall_notMem ?_
    rintro ⟨r, y⟩ ⟨⟨⟨hr, ⟨hy₁, hyW⟩, hyH⟩, ⟨-, ⟨hy₂, -⟩, -⟩⟩, ⟨-, ⟨hy₃, -⟩, -⟩⟩
    obtain ⟨h, hh, hyh⟩ := hH y hyW ⟨c₁.1, c₂.1, c₃.1, Subtype.coe_ne_coe.2 h12,
      Subtype.coe_ne_coe.2 h13, Subtype.coe_ne_coe.2 h23, hy₁, hy₂, hy₃⟩
    exact absurd ((hr.1.trans (hyH h hh)).trans_lt (mem_ball.1 hyh)) (lt_irrefl _)
  obtain ⟨δ, hδ, Hδ⟩ := exists_footprint_two_owners_param hF h3
  refine ⟨δ, hδ, fun r hr x p₁ p₂ p₃ ⟨⟨b₁, w₁⟩, o₁⟩ ⟨⟨b₂, w₂⟩, o₂⟩ ⟨⟨b₃, w₃⟩, o₃⟩ => ?_⟩
  have mem (p : ℝ × ℝ) (hw : p ∈ W) (ho : p ∉ ⋃ h ∈ H, ball h r) :
      (r, p) ∈ F ⟨f p, p, rfl⟩ := by
    refine ⟨hr, ⟨subset_closure rfl, hw⟩, fun h hh => ?_⟩
    by_contra hlt
    exact ho (mem_biUnion hh (mem_ball.2 (not_le.1 hlt)))
  by_contra hne
  push Not at hne
  exact Hδ r x ⟨f p₁, p₁, rfl⟩ ⟨f p₂, p₂, rfl⟩ ⟨f p₃, p₃, rfl⟩
    (fun h => hne.1 (congrArg Subtype.val h)) (fun h => hne.2.1 (congrArg Subtype.val h))
    (fun h => hne.2.2 (congrArg Subtype.val h))
    ⟨⟨p₁, mem p₁ w₁ o₁, by rw [mem_closedBall] at b₁; exact b₁⟩,
      ⟨p₂, mem p₂ w₂ o₂, by rw [mem_closedBall] at b₂; exact b₂⟩,
      ⟨p₃, mem p₃ w₃ o₃, by rw [mem_closedBall] at b₃; exact b₃⟩⟩

/-! ### One ratio for finitely many templates -/

/-- **One footprint ratio for all scales.** Let finitely many template guides `g i`, each with
finitely many values, compact working sets `W i` and hole centers `H i`, have all their true
vertices in `W i` inside the open inner holes of radius `r₀ > 0`. Then there is one ratio `ν > 0`
such that, for every template, every relabelling `σ`, every scale `s > 0`, every center `v` and
every inner radius `r ∈ [r₀, r₁]`, the relabelled image `q ↦ σ (g i (s⁻¹ (q - v)))` satisfies the
two-owner condition with the image working set and hole centers, inner radius `s r` and footprint
radius `ν s`. In the source the templates are the finitely many label-equality types of the scaled
old and new guides, and `s` is `t` near a mark and `n` at a direct repainting or a resizing.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–479, 486–491, 515–520,
534–538`. -/
theorem exists_footprintRatio {I κ : Type*} [Finite I] {g : I → ℝ × ℝ → κ}
    (hfin : ∀ i, (range (g i)).Finite) {W H : I → Set (ℝ × ℝ)} (hW : ∀ i, IsCompact (W i))
    {r₀ r₁ : ℝ} (hH : ∀ i, ∀ c ∈ W i, IsTrueVertex (g i) c → ∃ h ∈ H i, c ∈ ball h r₀) :
    ∃ ν > 0, ∀ (i : I) {ι : Type*} (σ : κ → ι) (v : ℝ × ℝ) {s : ℝ}, 0 < s →
      ∀ r ∈ Icc r₀ r₁, HasTwoOwnerFootprints (fun q => σ (g i (s⁻¹ • (q - v))))
        (similarity v s '' W i) (similarity v s '' H i) (s * r) (ν * s) := by
  choose δ hδ hδr using fun i => exists_hasTwoOwnerFootprints_Icc (r₁ := r₁) (hfin i) (hW i) (hH i)
  obtain ⟨ν, hν0, hν⟩ : ∃ ν > 0, ∀ i, ν ≤ δ i := by
    rcases isEmpty_or_nonempty I with hI | hI
    · exact ⟨1, one_pos, fun i => hI.elim i⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min δ
      exact ⟨δ i₀, hδ i₀, hi₀⟩
  refine ⟨ν, hν0, fun i ι σ v s hs r hr => ?_⟩
  have := (((hδr i r hr).mono (hν i)).image_similarity v hs).relabel σ
  rw [mul_comm ν s]
  exact this

/-! ### True vertices under relabelling and similarities -/

/-- An injective relabelling on the values of a guide keeps its true vertices. -/
theorem isTrueVertex_comp_iff {X ι κ : Type*} [TopologicalSpace X] {f : X → ι} {σ : ι → κ}
    (hσ : InjOn σ (range f)) {c : X} : IsTrueVertex (σ ∘ f) c ↔ IsTrueVertex f c := by
  have pre (k : ι) (hk : k ∈ range f) : (σ ∘ f) ⁻¹' {σ k} = f ⁻¹' {k} := by
    ext p
    simp only [mem_preimage, Function.comp_apply, mem_singleton_iff]
    exact ⟨fun h => hσ (mem_range_self p) hk h, fun h => by rw [h]⟩
  constructor
  · rintro ⟨l₁, l₂, l₃, h12, h13, h23, h1, h2, h3⟩
    have back {l : κ} (hl : c ∈ closure ((σ ∘ f) ⁻¹' {l})) :
        ∃ k ∈ range f, l = σ k ∧ c ∈ closure (f ⁻¹' {k}) := by
      obtain ⟨p, hp⟩ : ((σ ∘ f) ⁻¹' {l}).Nonempty := by
        by_contra h
        rw [not_nonempty_iff_eq_empty] at h
        rw [h, closure_empty] at hl
        exact hl
      have hl' : l = σ (f p) := hp.symm
      exact ⟨f p, mem_range_self p, hl', by rwa [← pre _ (mem_range_self p), ← hl']⟩
    obtain ⟨k₁, -, rfl, c₁⟩ := back h1
    obtain ⟨k₂, -, rfl, c₂⟩ := back h2
    obtain ⟨k₃, -, rfl, c₃⟩ := back h3
    exact ⟨k₁, k₂, k₃, fun h => h12 (h ▸ rfl), fun h => h13 (h ▸ rfl), fun h => h23 (h ▸ rfl),
      c₁, c₂, c₃⟩
  · rintro ⟨k₁, k₂, k₃, h12, h13, h23, h1, h2, h3⟩
    have inr {k : ι} (hk : c ∈ closure (f ⁻¹' {k})) : k ∈ range f := by
      by_contra h
      have : f ⁻¹' {k} = ∅ := eq_empty_of_forall_notMem fun p hp => h ⟨p, hp⟩
      rw [this, closure_empty] at hk
      exact hk
    refine ⟨σ k₁, σ k₂, σ k₃, fun h => h12 (hσ (inr h1) (inr h2) h),
      fun h => h13 (hσ (inr h1) (inr h3) h), fun h => h23 (hσ (inr h2) (inr h3) h), ?_, ?_, ?_⟩
    · rwa [pre _ (inr h1)]
    · rwa [pre _ (inr h2)]
    · rwa [pre _ (inr h3)]

/-- A homeomorphism carries true vertices. -/
theorem isTrueVertex_comp_homeomorph {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → ι} (h : X ≃ₜ Y) {c : X} : IsTrueVertex (f ∘ h) c ↔ IsTrueVertex f (h c) := by
  have key (l : ι) : c ∈ closure ((f ∘ h) ⁻¹' {l}) ↔ h c ∈ closure (f ⁻¹' {l}) := by
    rw [preimage_comp, ← h.preimage_closure]; rfl
  simp only [IsTrueVertex, key]

/-- The inverse `q ↦ t⁻¹ (q - v)` of the similarity `u ↦ v + t u`, as a homeomorphism. -/
noncomputable def similarityInv (v : ℝ × ℝ) {t : ℝ} (ht : t ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.addRight (-v)).trans (Homeomorph.smulOfNeZero t⁻¹ (inv_ne_zero ht))

/-- The value of the inverse similarity. -/
theorem similarityInv_apply (v : ℝ × ℝ) {t : ℝ} (ht : t ≠ 0) (q : ℝ × ℝ) :
    similarityInv v ht q = t⁻¹ • (q - v) := by
  simp [similarityInv, sub_eq_add_neg]

/-- The offset `t⁻¹ (q - v)` has norm less than `ρ` exactly when `q` lies in the open square of
radius `t ρ` about `v`. -/
theorem norm_smul_inv_sub_lt_iff (v q : ℝ × ℝ) {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    ‖t⁻¹ • (q - v)‖ < ρ ↔ q ∈ ball v (t * ρ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, ← dist_eq_norm, inv_mul_lt_iff₀ ht,
    mem_ball]

/-- The offset `t⁻¹ (q - v)` has norm at most `ρ` exactly when `q` lies in the closed square of
radius `t ρ` about `v`. -/
theorem norm_smul_inv_sub_le_iff (v q : ℝ × ℝ) {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    ‖t⁻¹ • (q - v)‖ ≤ ρ ↔ q ∈ closedBall v (t * ρ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, ← dist_eq_norm, inv_mul_le_iff₀ ht,
    mem_closedBall]

/-- A similarity of ratio `t > 0` carries the closed square of radius `ρ` about the origin onto
the closed square of radius `t ρ` about `v`. -/
theorem image_similarity_closedBall (v : ℝ × ℝ) {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    similarity v t '' closedBall 0 ρ = closedBall v (t * ρ) := by
  ext q
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h0 : similarity v t 0 = v := by simp [similarity]
    rw [mem_closedBall]
    nth_rewrite 2 [← h0]
    rw [dist_similarity v ht]
    exact mul_le_mul_of_nonneg_left (mem_closedBall.1 hu) ht.le
  · intro hq
    refine ⟨t⁻¹ • (q - v), ?_, similarity_inv v ht.ne' q⟩
    rw [mem_closedBall, dist_zero_right]
    exact (norm_smul_inv_sub_le_iff v q ht ρ).2 hq

/-- The two-owner condition depends only on the values of the guide on the working set. -/
theorem HasTwoOwnerFootprints.congr {ι : Type*} {f g : ℝ × ℝ → ι} {W H : Set (ℝ × ℝ)} {r δ : ℝ}
    (h : HasTwoOwnerFootprints f W H r δ) (hfg : ∀ p ∈ W, f p = g p) :
    HasTwoOwnerFootprints g W H r δ := fun x p₁ p₂ p₃ h₁ h₂ h₃ => by
  rw [← hfg p₁ h₁.1.2, ← hfg p₂ h₂.1.2, ← hfg p₃ h₃.1.2]
  exact h x p₁ p₂ p₃ h₁ h₂ h₃

/-- **Transfer from a template.** Let a guide `f` agree, on the open square of radius `s ρ₃` about
`v`, with the relabelling by `σ` of a template `T` read through the similarity `u ↦ v + s u`, where
`σ` is injective on the values of `T`. If the image of `T` satisfies the two-owner condition with
the image working set `closedBall 0 ρ₁` and the image hole centers at the true vertices of `T` in
`closedBall 0 ρ₂`, `ρ₁ ≤ ρ₂ < ρ₃`, then `f` satisfies it with working set `closedBall v (s ρ₁)` and
hole centers at its true vertices in `closedBall v (s ρ₂)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:469–471, 486–491`. -/
theorem HasTwoOwnerFootprints.of_template {ι κ : Type*} {f : ℝ × ℝ → ι} {T : ℝ × ℝ → κ}
    {σ : κ → ι} (hσ : InjOn σ (range T)) {v : ℝ × ℝ} {s : ℝ} (hs : 0 < s) {ρ₁ ρ₂ ρ₃ : ℝ}
    (h12 : ρ₁ ≤ ρ₂) (h23 : ρ₂ < ρ₃) (hf : ∀ q ∈ ball v (s * ρ₃), f q = σ (T (s⁻¹ • (q - v))))
    {r δ : ℝ} (hT : HasTwoOwnerFootprints (fun q => σ (T (s⁻¹ • (q - v))))
      (similarity v s '' closedBall 0 ρ₁)
      (similarity v s '' {u | u ∈ closedBall (0 : ℝ × ℝ) ρ₂ ∧ IsTrueVertex T u}) r δ) :
    HasTwoOwnerFootprints f (closedBall v (s * ρ₁))
      {c | c ∈ closedBall v (s * ρ₂) ∧ IsTrueVertex f c} r δ := by
  have htv (q : ℝ × ℝ) (hq : q ∈ closedBall v (s * ρ₂)) :
      IsTrueVertex f q ↔ IsTrueVertex T (s⁻¹ • (q - v)) := by
    have hq3 : q ∈ ball v (s * ρ₃) :=
      closedBall_subset_ball (mul_lt_mul_of_pos_left h23 hs) hq
    have hloc : f =ᶠ[nhds q] (σ ∘ (T ∘ similarityInv v hs.ne')) := by
      filter_upwards [isOpen_ball.mem_nhds hq3] with p hp
      simp only [Function.comp_apply, similarityInv_apply]
      exact hf p hp
    rw [isTrueVertex_congr (incidentLabels_congr hloc),
      isTrueVertex_comp_iff (hσ.mono (range_comp_subset_range _ _)),
      isTrueVertex_comp_homeomorph, similarityInv_apply]
  have hH : similarity v s '' {u | u ∈ closedBall (0 : ℝ × ℝ) ρ₂ ∧ IsTrueVertex T u} =
      {c | c ∈ closedBall v (s * ρ₂) ∧ IsTrueVertex f c} := by
    ext q
    constructor
    · rintro ⟨w, ⟨hw, hwt⟩, rfl⟩
      have hq : similarity v s w ∈ closedBall v (s * ρ₂) := by
        rw [← image_similarity_closedBall v hs]
        exact mem_image_of_mem _ hw
      refine ⟨hq, (htv _ hq).2 ?_⟩
      rwa [similarity, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    · rintro ⟨hq, hqt⟩
      refine ⟨s⁻¹ • (q - v), ⟨?_, (htv q hq).1 hqt⟩, similarity_inv v hs.ne' q⟩
      rw [mem_closedBall, dist_zero_right]
      exact (norm_smul_inv_sub_le_iff v q hs ρ₂).2 hq
  rw [image_similarity_closedBall v hs, hH] at hT
  exact hT.congr fun q hq =>
    (hf q (closedBall_subset_ball ((mul_le_mul_of_nonneg_left h12 hs.le).trans_lt
      (mul_lt_mul_of_pos_left h23 hs)) hq)).symm

/-! ### Label-equality types -/

/-- A representative, under `σ`, of the class of `k`: a preimage under `σ` of `σ k`, chosen as a
function of `σ k`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:469–471`. -/
noncomputable def classRep {κ ι : Type*} [Nonempty κ] (σ : κ → ι) (k : κ) : κ :=
  Function.invFun σ (σ k)

/-- The representative of a class has the same image. -/
theorem classRep_spec {κ ι : Type*} [Nonempty κ] (σ : κ → ι) (k : κ) :
    σ (classRep σ k) = σ k :=
  Function.invFun_eq ⟨k, rfl⟩

/-- A relabelling is injective on the representatives of its classes. -/
theorem injOn_range_classRep {κ ι : Type*} [Nonempty κ] (σ : κ → ι) :
    InjOn σ (range (classRep σ)) := by
  rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩ h
  rw [classRep_spec σ k, classRep_spec σ k'] at h
  simp only [classRep, h]

/-! ### Block guides in units of their side -/

/-- The integer part of a real number in `[a, b + 1)` lies in `[a, b]`. -/
theorem floor_mem_Icc {a b : ℤ} {x : ℝ} (h₁ : (a : ℝ) ≤ x) (h₂ : x < b + 1) :
    ⌊x⌋ ∈ Finset.Icc a b :=
  Finset.mem_Icc.2 ⟨Int.le_floor.2 h₁, Int.floor_le_iff.2 h₂⟩

/-- The blocks `Q` with `|Q₁|, |Q₂| ≤ M`. -/
def blockWindow (M : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M

/-- The labels of the block templates: one slot for each block of the window, and one further
slot for the blocks outside it. -/
abbrev BlockSlot (M : ℕ) := Option (blockWindow M)

/-- The slot of a block. -/
def blockSlot (M : ℕ) (Q : ℤ × ℤ) : BlockSlot M :=
  if h : Q ∈ blockWindow M then some ⟨Q, h⟩ else none

/-- The labels that the block labels `lab` put in the slots, with `b` outside the window. -/
def blockSlotLabel {ι : Type*} {M : ℕ} (lab : ℤ × ℤ → ι) (b : ι) : BlockSlot M → ι
  | none => b
  | some Q => lab Q

/-- The slot labels of a block of the window are its labels. -/
theorem blockSlotLabel_blockSlot {ι : Type*} {M : ℕ} (lab : ℤ × ℤ → ι) (b : ι) {Q : ℤ × ℤ}
    (hQ : Q ∈ blockWindow M) : blockSlotLabel lab b (blockSlot M Q) = lab Q := by
  simp [blockSlot, hQ, blockSlotLabel]

/-- **A block guide in units of its side.** Near a grid corner `blockCorner s Q`, at points
`blockCorner s Q + s u` with `‖u‖ < M`, a block guide of side `s` is the relabelling of the block
guide of side one labelled by the slots of the window of radius `M`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–471, 515–520`. -/
theorem blockGuide_eq_blockSlot {ι : Type*} {s : ℝ} (hs : 0 < s) (lab : ℤ × ℤ → ι)
    (Q : ℤ × ℤ) (M : ℕ) {u : ℝ × ℝ} (hu : ‖u‖ < M) :
    blockGuide s lab (blockCorner s Q + s • u) =
      blockSlotLabel (fun R => lab (Q + R)) (lab Q) (blockGuide 1 (blockSlot M) u) := by
  rw [Prod.norm_def, max_lt_iff, Real.norm_eq_abs, Real.norm_eq_abs, abs_lt, abs_lt] at hu
  have hmem : (⌊u.1⌋, ⌊u.2⌋) ∈ blockWindow M :=
    Finset.mem_product.2 ⟨floor_mem_Icc (by push_cast; linarith) (by push_cast; linarith),
      floor_mem_Icc (by push_cast; linarith) (by push_cast; linarith)⟩
  have h1 : (s * Q.1 + s * u.1) / s = u.1 + Q.1 := by field_simp; ring
  have h2 : (s * Q.2 + s * u.2) / s = u.2 + Q.2 := by field_simp; ring
  simp only [blockGuide, blockIndex, blockCorner, div_one, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, h1, h2, Int.floor_add_intCast, blockSlot, hmem,
    dite_true, blockSlotLabel]
  congr 1
  exact Prod.ext (add_comm _ _) (add_comm _ _)

/-- On the open square of radius `s M` about a block corner, a block guide of side `s` is the
block guide of side one labelled by the slots of the window of radius `M`, read through the
similarity and relabelled first by the class representatives and then by the labels of the
blocks around the corner.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–471, 515–520`. -/
theorem blockGuide_eq_classRep {ι : Type*} {s : ℝ} (hs : 0 < s) (lab : ℤ × ℤ → ι)
    (Q : ℤ × ℤ) (M : ℕ) {q : ℝ × ℝ} (hq : q ∈ ball (blockCorner s Q) (s * M)) :
    blockGuide s lab q = blockSlotLabel (fun R => lab (Q + R)) (lab Q)
      (classRep (blockSlotLabel (fun R => lab (Q + R)) (lab Q))
        (blockGuide 1 (blockSlot M) (s⁻¹ • (q - blockCorner s Q)))) := by
  rw [classRep_spec (blockSlotLabel (fun R => lab (Q + R)) (lab Q)),
    ← blockGuide_eq_blockSlot hs lab Q M ((norm_smul_inv_sub_lt_iff _ q hs _).2 hq)]
  exact congrArg _ (similarity_inv _ hs.ne' q).symm

end TNLean.PEPS.Approximation
