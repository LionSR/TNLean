/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicSmallPatchCovers

/-!
# Footprint ratios uniform in the scale

The small-patch covers need a patch radius `u = ν t` (near a mark) or `u = ν n` (direct repainting
and resizing) such that every outer patch footprint meets at most two owners outside the inner
holes, with one ratio `ν` for all scales. The source obtains `ν` from the compactness observation:
the scaled old and new guides form finitely many label-equality types, the radius parameters
range over compact intervals bounded away from zero, and the joint sets of a radius and a point
are closed because being outside an open square is a non-strict distance inequality. This file
proves this argument in the following form:

* the two-owner condition for a guide, a working set, hole centers, an inner radius and a
  footprint radius; it survives shrinking the footprint and identifying labels;
* it is invariant under the similarities `u ↦ v + s u`, `s > 0`, of the sup metric, which scale
  all radii by `s`;
* for one guide with finitely many values whose true vertices in a compact working set lie strictly
  inside the smallest inner holes, the joint sets of a radius in `[r₀, r₁]`, `0 < r₀`, and a point
  are compact, and one footprint radius works for every inner radius in that interval;
* consequently, for finitely many template guides, one ratio `ν > 0` works for every template,
  every relabelling, every scale `s > 0`, every center and every inner radius in `s [r₀, r₁]`, with
  footprint radius `ν s`.

The identification of the guides of the protocol near a mark, at a direct repainting and at a
resizing, with relabelled similar images of finitely many templates is not proved here.

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
def TwoOwnerFootprints {ι : Type*} (f : ℝ × ℝ → ι) (W H : Set (ℝ × ℝ)) (r δ : ℝ) : Prop :=
  ∀ x p₁ p₂ p₃ : ℝ × ℝ, p₁ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
    p₂ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
    p₃ ∈ (closedBall x δ ∩ W) \ (⋃ h ∈ H, ball h r) →
    f p₁ = f p₂ ∨ f p₁ = f p₃ ∨ f p₂ = f p₃

section TwoOwner

variable {ι κ : Type*} {f : ℝ × ℝ → ι} {W H : Set (ℝ × ℝ)} {r δ : ℝ}

/-- The two-owner condition survives shrinking the footprint. -/
theorem TwoOwnerFootprints.mono {δ' : ℝ} (h : TwoOwnerFootprints f W H r δ) (hδ : δ' ≤ δ) :
    TwoOwnerFootprints f W H r δ' := fun x p₁ p₂ p₃ h₁ h₂ h₃ =>
  h x p₁ p₂ p₃ ⟨⟨closedBall_subset_closedBall hδ h₁.1.1, h₁.1.2⟩, h₁.2⟩
    ⟨⟨closedBall_subset_closedBall hδ h₂.1.1, h₂.1.2⟩, h₂.2⟩
    ⟨⟨closedBall_subset_closedBall hδ h₃.1.1, h₃.1.2⟩, h₃.2⟩

/-- **Identifying labels.** The two-owner condition survives any relabelling, injective or not:
identifying nominal labels can only merge owners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:315–318, 469–471`. -/
theorem TwoOwnerFootprints.relabel (h : TwoOwnerFootprints f W H r δ) (σ : ι → κ) :
    TwoOwnerFootprints (σ ∘ f) W H r δ := fun x p₁ p₂ p₃ h₁ h₂ h₃ => by
  rcases h x p₁ p₂ p₃ h₁ h₂ h₃ with e | e | e
  · exact Or.inl (congrArg σ e)
  · exact Or.inr (Or.inl (congrArg σ e))
  · exact Or.inr (Or.inr (congrArg σ e))

end TwoOwner

/-! ### Similarities of the sup metric -/

/-- The similarity `u ↦ v + s u` of the plane. -/
def similarity (v : ℝ × ℝ) (s : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := v + s • u

theorem dist_similarity (v : ℝ × ℝ) {s : ℝ} (hs : 0 < s) (a b : ℝ × ℝ) :
    dist (similarity v s a) (similarity v s b) = s * dist a b := by
  rw [similarity, similarity, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hs]

theorem similarity_inv (v : ℝ × ℝ) {s : ℝ} (hs : s ≠ 0) (q : ℝ × ℝ) :
    similarity v s (s⁻¹ • (q - v)) = q := by
  rw [similarity, smul_smul, mul_inv_cancel₀ hs, one_smul, add_sub_cancel]

/-- **Invariance under similarities.** If a template guide `g` satisfies the two-owner condition
with working set `W`, hole centers `H`, inner radius `r` and footprint radius `δ`, then its image
`q ↦ g (s⁻¹ (q - v))` under the similarity `u ↦ v + s u`, `s > 0`, satisfies it with the image
working set and hole centers and the radii `s r` and `s δ`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–471, 486–491`. -/
theorem TwoOwnerFootprints.image_similarity {ι : Type*} {g : ℝ × ℝ → ι} {W H : Set (ℝ × ℝ)}
    {r δ : ℝ} (h : TwoOwnerFootprints g W H r δ) (v : ℝ × ℝ) {s : ℝ} (hs : 0 < s) :
    TwoOwnerFootprints (fun q => g (s⁻¹ • (q - v))) (similarity v s '' W)
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
theorem exists_twoOwnerFootprints_Icc {ι : Type*} {f : ℝ × ℝ → ι} (hfin : (range f).Finite)
    {W : Set (ℝ × ℝ)} (hW : IsCompact W) {H : Set (ℝ × ℝ)} {r₀ r₁ : ℝ}
    (hH : ∀ c ∈ W, IsTrueVertex f c → ∃ h ∈ H, c ∈ ball h r₀) :
    ∃ δ > 0, ∀ r ∈ Icc r₀ r₁, TwoOwnerFootprints f W H r δ := by
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
      ∀ r ∈ Icc r₀ r₁, TwoOwnerFootprints (fun q => σ (g i (s⁻¹ • (q - v))))
        (similarity v s '' W i) (similarity v s '' H i) (s * r) (ν * s) := by
  choose δ hδ hδr using fun i => exists_twoOwnerFootprints_Icc (r₁ := r₁) (hfin i) (hW i) (hH i)
  obtain ⟨ν, hν0, hν⟩ : ∃ ν > 0, ∀ i, ν ≤ δ i := by
    rcases isEmpty_or_nonempty I with hI | hI
    · exact ⟨1, one_pos, fun i => hI.elim i⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min δ
      exact ⟨δ i₀, hδ i₀, hi₀⟩
  refine ⟨ν, hν0, fun i ι σ v s hs r hr => ?_⟩
  have := (((hδr i r hr).mono (hν i)).image_similarity v hs).relabel σ
  rw [mul_comm ν s]
  exact this

end TNLean.PEPS.Approximation
