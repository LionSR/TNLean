/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicRimPatterns
import TNLean.PEPS.Approximation.DyadicSampledGuides
import TNLean.PEPS.Approximation.LocalGuideRewrite

/-!
# The point treatment of a mark as a local rewrite

A point treatment homogenizes an unmodified guide of the repainting of a block to one label on the
open square of radius `t` about a further grid corner `Q₀` (`06-geometry.tex`, lines 328–339),
and rewrites the frame by one small-patch rewrite over the treated square (lines 481–505); the
removal of the treatment is the reverse rewrite. Every
true vertex of the reading of a treated guide is within `t` of `Q₀` or at distance at least
`n - t` from it (`dist_le_or_le_dist_of_isTrueVertex_homogenize`), so the hole centers split as
in the local rewrite of `TNLean.PEPS.Approximation.LocalGuideRewrite`, with `ρ₀ = ρ₁ = t` and
`ρ₂ = n - t` (`exists_pointTreatment_planeConditions`).

## Main results

* `Approximation.dist_le_or_le_dist_of_isTrueVertex_homogenize`.
* `Approximation.exists_pointTreatment_planeConditions`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the point treatments
  (lines 328–339), the rim patterns (lines 341–351), the point-treatment covers (lines 481–505);
  Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

/-- **The true vertices of a treated guide near a mark.** Let `2 t < n`. Every true vertex of an
unmodified guide of the repainting of a block, homogenized on the open squares of radius `t`
about the grid corners of a finite set `M`, is within `t` of a given grid corner `Q₀` or at
distance at least `n - t` from it.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 330–347. -/
theorem dist_le_or_le_dist_of_isTrueVertex_homogenize {κ : Type*} {n t : ℝ} (hn : 0 < n)
    (ht : 0 ≤ t) (htn : 2 * t < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ} {g : ℝ × ℝ → κ}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (M : Finset (ℤ × ℤ)) (P : κ)
    (Q₀ : ℤ × ℤ) {c : ℝ × ℝ} (h : IsTrueVertex (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t)
      P (shiftGuide (blockCorner n S) g)) c) :
    dist c (blockCorner n Q₀) ≤ t ∨ n - t ≤ dist c (blockCorner n Q₀) := by
  rcases isTrueVertex_homogenize_cases hn htn hg M P h with ⟨Q, rfl⟩ | ⟨Q, -, hc⟩
  · by_cases hQ : Q = Q₀
    · subst hQ
      left
      rw [dist_self]
      exact ht
    · right
      linarith [le_dist_blockCorner_of_ne hn hQ]
  · have hct := dist_of_mem_rimPattern ht hc
    by_cases hQ : Q = Q₀
    · subst hQ
      exact Or.inl hct.le
    · right
      have := le_dist_blockCorner_of_ne hn hQ
      linarith [dist_triangle (blockCorner n Q) c (blockCorner n Q₀), dist_comm c (blockCorner n Q)]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- **The point treatment satisfies the plane conditions of Lemma 6.3.** Let `g` be an unmodified
guide of the repainting of the block `S` of side `n`, let `g₁` and `g₂` be the readings along `v`
of `g` homogenized to `L₀` on the open squares of radius `t` about the grid corners of `M₁` and
of `M₂`, two sets that differ at most at `Q₀` (a treatment adds `Q₀`, its removal removes it),
and let `V`, `V'` be finite sets of true vertices of `g₁`, `g₂` with the same points at distance
at least `n - t` from `Q₀`. Let the holes have radius `r`, the patches radius
`u`, with `2 t + 6 r + 3 u < n`. Suppose that `g₁` and `g₂` satisfy the two-owner condition for
footprints of radius `2 u` in a set `W` containing the ball of radius `t + 2 r + 3 u` about `Q₀`,
outside the open inner holes at sets of centers `H ⊆ V` and `H' ⊆ V'`, and that the list `P`
contains the owners in that ball and the tag holders at the centers within `t` of `Q₀`. Then
there is a rewrite from the frame of `g₁` with holes at `V` to the frame of `g₂` with holes at
`V'`, with patches on a net over the ball of radius `t + 2 r` about `Q₀`, satisfying the plane
conditions of Lemma 6.3; it has at most `(2 (t + 2 r + u) / u + 1)²` patches.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339 and 481–505; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–207. -/
theorem exists_pointTreatment_planeConditions {n t r u : ℝ} (hn : 0 < n) (ht : 0 < t)
    (hr : 0 < r) (hu : 0 < u) (hsep : 2 * t + 6 * r + 3 * u < n) {lab : ℤ × ℤ → κ}
    {S : ℤ × ℤ} {B : κ} {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g)
    {M₁ M₂ : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ) (hM : ∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) (L₀ : κ)
    {v : ℝ × ℝ} {g₁ g₂ : ℝ × ℝ → κ}
    (hg₁ : IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v)
    (hg₂ : IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v) (own : κ → Party) (ph : κ) (rank : κ → ℕ)
    {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g₁ c) (hV' : ∀ c ∈ V', IsTrueVertex g₂ c)
    (hVV' : ∀ c, n - t ≤ dist c (blockCorner n Q₀) → (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = r)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {W H H' : Set (ℝ × ℝ)} (hW : closedBall (blockCorner n Q₀) (t + 2 * r + 3 * u) ⊆ W)
    (hH : ∀ c ∈ H, c ∈ V) (hH' : ∀ c ∈ H', c ∈ V')
    (htwo : HasTwoOwnerFootprints g₁ W H r (2 * u))
    (htwo' : HasTwoOwnerFootprints g₂ W H' r (2 * u)) (P : Finset Party)
    (hP : ∀ p, dist p (blockCorner n Q₀) ≤ t + 2 * r + 3 * u →
      own (g₁ p) ∈ P ∧ own (g₂ p) ∈ P)
    (hPt : ∀ a ∈ V, dist a (blockCorner n Q₀) ≤ t → own (tagHolder rank g₁ ph a) ∈ P)
    (hPt' : ∀ a ∈ V', dist a (blockCorner n Q₀) ≤ t → own (tagHolder rank g₂ ph a) ∈ P) :
    ∃ G : GuideFrameRewrite pos q κ Party, G.PlaneConditions ∧ G.old = g₁ ∧ G.new = g₂ ∧
      G.own = own ∧ G.ph = ph ∧ G.rank = rank ∧ G.holeOld = hole ∧ G.holeNew = hole ∧
      G.patch = patch ∧ G.parties = P ∧ G.untouched ∪ G.oldAffected = V ∧
      G.untouched ∪ G.newAffected = V' ∧
      (∀ a ∈ G.oldAffected, dist a (blockCorner n Q₀) ≤ t) ∧
      (∀ a ∈ G.newAffected, dist a (blockCorner n Q₀) ≤ t) ∧
      (G.centers.card : ℝ) ≤ (2 * (t + 2 * r + u) / u + 1) ^ 2 := by
  have htn : 2 * t < n := by linarith
  have hmax : max t (t + 2 * r) = t + 2 * r := max_eq_right (by linarith)
  have hsplit : ∀ {g' : ℝ × ℝ → κ} (M' : Finset (ℤ × ℤ)),
      IsDisplacedReading g' (homogenize (⋃ Q ∈ M', ball (blockCorner n Q) t) L₀
        (shiftGuide (blockCorner n S) g)) v → ∀ c, IsTrueVertex g' c →
      dist c (blockCorner n Q₀) ≤ t ∨ n - t ≤ dist c (blockCorner n Q₀) :=
    fun M' hr c hc => dist_le_or_le_dist_of_isTrueVertex_homogenize hn ht.le htn hg M' L₀ Q₀
      (hr.isTrueVertex hc)
  have hchange : ∀ p, t < dist p (blockCorner n Q₀) → g₁ p = g₂ p := by
    intro p hp
    by_contra hne
    have hcl := hg₁.ne_subset_closure hg₂ hne
    have hsub : {x | homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) L₀
        (shiftGuide (blockCorner n S) g) x ≠ homogenize (⋃ Q ∈ M₂,
          ball (blockCorner n Q) t) L₀ (shiftGuide (blockCorner n S) g) x} ⊆
        closedBall (blockCorner n Q₀) t := by
      intro x hx
      by_contra hxc
      have hxb : x ∉ ball (blockCorner n Q₀) t := fun h => hxc (ball_subset_closedBall h)
      refine hx ?_
      have hiff : x ∈ (⋃ Q ∈ M₁, ball (blockCorner n Q) t) ↔
          x ∈ (⋃ Q ∈ M₂, ball (blockCorner n Q) t) := by
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨Q, hQ, h⟩
          have hQ₀ : Q ≠ Q₀ := fun e => hxb (e ▸ h)
          exact ⟨Q, (hM Q hQ₀).1 hQ, h⟩
        · rintro ⟨Q, hQ, h⟩
          have hQ₀ : Q ≠ Q₀ := fun e => hxb (e ▸ h)
          exact ⟨Q, (hM Q hQ₀).2 hQ, h⟩
      by_cases hx₁ : x ∈ (⋃ Q ∈ M₁, ball (blockCorner n Q) t)
      · rw [homogenize_of_mem hx₁, homogenize_of_mem (hiff.1 hx₁)]
      · rw [homogenize_of_notMem hx₁, homogenize_of_notMem (fun h => hx₁ (hiff.2 h))]
    have := closure_minimal hsub isClosed_closedBall hcl
    exact (not_le.2 hp) (mem_closedBall.1 this)
  obtain ⟨G, hG, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ :=
    exists_local_planeConditions (pos := pos) (o := blockCorner n Q₀) (ρ₀ := t) (ρ₁ := t)
      (ρ₂ := n - t) hr hu ht.le (by rw [hmax]; linarith) hchange own ph rank
      (fun c hc => hsplit M₁ hg₁ c (hV c hc)) (fun c hc => hsplit _ hg₂ c (hV' c hc)) hVV'
      hole patch hhole hpatch hpV hpV' (by rw [hmax]; exact hW) hH hH' htwo htwo' P
      (fun p hp => hP p (by rw [hmax] at hp; exact hp)) hPt hPt'
  rw [hmax] at h₁₄
  exact ⟨G, hG, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩

end TNLean.PEPS.Approximation
