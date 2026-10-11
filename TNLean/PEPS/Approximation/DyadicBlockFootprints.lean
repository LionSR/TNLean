/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicFootprintScaling

/-!
# Footprint ratios of block guides

At a direct repainting of a square of side `n ≤ K₀ t`, and at a hole resizing, the guides are
uniform on the blocks of one level, and the inner hole radius is a fixed multiple of the side up
to a factor in a compact interval. The source applies the compactness observation in units of
`n`: the label patterns near the square form a finite collection, and the radius ratios lie in a
compact positive interval. This file proves:

* in units of the side `s`, a block guide near a grid corner is an injective relabelling of one of
  finitely many templates: a block guide of side one labelled by the slots of a square window of
  blocks, composed with a representative map of a label-equality type;
* hence, for `0 < r₀`, one ratio `ν > 0` gives, for every block guide of every side
  `s`, every grid corner `v` and every inner radius in `[r₀ s, r₁ s]`, the two-owner condition with
  working set the closed square of radius `s ρ` about `v`, holes at the true vertices within
  `s (ρ + 1)` of `v`, and footprint radius `ν s`;
* in particular one ratio serves every direct repainting, with inner radius `h_n` and
  `ε₀ / max(K₀, 1) ≤ h_n / n ≤ ε₀`, and every resizing, with the old and new radii between
  `ε₀ n` and `2 ε₀ n` on the blocks of side `2 n`.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the compactness observation
  and its uniformity (lines 447–479), the direct repainting (lines 507–527) and the resizing
  (lines 529–541).
-/

namespace TNLean.PEPS.Approximation

open Set Metric

universe u

/-- **One footprint ratio for block guides.** Fix `ρ` and `0 < r₀`. There is a ratio `ν > 0`
such that every guide uniform on the blocks of side `s > 0`, about every grid corner `v`, with
every inner radius `r ∈ [r₀ s, r₁ s]`, has the two-owner condition with working set the closed
square of radius `s ρ` about `v`, holes at its true vertices within `s (ρ + 1)` of `v`, and
footprint radius `ν s`. For `r₁ ≤ 1` holes centered farther away do not meet the working set.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–479, 515–520,
534–538`. -/
theorem exists_blockGuide_footprintRatio {ρ r₀ r₁ : ℝ} (hr₀ : 0 < r₀) :
    ∃ ν > 0, ∀ {ι : Type u} {s : ℝ}, 0 < s → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ),
      ∀ r ∈ Icc (r₀ * s) (r₁ * s),
      HasTwoOwnerFootprints (blockGuide s lab) (closedBall (blockCorner s Q) (s * ρ))
        {c | c ∈ closedBall (blockCorner s Q) (s * (ρ + 1)) ∧ IsTrueVertex (blockGuide s lab) c}
        r (ν * s) := by
  set M : ℕ := ⌈ρ⌉₊ + 2
  have hM : ρ + 2 ≤ M := by push_cast [M]; linarith [Nat.le_ceil ρ]
  let T : (BlockSlot M → BlockSlot M) → ℝ × ℝ → BlockSlot M := fun π u =>
    π (blockGuide 1 (blockSlot M) u)
  obtain ⟨ν, hν, H⟩ := exists_footprintRatio.{0, 0, u} (I := BlockSlot M → BlockSlot M) (g := T)
    (fun _ => Set.toFinite _) (W := fun _ => closedBall 0 ρ) (fun _ => isCompact_closedBall 0 ρ)
    (H := fun π => {w | w ∈ closedBall (0 : ℝ × ℝ) (ρ + 1) ∧ IsTrueVertex (T π) w})
    (r₀ := r₀) (r₁ := r₁) (fun _ c hc htv =>
      ⟨c, ⟨closedBall_subset_closedBall (by linarith) hc, htv⟩, mem_ball_self hr₀⟩)
  refine ⟨ν, hν, fun {ι s} hs lab Q r hr => ?_⟩
  set σ : BlockSlot M → ι := blockSlotLabel (fun R => lab (Q + R)) (lab Q)
  have hinj : InjOn σ (range (T (classRep σ))) :=
    (injOn_range_classRep σ).mono (by rintro _ ⟨w, rfl⟩; exact mem_range_self _)
  have hf (q : ℝ × ℝ) (hq : q ∈ ball (blockCorner s Q) (s * (ρ + 2))) :
      blockGuide s lab q = σ (T (classRep σ) (s⁻¹ • (q - blockCorner s Q))) :=
    blockGuide_eq_classRep hs lab Q M (ball_subset_ball (mul_le_mul_of_nonneg_left hM hs.le) hq)
  have hrs : r / s ∈ Icc r₀ r₁ := ⟨(le_div_iff₀ hs).2 hr.1, (div_le_iff₀ hs).2 hr.2⟩
  have key := HasTwoOwnerFootprints.of_template (ρ₁ := ρ) (ρ₂ := ρ + 1) (ρ₃ := ρ + 2) hinj hs
    (by linarith) (by linarith) hf (H (classRep σ) σ (blockCorner s Q) hs (r / s) hrs)
  rwa [mul_div_cancel₀ r hs.ne'] at key

/-- **One footprint ratio for the direct repaintings.** Fix `ε₀ > 0` and `K₀`. There is a ratio
`ν > 0` such that, for every square of side `0 < n ≤ K₀ t`, every guide uniform on the
`n`-blocks (before or after the repainting) has the two-owner condition with working set the
closed square of radius `2 n` about a corner of the square, which contains the square and its
outer holes once `ε₀ ≤ 1/2`, holes at its true vertices within `3 n`, inner radius `h_n` and
footprint radius `ν n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:507–527`. -/
theorem exists_directRepainting_footprintRatio {ε₀ K₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ}, 0 < n → 0 < t → n ≤ K₀ * t →
      ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ),
      HasTwoOwnerFootprints (blockGuide n lab) (closedBall (blockCorner n Q) (n * 2))
        {c | c ∈ closedBall (blockCorner n Q) (n * (2 + 1)) ∧ IsTrueVertex (blockGuide n lab) c}
        (holeRadius ε₀ n t) (ν * n) := by
  obtain ⟨ν, hν, H⟩ := exists_blockGuide_footprintRatio.{u} (ρ := 2) (r₀ := ε₀ / max K₀ 1)
    (r₁ := ε₀) (div_pos hε (lt_of_lt_of_le one_pos (le_max_right _ _)))
  refine ⟨ν, hν, fun {ι n t} hn ht hK lab Q => H hn lab Q _ ?_⟩
  have h := holeRadius_div_mem_Icc hε.le hn ht hK
  exact ⟨(le_div_iff₀ hn).1 h.1, (div_le_iff₀ hn).1 h.2⟩

/-- For `0 < n < t`, both hole radii `h_n = ε₀ min(n, t)` and `h_{2n} = ε₀ min(2n, t)` lie
between `ε₀ n` and `2 ε₀ n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:371, 529–541`. -/
theorem mem_Icc_of_mem_holeRadius_pair {ε₀ n t r : ℝ} (hε : 0 < ε₀) (hn : 0 < n) (hnt : n < t)
    (hr : r ∈ ({holeRadius ε₀ n t, holeRadius ε₀ (2 * n) t} : Set ℝ)) :
    r ∈ Icc (ε₀ / 2 * (2 * n)) (ε₀ * (2 * n)) := by
  rcases hr with rfl | rfl
  · rw [holeRadius, min_eq_left hnt.le]
    exact ⟨by linarith, by nlinarith⟩
  · rw [holeRadius]
    refine ⟨?_, ?_⟩
    · have : n ≤ min (2 * n) t := le_min (by linarith) hnt.le
      nlinarith
    · have : min (2 * n) t ≤ 2 * n := min_le_left _ _
      nlinarith

/-- **One footprint ratio for the resizings.** Fix `ε₀ > 0`. There is a ratio `ν > 0` such that,
whenever `0 < n < t` (the only case in which the radii `h_{2n}` and `h_n` differ), every guide
uniform on the `2n`-blocks has, about every grid corner of side `2n`, for both inner radii
`h_n = ε₀ min(n, t)` and `h_{2n} = ε₀ min(2n, t)`, the two-owner condition with working set the
closed square of radius `2n`, which contains both outer footprints once `ε₀ ≤ 1/2`, holes at its
true vertices within `4n`, and footprint radius `2 ν n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:529–541`. -/
theorem exists_resizing_footprintRatio {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ}, 0 < n → n < t → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ),
      ∀ r ∈ ({holeRadius ε₀ n t, holeRadius ε₀ (2 * n) t} : Set ℝ),
      HasTwoOwnerFootprints (blockGuide (2 * n) lab)
        (closedBall (blockCorner (2 * n) Q) (2 * n * 1))
        {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧
          IsTrueVertex (blockGuide (2 * n) lab) c} r (ν * (2 * n)) := by
  obtain ⟨ν, hν, H⟩ := exists_blockGuide_footprintRatio.{u} (ρ := 1) (r₀ := ε₀ / 2) (r₁ := ε₀)
    (by positivity)
  exact ⟨ν, hν, fun {ι n t} hn hnt lab Q r hr =>
    H (by positivity) lab Q r (mem_Icc_of_mem_holeRadius_pair hε hn hnt hr)⟩

/-- **Intermediate configurations of a resizing.** With one ratio `ν > 0`, whenever `0 < n < t`,
every guide uniform on the `2n`-blocks satisfies the two-owner condition about every grid corner of
side `2n` when each hole has its own radius, `h_n` or `h_{2n}`: some holes may already be resized
and others not. The holes, the working set and the footprint radius are those of
`exists_resizing_footprintRatio`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:529–541`. -/
theorem exists_resizing_footprintRatio_mixed {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ}, 0 < n → n < t → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ)
      (ρ : ℝ × ℝ → ℝ), (∀ c, ρ c = holeRadius ε₀ n t ∨ ρ c = holeRadius ε₀ (2 * n) t) →
      ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall x (ν * (2 * n)) ∩ closedBall (blockCorner (2 * n) Q) (2 * n * 1)) \
          ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧
            IsTrueVertex (blockGuide (2 * n) lab) c}, ball c (ρ c)) →
      blockGuide (2 * n) lab p₁ = blockGuide (2 * n) lab p₂ ∨
        blockGuide (2 * n) lab p₁ = blockGuide (2 * n) lab p₃ ∨
        blockGuide (2 * n) lab p₂ = blockGuide (2 * n) lab p₃ := by
  obtain ⟨ν, hν, H⟩ := exists_resizing_footprintRatio.{u} hε
  refine ⟨ν, hν, fun {ι n t} hn hnt lab Q ρ hρ x p₁ p₂ p₃ hp => ?_⟩
  have hle : holeRadius ε₀ n t ≤ holeRadius ε₀ (2 * n) t :=
    mul_le_mul_of_nonneg_left (min_le_min (by linarith) le_rfl) hε.le
  exact (H hn hnt lab Q _ (Or.inl rfl)).of_le_radii
    (fun c _ => (hρ c).elim (fun h => h.ge) fun h => h ▸ hle) x p₁ p₂ p₃
    (hp p₁ (by simp)) (hp p₂ (by simp)) (hp p₃ (by simp))

end TNLean.PEPS.Approximation
