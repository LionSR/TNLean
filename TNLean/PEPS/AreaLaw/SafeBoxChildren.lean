/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles

/-!
# Partitioning a rectangle into chunks

Partition each axis of an integer rectangle `Q` into chunks of `r` sites and one final shorter
chunk if needed. The Cartesian products of the chunks are the children of `Q`: they are
rectangles of size at most `r`, pairwise disjoint, and cover `Q`. If `size Q ≤ M r` there are
at most `M` chunks along each axis. A child whose padding `C r` meets another child is within
`C` chunk positions of it along each axis, and a child at least `C` positions from the first
chunk and `C + 2` from the last one along both axes has its padding inside `Q`. Children of a
safe rectangle are safe.

## Main definitions

* `IntRect.width`, `IntRect.height`, `IntRect.numChunksX`, `IntRect.numChunksY`.
* `IntRect.child`: the child at chunk position `(a, b)`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 3.3 (`prop:initial-box`), `02-initial.tex`, lines 607–624.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

namespace IntRect

variable (Q : IntRect) (r : ℕ)

/-- The number of sites along the horizontal axis. -/
def width : ℕ := (Q.x₁ + 1 - Q.x₀).toNat

/-- The number of sites along the vertical axis. -/
def height : ℕ := (Q.y₁ + 1 - Q.y₀).toNat

theorem width_eq : (Q.width : ℤ) = Q.x₁ + 1 - Q.x₀ := by
  have := Q.hx; simp only [width]; omega

theorem height_eq : (Q.height : ℤ) = Q.y₁ + 1 - Q.y₀ := by
  have := Q.hy; simp only [height]; omega

theorem width_le_size' : Q.width ≤ Q.size := by
  have := Q.width_le_size; have := Q.width_eq; omega

theorem height_le_size' : Q.height ≤ Q.size := by
  have := Q.height_le_size; have := Q.height_eq; omega

/-- The number of horizontal chunks of `r` sites. -/
def numChunksX : ℕ := (Q.width - 1) / r + 1

/-- The number of vertical chunks of `r` sites. -/
def numChunksY : ℕ := (Q.height - 1) / r + 1

theorem numChunksX_le {M : ℕ} (hr : 1 ≤ r) (hQ : Q.size ≤ M * r) : Q.numChunksX r ≤ M := by
  have hw := Q.width_le_size'
  have h1 := Q.one_le_size
  simp only [numChunksX]
  have : (Q.width - 1) / r < M := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  omega

theorem numChunksY_le {M : ℕ} (hr : 1 ≤ r) (hQ : Q.size ≤ M * r) : Q.numChunksY r ≤ M := by
  have hw := Q.height_le_size'
  have h1 := Q.one_le_size
  simp only [numChunksY]
  have : (Q.height - 1) / r < M := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  omega

/-- The child of `Q` at chunk position `(a, b)`: the product of the `a`-th horizontal and the
`b`-th vertical chunk of `r` sites, the last chunks being cut off by `Q`.
Source: `02-initial.tex`, lines 609–612. -/
def child (a b : ℕ) : IntRect where
  x₀ := Q.x₀ + a * r
  x₁ := max (Q.x₀ + a * r) (min (Q.x₀ + a * r + r - 1) Q.x₁)
  y₀ := Q.y₀ + b * r
  y₁ := max (Q.y₀ + b * r) (min (Q.y₀ + b * r + r - 1) Q.y₁)
  hx := le_max_left _ _
  hy := le_max_left _ _

variable {Q r}

/-- The chunk position of an offset `t ∈ [0, n)` is `t / r`, and it is a valid position. -/
theorem div_lt_numChunks {n t : ℕ} (ht : t < n) : t / r < (n - 1) / r + 1 :=
  Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))

/-- A valid chunk position `a` of `n ≥ 1` sites starts at offset at most `n - 1`. -/
private theorem chunk_mul_le {n a : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) (ha : a < (n - 1) / r + 1) :
    (a : ℤ) * r ≤ n - 1 := by
  have h : a * r ≤ n - 1 := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
  have h' : ((a * r : ℕ) : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast h
  push_cast [Nat.cast_sub hn] at h'
  exact h'

/-- Points of a child at a valid position. -/
theorem mem_child {a b : ℕ} (hr : 1 ≤ r) (ha : a < Q.numChunksX r) (hb : b < Q.numChunksY r)
    {p : ℤ × ℤ} :
    p ∈ (Q.child r a b).toFinset ↔
      Q.x₀ + a * r ≤ p.1 ∧ p.1 ≤ Q.x₀ + a * r + r - 1 ∧ p.1 ≤ Q.x₁ ∧
      Q.y₀ + b * r ≤ p.2 ∧ p.2 ≤ Q.y₀ + b * r + r - 1 ∧ p.2 ≤ Q.y₁ := by
  have hw := Q.width_eq
  have hh := Q.height_eq
  have hax := chunk_mul_le (n := Q.width) hr (by have := Q.hx; omega) ha
  have hby := chunk_mul_le (n := Q.height) hr (by have := Q.hy; omega) hb
  have hr' : (1 : ℤ) ≤ r := by exact_mod_cast hr
  rw [mem_toFinset]
  simp only [child]
  omega

/-- Children lie in the parent. -/
theorem child_subset {a b : ℕ} (hr : 1 ≤ r) (ha : a < Q.numChunksX r)
    (hb : b < Q.numChunksY r) : (Q.child r a b).toFinset ⊆ Q.toFinset := by
  intro p hp
  rw [mem_child hr ha hb] at hp
  rw [mem_toFinset]
  have : (0 : ℤ) ≤ a * r := by positivity
  have : (0 : ℤ) ≤ b * r := by positivity
  omega

/-- Children have size at most `r`. -/
theorem size_child_le (a b : ℕ) (hr : 1 ≤ r) : (Q.child r a b).size ≤ r := by
  simp only [size, child]
  omega

/-- Every point of the parent lies in the child at its chunk position. -/
theorem exists_mem_child (hr : 1 ≤ r) {p : ℤ × ℤ} (hp : p ∈ Q.toFinset) :
    ∃ a < Q.numChunksX r, ∃ b < Q.numChunksY r, p ∈ (Q.child r a b).toFinset := by
  rw [mem_toFinset] at hp
  set s := (p.1 - Q.x₀).toNat
  set t := (p.2 - Q.y₀).toNat
  have hs : s < Q.width := by have := Q.width_eq; omega
  have ht : t < Q.height := by have := Q.height_eq; omega
  refine ⟨s / r, div_lt_numChunks hs, t / r, div_lt_numChunks ht, ?_⟩
  rw [mem_child hr (div_lt_numChunks hs) (div_lt_numChunks ht)]
  have h1 : ((s / r : ℕ) : ℤ) * r ≤ s := by exact_mod_cast Nat.div_mul_le_self s r
  have h2 : (s : ℤ) < ((s / r : ℕ) : ℤ) * r + r := by
    exact_mod_cast Nat.lt_div_mul_add (a := s) (b := r) (by omega)
  have h3 : ((t / r : ℕ) : ℤ) * r ≤ t := by exact_mod_cast Nat.div_mul_le_self t r
  have h4 : (t : ℤ) < ((t / r : ℕ) : ℤ) * r + r := by
    exact_mod_cast Nat.lt_div_mul_add (a := t) (b := r) (by omega)
  have hs' : (s : ℤ) = p.1 - Q.x₀ := by omega
  have ht' : (t : ℤ) = p.2 - Q.y₀ := by omega
  omega

/-- A point in two children determines the chunk position. -/
theorem eq_of_mem_child {a b a' b' : ℕ} (hr : 1 ≤ r) (ha : a < Q.numChunksX r)
    (hb : b < Q.numChunksY r) (ha' : a' < Q.numChunksX r) (hb' : b' < Q.numChunksY r)
    {p : ℤ × ℤ} (hp : p ∈ (Q.child r a b).toFinset) (hp' : p ∈ (Q.child r a' b').toFinset) :
    a = a' ∧ b = b' := by
  rw [mem_child hr ha hb] at hp
  rw [mem_child hr ha' hb'] at hp'
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  constructor <;> by_contra h <;> rcases Nat.lt_or_gt_of_ne h with h | h <;> zify at h <;>
    nlinarith

/-- **Neighbors of a padded child.** If a point of the child at `(a', b')` lies in the
padding `C r` of the child at `(a, b)`, the positions differ by at most `C` along each axis.
Source: `02-initial.tex`, lines 625–628. -/
theorem dist_le_of_mem_child_dilate {a b a' b' C : ℕ} (hr : 1 ≤ r) (ha' : a' < Q.numChunksX r)
    (hb' : b' < Q.numChunksY r)
    {p : ℤ × ℤ} (hp : p ∈ (Q.child r a' b').toFinset)
    (hp' : p ∈ ((Q.child r a b).dilate (C * r)).toFinset) :
    a' ≤ a + C ∧ a ≤ a' + C ∧ b' ≤ b + C ∧ b ≤ b' + C := by
  rw [mem_child hr ha' hb'] at hp
  rw [mem_dilate] at hp'
  simp only [child] at hp'
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  push_cast at hp'
  have h1 : (a' : ℤ) * r < (a + C + 1) * r := by
    rcases le_total (Q.x₀ + ↑a * ↑r) (min (Q.x₀ + ↑a * ↑r + ↑r - 1) Q.x₁) with h | h
    · rw [max_eq_right h] at hp'
      have := min_le_left (Q.x₀ + ↑a * ↑r + ↑r - 1) Q.x₁
      nlinarith
    · rw [max_eq_left h] at hp'
      nlinarith
  have h2 : (a : ℤ) * r < (a' + C + 1) * r := by nlinarith
  have h3 : (b' : ℤ) * r < (b + C + 1) * r := by
    rcases le_total (Q.y₀ + ↑b * ↑r) (min (Q.y₀ + ↑b * ↑r + ↑r - 1) Q.y₁) with h | h
    · rw [max_eq_right h] at hp'
      have := min_le_left (Q.y₀ + ↑b * ↑r + ↑r - 1) Q.y₁
      nlinarith
    · rw [max_eq_left h] at hp'
      nlinarith
  have h4 : (b : ℤ) * r < (b' + C + 1) * r := by nlinarith
  have := lt_of_mul_lt_mul_right h1 hr'.le
  have := lt_of_mul_lt_mul_right h2 hr'.le
  have := lt_of_mul_lt_mul_right h3 hr'.le
  have := lt_of_mul_lt_mul_right h4 hr'.le
  omega

/-- **Interior children.** A child at least `C` chunk positions from the first chunk and
`C + 2` from the last one along both axes has its padding `C r` inside the parent.
Source: `02-initial.tex`, lines 614–618. -/
theorem child_dilate_subset {a b C : ℕ} (hr : 1 ≤ r) (ha : a + C + 2 ≤ Q.numChunksX r)
    (hb : b + C + 2 ≤ Q.numChunksY r) (haC : C ≤ a) (hbC : C ≤ b) :
    ((Q.child r a b).dilate (C * r)).toFinset ⊆ Q.toFinset := by
  intro p hp
  have ha' : a < Q.numChunksX r := by omega
  have hb' : b < Q.numChunksY r := by omega
  have hsub := child_subset hr ha' hb'
  rw [mem_dilate] at hp
  rw [mem_toFinset]
  have hw := Q.width_eq
  have hh := Q.height_eq
  have hx1' := chunk_mul_le (n := Q.width) (a := a + C + 1) hr (by have := Q.hx; omega)
    (by unfold numChunksX at ha; omega)
  have hy1' := chunk_mul_le (n := Q.height) (a := b + C + 1) hr (by have := Q.hy; omega)
    (by unfold numChunksY at hb; omega)
  push_cast at hx1' hy1'
  have hCa : (C : ℤ) * r ≤ a * r := by exact_mod_cast Nat.mul_le_mul_right r haC
  have hCb : (C : ℤ) * r ≤ b * r := by exact_mod_cast Nat.mul_le_mul_right r hbC
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  simp only [child] at hp
  push_cast at hp
  refine ⟨by linarith [hp.1], ?_, by linarith [hp.2.2.1], ?_⟩
  · have := hp.2.1
    have : max (Q.x₀ + ↑a * ↑r) (min (Q.x₀ + ↑a * ↑r + ↑r - 1) Q.x₁) ≤
        Q.x₀ + ↑a * ↑r + ↑r - 1 := max_le (by linarith [hr1])
          (min_le_left _ _)
    nlinarith
  · have := hp.2.2.2
    have : max (Q.y₀ + ↑b * ↑r) (min (Q.y₀ + ↑b * ↑r + ↑r - 1) Q.y₁) ≤
        Q.y₀ + ↑b * ↑r + ↑r - 1 := max_le (by linarith [hr1])
          (min_le_left _ _)
    nlinarith

/-- A subrectangle has no larger size. -/
theorem size_le_of_subset {Q Q' : IntRect} (h : Q'.toFinset ⊆ Q.toFinset) :
    Q'.size ≤ Q.size := by
  have h0 := h ((mem_toFinset (p := (Q'.x₀, Q'.y₀))).mpr ⟨le_rfl, Q'.hx, le_rfl, Q'.hy⟩)
  have h1 := h ((mem_toFinset (p := (Q'.x₁, Q'.y₁))).mpr ⟨Q'.hx, le_rfl, Q'.hy, le_rfl⟩)
  rw [mem_toFinset] at h0 h1
  simp only [size]
  omega

end IntRect

/-- Subrectangles of no larger size of a safe rectangle are safe. -/
theorem IsSafe.mono {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {D₀ : ℕ} {Q Q' : IntRect}
    (h : IsSafe Λ A D₀ Q) (hsub : Q'.toFinset ⊆ Q.toFinset) (hsize : Q'.size ≤ Q.size) :
    IsSafe Λ A D₀ Q' := fun e he z hz p hp ↦
  lt_of_le_of_lt (Nat.mul_le_mul_left D₀ hsize) (h e he z hz p (hsub hp))

end TNLean.PEPS.AreaLaw
