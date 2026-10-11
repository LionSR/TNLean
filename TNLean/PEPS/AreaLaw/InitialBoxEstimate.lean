/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialBuffer
import TNLean.PEPS.AreaLaw.RotatedChainRule
import TNLean.PEPS.AreaLaw.SafeBoxChildren
import TNLean.PEPS.AreaLaw.EntropyDimension
import QICLean.Analysis.ScaleRecurrence

/-!
# The initial safe-box estimate

`F_box(r)` is the supremum of `S_Ω(A ∩ Q)` over all finite-range Hamiltonians on finite
domains with gapped ground vectors, all cuts `A`, and all safe rectangles `Q` of size at most
`r`, at fixed `q, R, J, Δ` and safety parameter `D₀`. Proposition 3.3 of the area-law
manuscript bounds it by `C r^{1 + e₀}` with `e₀ ∈ (0, 1)`. The constants depend only
on `q, R, J, Δ` and work for every admissible safety parameter: the entropy decreases
as `D₀` increases, so the estimate at `D₀ = 2 * R + 11` suffices.

A safe parent of size at most `M r` is partitioned into at most `M²` children of size at most
`r`. With `P = 2 C_pad + 1`, color the children by their chunk positions modulo `P`; the
padding of a child meets only children of other colors. Averaging the entropy chain rule over
the `N = P²` cyclic rotations of the colors, each interior child receives the buffer discount
of Lemma 3.2 in one of the `N` orders. At most `2 (2 C_pad + 1) M` children are not interior.
This gives the scale recurrence
`F_box(M r) ≤ ((1 - p) M² + p · 2 (2 C_pad + 1) M) F_box(r) + C_buf M² r` with `p = 1/(2N)`,
which the QICLean iteration turns into a power bound.

The source averages over a uniformly random child order; the deterministic rotations give the
same lower bound `1/N` on the frequency of the buffer event.

## Main definitions

* `boxEntropy`: the function `F_box`.

## Main results

* `boxEntropy_le_of_scale`: the scale recurrence `eq:initial-box-recursion`.
* `exists_boxEntropy_le_rpow`: Proposition 3.3 (`prop:initial-box`).

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 3.3 (`prop:initial-box`), `02-initial.tex`, lines 588–669.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- The values `S_Ω(A ∩ Q)` entering `F_box(r)`. -/
def boxEntropyValues (q R : ℕ) (J Δ : ℝ) (D₀ r : ℕ) : Set ℝ :=
  {s | ∃ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J) (E₀ : ℝ) (Ω : StateSpace Λ q)
    (A : Finset (Site Λ)) (Q : IntRect), IsGappedGroundState Λ q h.operator E₀ Ω Δ ∧
      IsSafe Λ A D₀ Q ∧ Q.size ≤ r ∧ s = regionalEntropy Λ q Ω (rectRegion A Q)}

/-- **The safe-box entropy** `F_box(r)`: the supremum of `S_Ω(A ∩ Q)` over all admissible
Hamiltonians with gapped ground vectors, cuts, and safe rectangles of size at most `r`, at
fixed `q, R, J, Δ, D₀`. Source: `02-initial.tex`, lines 590–594. -/
noncomputable def boxEntropy (q R : ℕ) (J Δ : ℝ) (D₀ r : ℕ) : ℝ :=
  sSup (boxEntropyValues q R J Δ D₀ r)

variable {q R : ℕ} {J Δ : ℝ} {D₀ : ℕ}

/-- The number of sites of `A ∩ Q` is at most `size(Q)²`. -/
theorem card_rectRegion_le {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ)) (Q : IntRect) :
    (rectRegion A Q).card ≤ Q.size ^ 2 := by
  have h1 : (rectRegion A Q).card ≤ Q.toFinset.card :=
    Finset.card_le_card_of_injOn Subtype.val (fun x hx ↦ (mem_rectRegion.mp hx).2)
      Subtype.val_injective.injOn
  have h2 : Q.toFinset.card = Q.width * Q.height := by
    rw [IntRect.toFinset, Finset.card_product, Int.card_Icc, Int.card_Icc]; rfl
  rw [h2] at h1
  have := Nat.mul_le_mul Q.width_le_size' Q.height_le_size'
  rw [sq]; omega

/-- `F_box(r) ≤ r² log q` on its values. -/
theorem le_of_mem_boxEntropyValues (hq : 1 ≤ q) {r : ℕ} {s : ℝ}
    (hs : s ∈ boxEntropyValues q R J Δ D₀ r) : s ≤ (r : ℝ) ^ 2 * Real.log q := by
  obtain ⟨Λ, h, E₀, Ω, A, Q, hgs, -, hQ, rfl⟩ := hs
  refine (regionalEntropy_le_card_mul_log Λ q Ω hgs.1 _).trans ?_
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have : ((rectRegion A Q).card : ℝ) ≤ (r : ℝ) ^ 2 := by
    exact_mod_cast (card_rectRegion_le A Q).trans (Nat.pow_le_pow_left hQ 2)
  exact mul_le_mul_of_nonneg_right this hlog

theorem bddAbove_boxEntropyValues (hq : 1 ≤ q) (r : ℕ) :
    BddAbove (boxEntropyValues q R J Δ D₀ r) :=
  ⟨_, fun _ hs ↦ le_of_mem_boxEntropyValues hq hs⟩

theorem nonneg_of_mem_boxEntropyValues {r : ℕ} {s : ℝ}
    (hs : s ∈ boxEntropyValues q R J Δ D₀ r) : 0 ≤ s := by
  obtain ⟨Λ, h, E₀, Ω, A, Q, hgs, -, -, rfl⟩ := hs
  exact regionalEntropy_nonneg Λ q Ω hgs.1 _

theorem boxEntropy_nonneg (r : ℕ) : 0 ≤ boxEntropy q R J Δ D₀ r :=
  Real.sSup_nonneg fun _ hs ↦ nonneg_of_mem_boxEntropyValues hs

/-- `F_box(r) ≤ r² log q`. Source: `02-initial.tex`, line 594. -/
theorem boxEntropy_le_sq_mul_log (hq : 1 ≤ q) (r : ℕ) :
    boxEntropy q R J Δ D₀ r ≤ (r : ℝ) ^ 2 * Real.log q :=
  Real.sSup_le (fun _ hs ↦ le_of_mem_boxEntropyValues hq hs)
    (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast hq)))

/-- Every safe-box entropy is at most `F_box(r)`. -/
theorem regionalEntropy_le_boxEntropy (hq : 1 ≤ q) {Λ : Finset (ℤ × ℤ)}
    (h : LocalHamiltonian Λ q R J) {E₀ : ℝ} {Ω : StateSpace Λ q}
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) {A : Finset (Site Λ)} {Q : IntRect}
    (hsafe : IsSafe Λ A D₀ Q) {r : ℕ} (hQ : Q.size ≤ r) :
    regionalEntropy Λ q Ω (rectRegion A Q) ≤ boxEntropy q R J Δ D₀ r :=
  le_csSup (bddAbove_boxEntropyValues hq r) ⟨Λ, h, E₀, Ω, A, Q, hgs, hsafe, hQ, rfl⟩

/-- `F_box` is nondecreasing. -/
theorem boxEntropy_mono (hq : 1 ≤ q) : Monotone (boxEntropy q R J Δ D₀) := by
  intro r r' hrr
  refine Real.sSup_le (fun s hs ↦ ?_) (boxEntropy_nonneg r')
  obtain ⟨Λ, h, E₀, Ω, A, Q, hgs, hsafe, hQ, rfl⟩ := hs
  exact regionalEntropy_le_boxEntropy hq h hgs hsafe (hQ.trans hrr)

/-- The safe-box entropy decreases with the safety parameter. Increasing the threshold
in the safety condition (`02-initial.tex`, lines 220–228) reduces the collection of
rectangles in the supremum defining `F_box` (lines 590–594). -/
theorem boxEntropy_antitone (hq : 1 ≤ q) (r : ℕ) :
    Antitone (fun D₀ : ℕ => boxEntropy q R J Δ D₀ r) := by
  intro D₀ D₁ hD
  refine Real.sSup_le (fun s hs ↦ ?_) (boxEntropy_nonneg (D₀ := D₀) r)
  obtain ⟨Λ, h, E₀, Ω, A, Q, hgs, hsafe, hQ, rfl⟩ := hs
  exact regionalEntropy_le_boxEntropy hq h hgs
    (fun e he z hz p hp ↦
      (Nat.mul_le_mul_right Q.size hD).trans_lt (hsafe e he z hz p hp)) hQ

/-! ### Children of a safe parent -/

/-- Equal colors `(a mod P) P + (b mod P)` at chunk distance at most `C < P` along both axes
force equal positions. -/
theorem eq_of_color_eq {P a b a' b' C : ℕ} (hCP : C < P)
    (hcol : (a % P) * P + b % P = (a' % P) * P + b' % P)
    (h1 : a' ≤ a + C) (h2 : a ≤ a' + C) (h3 : b' ≤ b + C) (h4 : b ≤ b' + C) :
    a = a' ∧ b = b' := by
  have hP : 0 < P := by omega
  have hb : b % P < P := Nat.mod_lt _ hP
  have hb' : b' % P < P := Nat.mod_lt _ hP
  have hmb : b % P = b' % P := by
    have := congrArg (· % P) hcol
    simpa [Nat.add_mod, Nat.mul_mod_left, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hb'] using this
  have hma : a % P = a' % P := by
    rw [hmb] at hcol
    exact Nat.eq_of_mul_eq_mul_right hP (Nat.add_right_cancel hcol)
  -- equal residues at distance less than `P`
  have key : ∀ {x y : ℕ}, x % P = y % P → x ≤ y + C → y ≤ x + C → x = y :=
    fun hxy hx hy ↦ Nat.ModEq.eq_of_abs_lt hxy (abs_lt.mpr ⟨by omega, by omega⟩)
  exact ⟨key hma h2 h1, key hmb h4 h3⟩

/-- At most `2 C + 1` chunk positions in `[0, n)` violate `C ≤ a ∧ a + C + 2 ≤ n`. -/
theorem card_filter_not_interior_le (n C : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter fun a : Fin n ↦ ¬ (C ≤ a.val ∧ a.val + C + 2 ≤ n)).card
      ≤ 2 * C + 1 := by
  have hsub : ((Finset.univ : Finset (Fin n)).filter
      fun a : Fin n ↦ ¬ (C ≤ a.val ∧ a.val + C + 2 ≤ n)).map Fin.valEmbedding ⊆
      Finset.range C ∪ Finset.Ico (n - (C + 1)) n := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    have := a.isLt
    omega
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_map, Finset.card_range, Nat.card_Ico] at this
  omega

/-! ### The scale recurrence -/

/-- **One parent.** Let `C_pad ≥ 1` and `C_buf ≥ 0` be constants for which Lemma 3.2 holds.
For a safe parent `Q` of size at most `M r`, with `P = 2 C_pad + 1`, `N = P²` and
`p = 1/(2N)`,
`S(A ∩ Q) ≤ ((1 - p) M² + p · 2 (2 C_pad + 1) M) F_box(r) + C_buf M² r`.
Source: `02-initial.tex`, lines 606–646. -/
theorem regionalEntropy_rectRegion_le_of_children (hq : 1 ≤ q) {Cpad : ℕ} {Cbuf : ℝ}
    (hCbuf : 0 ≤ Cbuf)
    (hbuf : ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J) (E₀ : ℝ)
      (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
      ∀ (A : Finset (Site Λ)) (Q : IntRect), IsSafe Λ A D₀ Q →
      ∀ r : ℕ, 1 ≤ r → ∀ Q₀ : IntRect, Q₀.size ≤ r →
        (Q₀.dilate (Cpad * r)).toFinset ⊆ Q.toFinset →
        regionalEntropy Λ q Ω (rectRegion A Q₀ ∪
            (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀)) -
          regionalEntropy Λ q Ω (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀) ≤
        regionalEntropy Λ q Ω (rectRegion A Q₀) / 2 + Cbuf * r)
    {Λ : Finset (ℤ × ℤ)} (h : LocalHamiltonian Λ q R J) {E₀ : ℝ} {Ω : StateSpace Λ q}
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) {A : Finset (Site Λ)} {Q : IntRect}
    (hsafe : IsSafe Λ A D₀ Q) {M r : ℕ} (hr : 1 ≤ r) (hQ : Q.size ≤ M * r) :
    regionalEntropy Λ q Ω (rectRegion A Q) ≤
      ((1 - 1 / (2 * ((2 * Cpad + 1) ^ 2 : ℕ))) * M ^ 2 +
        1 / (2 * ((2 * Cpad + 1) ^ 2 : ℕ)) * (2 * (2 * Cpad + 1) * M)) *
          boxEntropy q R J Δ D₀ r + Cbuf * M ^ 2 * r := by
  classical
  set P : ℕ := 2 * Cpad + 1
  set N : ℕ := P ^ 2
  set nx := Q.numChunksX r
  set ny := Q.numChunksY r
  set F := boxEntropy q R J Δ D₀ r
  have hF : 0 ≤ F := boxEntropy_nonneg r
  have hnx : nx ≤ M := Q.numChunksX_le r hr hQ
  have hny : ny ≤ M := Q.numChunksY_le r hr hQ
  set ι := Fin nx × Fin ny
  set ch : ι → IntRect := fun i ↦ Q.child r i.1 i.2
  set Xs : ι → Finset (Site Λ) := fun i ↦ rectRegion A (ch i)
  set col : ι → ℕ := fun i ↦ ((i.1 : ℕ) % P) * P + (i.2 : ℕ) % P
  set good : Finset ι := Finset.univ.filter fun i ↦
    (Cpad ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) + Cpad + 2 ≤ nx) ∧ (Cpad ≤ (i.2 : ℕ) ∧ (i.2 : ℕ) + Cpad + 2 ≤ ny)
  set T : ι → Finset (Site Λ) := fun i ↦
    rectRegion A ((ch i).dilate (Cpad * r)) \ Xs i
  have hP : 0 < P := by omega
  have hcol : ∀ i, col i < N := fun i ↦ by
    have h1 := Nat.mod_lt (i.1 : ℕ) hP
    have h2 := Nat.mod_lt (i.2 : ℕ) hP
    simp only [col, N, sq]
    nlinarith
  have hsub : ∀ i : ι, (ch i).toFinset ⊆ Q.toFinset := fun i ↦
    IntRect.child_subset hr i.1.isLt i.2.isLt
  have hchsafe : ∀ i : ι, IsSafe Λ A D₀ (ch i) := fun i ↦
    hsafe.mono (hsub i) (IntRect.size_le_of_subset (hsub i))
  -- the children partition `A ∩ Q`
  have hunion : Finset.univ.biUnion Xs = rectRegion A Q := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Xs, mem_rectRegion]
    constructor
    · rintro ⟨i, hxA, hx⟩; exact ⟨hxA, hsub i hx⟩
    · rintro ⟨hxA, hx⟩
      obtain ⟨a, ha, b, hb, hab⟩ := IntRect.exists_mem_child hr hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hxA, hab⟩
  have hdisj : Pairwise fun i j ↦ Disjoint (Xs i) (Xs j) := by
    intro i j hij
    refine Finset.disjoint_left.mpr fun x hxi hxj ↦ hij ?_
    rw [mem_rectRegion] at hxi hxj
    obtain ⟨h1, h2⟩ := IntRect.eq_of_mem_child hr i.1.isLt i.2.isLt j.1.isLt j.2.isLt hxi.2 hxj.2
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  -- buffers of interior children lie in children of other colors
  have hT : ∀ i ∈ good, T i ⊆ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs := by
    intro i hi x hx
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [T, Finset.mem_sdiff, mem_rectRegion] at hx
    obtain ⟨⟨hxA, hxd⟩, hxi⟩ := hx
    have hxQ := IntRect.child_dilate_subset hr hi.1.2 hi.2.2 hi.1.1 hi.2.1 hxd
    obtain ⟨a, ha, b, hb, hab⟩ := IntRect.exists_mem_child hr hxQ
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_, mem_rectRegion.mpr ⟨hxA, hab⟩⟩
    intro hc
    obtain ⟨d1, d2, d3, d4⟩ := IntRect.dist_le_of_mem_child_dilate hr ha hb hab hxd
    obtain ⟨e1, e2⟩ := eq_of_color_eq (by omega) hc.symm d1 d2 d3 d4
    apply hxi
    simp only [Xs, ch, mem_rectRegion]
    exact ⟨hxA, by rw [e1, e2]; exact hab⟩
  have hbuf' : ∀ i ∈ good, regionalEntropy Λ q Ω (Xs i ∪ T i) - regionalEntropy Λ q Ω (T i) ≤
      regionalEntropy Λ q Ω (Xs i) / 2 + Cbuf * r := by
    intro i hi
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hbuf Λ h E₀ Ω hgs A Q hsafe r hr (ch i) (IntRect.size_child_le _ _ hr)
      (IntRect.child_dilate_subset hr hi.1.2 hi.2.2 hi.1.1 hi.2.1)
  have key := regionalEntropy_biUnion_le_rotations Ω hgs.1 Xs hdisj col hcol good T
    (Cbuf * r) hT hbuf'
  rw [hunion] at key
  -- bounds on the children
  have hXF : ∀ i, regionalEntropy Λ q Ω (Xs i) ≤ F := fun i ↦
    regionalEntropy_le_boxEntropy hq h hgs (hchsafe i) (IntRect.size_child_le _ _ hr)
  have hX0 : ∀ i, 0 ≤ regionalEntropy Λ q Ω (Xs i) := fun i ↦
    regionalEntropy_nonneg Λ q Ω hgs.1 _
  have hcard : (Finset.univ : Finset ι).card ≤ M ^ 2 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, sq]
    exact Nat.mul_le_mul hnx hny
  have hbad : (Finset.univ \ good).card ≤ 2 * (2 * Cpad + 1) * M := by
    have hsub' : Finset.univ \ good ⊆
        ((Finset.univ : Finset (Fin nx)).filter
            fun a : Fin nx ↦ ¬ (Cpad ≤ a.val ∧ a.val + Cpad + 2 ≤ nx)) ×ˢ Finset.univ ∪
          Finset.univ ×ˢ ((Finset.univ : Finset (Fin ny)).filter
            fun b : Fin ny ↦ ¬ (Cpad ≤ b.val ∧ b.val + Cpad + 2 ≤ ny)) := by
      intro i hi
      simp only [good, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and,
        not_and_or] at hi
      rcases hi with hi | hi
      · exact Finset.mem_union_left _ (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, Finset.mem_univ _⟩)
      · exact Finset.mem_union_right _ (Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    have h1 := card_filter_not_interior_le nx Cpad
    have h2 := card_filter_not_interior_le ny Cpad
    refine (Finset.card_le_card hsub').trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
    have := Nat.mul_le_mul h1 hny
    have := Nat.mul_le_mul hnx h2
    nlinarith
  -- assemble
  set p : ℝ := 1 / (2 * (N : ℝ))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_pow _ _ hP
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    simp only [p]; rw [div_le_one (by positivity)]; linarith
  have hsplit : ∑ i, regionalEntropy Λ q Ω (Xs i) -
      (∑ i ∈ good, regionalEntropy Λ q Ω (Xs i)) / (2 * N) =
      (1 - p) * ∑ i ∈ good, regionalEntropy Λ q Ω (Xs i) +
        ∑ i ∈ Finset.univ \ good, regionalEntropy Λ q Ω (Xs i) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ good)]
    simp only [p]
    field_simp
    ring
  have hg : ∑ i ∈ good, regionalEntropy Λ q Ω (Xs i) ≤ good.card * F := by
    rw [← nsmul_eq_mul]; exact Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ hXF i
  have hb : ∑ i ∈ Finset.univ \ good, regionalEntropy Λ q Ω (Xs i) ≤
      (Finset.univ \ good).card * F := by
    rw [← nsmul_eq_mul]; exact Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ hXF i
  have hgb : (good.card : ℝ) + (Finset.univ \ good).card ≤ M ^ 2 := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good)
    have : (((Finset.univ \ good).card + good.card : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
      rw [h1]; exact_mod_cast hcard
    push_cast at this
    linarith
  have hbad' : ((Finset.univ \ good).card : ℝ) ≤ 2 * (2 * Cpad + 1) * M := by
    exact_mod_cast hbad
  have hgood' : (good.card : ℝ) * (Cbuf * r) / N ≤ Cbuf * M ^ 2 * r := by
    rw [div_le_iff₀ (by linarith)]
    have hgM : (good.card : ℝ) ≤ M ^ 2 := by
      have : (0 : ℝ) ≤ (Finset.univ \ good).card := Nat.cast_nonneg _
      linarith
    have h0 : 0 ≤ Cbuf * r := by positivity
    calc (good.card : ℝ) * (Cbuf * r) ≤ M ^ 2 * (Cbuf * r) :=
          mul_le_mul_of_nonneg_right hgM h0
      _ ≤ M ^ 2 * (Cbuf * r) * N := le_mul_of_one_le_right (by positivity) hN1
      _ = Cbuf * M ^ 2 * r * N := by ring
  have hfinal : (1 - p) * (good.card * F) + (Finset.univ \ good).card * F ≤
      ((1 - p) * M ^ 2 + p * (2 * (2 * Cpad + 1) * M)) * F := by
    have : (1 - p) * (good.card * F) + (Finset.univ \ good).card * F =
        ((1 - p) * (good.card + (Finset.univ \ good).card) +
          p * (Finset.univ \ good).card) * F := by ring
    rw [this]
    gcongr
  rw [hsplit] at key
  have := mul_le_mul_of_nonneg_left hg (by linarith : 0 ≤ 1 - p)
  linarith

/-- **The scale recurrence** `eq:initial-box-recursion`: under the constants of Lemma 3.2,
`F_box(M r) ≤ ((1 - p) M² + p · 2 (2 C_pad + 1) M) F_box(r) + C_buf M² r` for `r ≥ 1`, where
`p = 1/(2 (2 C_pad + 1)²)`. Source: `02-initial.tex`, lines 629–646. -/
theorem boxEntropy_le_of_scale (hq : 1 ≤ q) {Cpad : ℕ} {Cbuf : ℝ} (hCbuf : 0 ≤ Cbuf)
    (hbuf : ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J) (E₀ : ℝ)
      (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
      ∀ (A : Finset (Site Λ)) (Q : IntRect), IsSafe Λ A D₀ Q →
      ∀ r : ℕ, 1 ≤ r → ∀ Q₀ : IntRect, Q₀.size ≤ r →
        (Q₀.dilate (Cpad * r)).toFinset ⊆ Q.toFinset →
        regionalEntropy Λ q Ω (rectRegion A Q₀ ∪
            (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀)) -
          regionalEntropy Λ q Ω (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀) ≤
        regionalEntropy Λ q Ω (rectRegion A Q₀) / 2 + Cbuf * r)
    (M : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    boxEntropy q R J Δ D₀ (M * r) ≤
      ((1 - 1 / (2 * ((2 * Cpad + 1) ^ 2 : ℕ))) * M ^ 2 +
        1 / (2 * ((2 * Cpad + 1) ^ 2 : ℕ)) * (2 * (2 * Cpad + 1) * M)) *
          boxEntropy q R J Δ D₀ r + Cbuf * M ^ 2 * r := by
  refine Real.sSup_le (fun s hs ↦ ?_) ?_
  · obtain ⟨Λ, h, E₀, Ω, A, Q, hgs, hsafe, hQ, rfl⟩ := hs
    exact regionalEntropy_rectRegion_le_of_children hq hCbuf hbuf h hgs hsafe hr hQ
  · have hF := boxEntropy_nonneg (q := q) (R := R) (J := J) (Δ := Δ) (D₀ := D₀) r
    have hp : (0 : ℝ) ≤ 1 / (2 * ((2 * Cpad + 1) ^ 2 : ℕ)) := by positivity
    have hp1 : 1 / (2 * (((2 * Cpad + 1) ^ 2 : ℕ) : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ ((2 * Cpad + 1) ^ 2 : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
      linarith
    have : 0 ≤ (1 - 1 / (2 * (((2 * Cpad + 1) ^ 2 : ℕ) : ℝ))) * M ^ 2 +
        1 / (2 * (((2 * Cpad + 1) ^ 2 : ℕ) : ℝ)) * (2 * (2 * Cpad + 1) * M) := by
      have : (0 : ℝ) ≤ 1 - 1 / (2 * (((2 * Cpad + 1) ^ 2 : ℕ) : ℝ)) := by linarith
      positivity
    positivity

/-- The safe-box estimate at a fixed safety parameter. This auxiliary form follows the
scale-recurrence argument of Proposition 3.3 (`prop:initial-box`, `02-initial.tex`,
lines 606–669). The estimate uniform in the safety parameter is stated separately below. -/
private theorem exists_boxEntropy_le_rpow_fixed (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) (D₀ : ℕ) (hD₀ : 2 * R + 10 < D₀) :
    ∃ C e₀ : ℝ, 0 < e₀ ∧ e₀ < 1 ∧
      ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ C * (r : ℝ) ^ (1 + e₀) := by
  obtain ⟨Cpad, hCpad, Cbuf, hCbuf, hbuf⟩ := exists_condEntropy_le_initialBuffer q R hq hJ hΔ
  set p : ℝ := 1 / (2 * (((2 * Cpad + 1) ^ 2 : ℕ) : ℝ))
  set M : ℕ := 8 * (Cpad + 1)
  set lam : ℝ := (1 - p / 2) * M ^ 2
  have hN1 : (1 : ℝ) ≤ ((2 * Cpad + 1) ^ 2 : ℕ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 / 2 := by
    simp only [p]; rw [div_le_div_iff₀ (by positivity) two_pos]; linarith
  have hM : 2 ≤ M := by omega
  have hC1 : (1 : ℝ) ≤ Cpad := by exact_mod_cast hCpad
  have hM' : (16 : ℝ) ≤ M := by simp only [M]; push_cast; linarith
  have hp34 : (3 / 4 : ℝ) ≤ 1 - p / 2 := by linarith
  have hMlam : (M : ℝ) < lam := by
    have h1 : (12 : ℝ) ≤ (1 - p / 2) * M := by nlinarith
    have h2 : (12 : ℝ) * M ≤ (1 - p / 2) * M * M :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : lam = (1 - p / 2) * M * M := by simp only [lam]; ring
    rw [h3]; linarith
  have hlamM2 : lam < (M : ℝ) ^ 2 := by
    have : 0 < (M : ℝ) ^ 2 := by positivity
    simp only [lam]; nlinarith
  have hF := boxEntropy_mono (q := q) (R := R) (J := J) (Δ := Δ) (D₀ := D₀) hq
  have hrec : ∀ r, 1 ≤ r → boxEntropy q R J Δ D₀ (M * r) ≤
      lam * boxEntropy q R J Δ D₀ r + Cbuf * M ^ 2 * r := by
    intro r hr
    refine (boxEntropy_le_of_scale hq hCbuf (hbuf D₀ hD₀) M hr).trans ?_
    have hF0 := boxEntropy_nonneg (q := q) (R := R) (J := J) (Δ := Δ) (D₀ := D₀) r
    gcongr
    -- `(1 - p) M² + p · 2 (2 C_pad + 1) M ≤ (1 - p/2) M²` since `2 (2 C_pad + 1) ≤ M/2`
    have hB : 2 * (2 * (Cpad : ℝ) + 1) * M ≤ (M : ℝ) ^ 2 / 2 := by
      have : 2 * (2 * (Cpad : ℝ) + 1) ≤ M / 2 := by
        simp only [M]; push_cast; linarith
      nlinarith
    change (1 - p) * M ^ 2 + p * (2 * (2 * Cpad + 1) * M) ≤ lam
    simp only [lam]
    nlinarith
  obtain ⟨C, hC⟩ := Entropy.exists_le_mul_rpow_of_scale_recurrence hF hM hMlam
    (by positivity) hrec
  have hexp := Entropy.one_lt_log_div_log_lt_two (by exact_mod_cast hM) hMlam hlamM2
  refine ⟨C, Real.log lam / Real.log M - 1, by linarith [hexp.1], by linarith [hexp.2],
    fun r hr ↦ ?_⟩
  rw [add_sub_cancel]
  exact hC r hr


/-- **Proposition 3.3: the initial safe-box estimate** (area-law manuscript,
`prop:initial-box`, `02-initial.tex`, lines 596–604). For local dimension `q ≥ 1`, range `R`,
term norm bound `J ≥ 0` and gap `Δ > 0`, there are constants `C` and `e₀ ∈ (0, 1)`,
depending only on `q, R, J, Δ`, such that for every safety parameter `D₀ > 2R + 10`
one has `F_box(r) ≤ C r^{1 + e₀}` for every `r ≥ 1`. -/
theorem exists_boxEntropy_le_rpow (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) :
    ∃ C e₀ : ℝ, 0 < e₀ ∧ e₀ < 1 ∧
      ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
        ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ C * (r : ℝ) ^ (1 + e₀) := by
  obtain ⟨C, e₀, he₀, he₀', hbound⟩ :=
    exists_boxEntropy_le_rpow_fixed q R hq hJ hΔ (2 * R + 11) (by omega)
  refine ⟨C, e₀, he₀, he₀', fun D₀ hD₀ r hr ↦ ?_⟩
  exact (boxEntropy_antitone (R := R) (J := J) (Δ := Δ) hq r
    (show 2 * R + 11 ≤ D₀ by omega)).trans (hbound r hr)

end TNLean.PEPS.AreaLaw
