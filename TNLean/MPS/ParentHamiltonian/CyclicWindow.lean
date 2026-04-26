/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Cyclic window infrastructure for periodic MPS chains

This file provides the infrastructure for restricting N-site quantum states to
cyclic windows of L consecutive sites on a periodic chain.

## Main results

* `MPSTensor.contiguous_mem_groundSpace` — iterated intersection:
  non-wrapping window conditions imply membership in the open-chain ground space.
* `MPSTensor.cyclicWindowSupport` and `MPSTensor.cyclicWindowsOverlap` — the
  support and overlap predicate for translated cyclic windows.
* `MPSTensor.cyclicWindowsOverlap_card_le` — each cyclic window overlaps at most
  `2 * (L - 1)` other cyclic windows when `2 * L ≤ N`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Contiguous (non-wrapping) window extraction -/

/-- Assemble an N-site configuration by placing window values `σ` at
contiguous sites `[s, s+1, ..., s+M-1]` and using `τ` for the remaining sites. -/
def contiguousCfg {N : ℕ} (s M : ℕ)
    (σ : Fin M → Fin d) (τ : Fin N → Fin d) : Fin N → Fin d :=
  fun k => if h : s ≤ k.val ∧ k.val < s + M
           then σ ⟨k.val - s, by omega⟩
           else τ k

/-- Linear restriction to a contiguous block `[s, s+1, ..., s+M-1]`. -/
def contiguousRestrictₗ {N : ℕ} (s M : ℕ) (_hsM : s + M ≤ N)
    (τ : Fin N → Fin d) : NSiteSpace d N →ₗ[ℂ] NSiteSpace d M where
  toFun ψ σ := ψ (contiguousCfg s M σ τ)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem contiguousRestrictₗ_apply {N : ℕ} (s M : ℕ) (hsM : s + M ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (σ : Fin M → Fin d) :
    contiguousRestrictₗ s M hsM τ ψ σ = ψ (contiguousCfg s M σ τ) := rfl

/-- The contiguous config at position 0 with M = N covers all sites. -/
theorem contiguousCfg_zero_full {N : ℕ} (σ : Fin N → Fin d) (τ : Fin N → Fin d) :
    contiguousCfg (N := N) 0 N σ τ = σ := by
  ext ⟨k, hk⟩
  simp only [contiguousCfg, Nat.zero_le, true_and]
  simp [hk]

/-- Restricting the last site of a contiguous `(M+1)`-block peels off
the rightmost site and extends the outside config. -/
theorem contiguousRestrictₗ_restrictLast {N : ℕ} (s M : ℕ) (hsM1 : s + (M + 1) ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (j : Fin d) :
    restrictLast (contiguousRestrictₗ s (M + 1) hsM1 τ ψ) j =
    contiguousRestrictₗ s M (by omega) (Function.update τ ⟨s + M, by omega⟩ j) ψ := by
  ext σ
  simp only [restrictLast_apply, contiguousRestrictₗ_apply]
  congr 1; ext ⟨k, hk⟩
  simp only [contiguousCfg]
  by_cases hwin : s ≤ k ∧ k < s + M
  · -- k is in the smaller window [s, s+M)
    rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_pos hwin]
    have hcast : (⟨k - s, by omega⟩ : Fin (M + 1)) =
        Fin.castSucc (⟨k - s, by omega⟩ : Fin M) := by
      ext; simp [Fin.castSucc]
    rw [hcast, Fin.snoc_castSucc]
  · by_cases hbdy : k = s + M
    · -- k is at position s+M (the site being peeled off)
      rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_neg hwin]
      have hlast : (⟨k - s, by omega⟩ : Fin (M + 1)) = Fin.last M := by
        ext; simp [Fin.last]; omega
      rw [hlast, Fin.snoc_last]
      simp [Function.update, hbdy]
    · -- k is outside both windows
      rw [dif_neg (show ¬(s ≤ k ∧ k < s + (M + 1)) from by omega), dif_neg hwin]
      simp [Function.update, show ¬(k = s + M) from hbdy]

/-- Restricting the first site of a contiguous `(M+1)`-block peels off
the leftmost site and shifts the window start. -/
theorem contiguousRestrictₗ_restrictFirst {N : ℕ} (s M : ℕ) (hsM1 : s + (M + 1) ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (i : Fin d) :
    restrictFirst (contiguousRestrictₗ s (M + 1) hsM1 τ ψ) i =
    contiguousRestrictₗ (s + 1) M (by omega) (Function.update τ ⟨s, by omega⟩ i) ψ := by
  ext σ
  simp only [restrictFirst_apply, contiguousRestrictₗ_apply]
  congr 1; ext ⟨k, hk⟩
  simp only [contiguousCfg]
  by_cases hwin : s + 1 ≤ k ∧ k < s + 1 + M
  · -- k is in the shifted window [s+1, s+1+M)
    rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_pos hwin]
    have hsucc : (⟨k - s, by omega⟩ : Fin (M + 1)) =
        Fin.succ (⟨k - (s + 1), by omega⟩ : Fin M) := by
      ext; simp; omega
    rw [hsucc, Fin.cons_succ]
  · by_cases hbdy : k = s
    · -- k is at position s (the site being peeled off)
      rw [dif_pos (show s ≤ k ∧ k < s + (M + 1) from by omega), dif_neg hwin]
      have hzero : (⟨k - s, by omega⟩ : Fin (M + 1)) = 0 := by
        ext; simp; omega
      rw [hzero, Fin.cons_zero]
      simp [Function.update, hbdy]
    · -- k is outside both windows
      rw [dif_neg (show ¬(s ≤ k ∧ k < s + (M + 1)) from by omega), dif_neg hwin]
      simp [Function.update, show ¬(k = s) from hbdy]

/-! ### Iterated intersection: non-wrapping windows → open-chain membership -/

/-- If an N-site state `ψ` satisfies the L-site ground condition at all
non-wrapping contiguous positions `s` (meaning `s + L ≤ N`), then
`ψ ∈ groundSpace A N` (the open-chain ground space).

The proof works by induction on `k` from 0 to `N - L`: at each step, two
adjacent windows of size `L + k` at positions `s` and `s + 1` are combined
via the intersection property to form a window of size `L + k + 1`.

**Hypotheses:** `L ≥ 2` (from the intersection property) and `L ≤ N`. -/
theorem contiguous_mem_groundSpace {A : MPSTensor d D} (hA : IsInjective A)
    {L N : ℕ} (hL : 1 < L) (hLN : L ≤ N) [NeZero d]
    {ψ : NSiteSpace d N}
    (hwindow : ∀ (s : ℕ) (hs : s + L ≤ N)
      (τ : Fin N → Fin d),
        contiguousRestrictₗ s L hs τ ψ ∈ groundSpace A L) :
    ψ ∈ groundSpace A N := by
  -- Prove the stronger claim parametrized by M: for L ≤ M ≤ N, every
  -- contiguous restriction of size M lies in groundSpace A M.
  suffices claim : ∀ (M : ℕ) (hLM : L ≤ M) (hMN : M ≤ N)
      (s : ℕ) (hs : s + M ≤ N) (τ : Fin N → Fin d),
        contiguousRestrictₗ s M hs τ ψ ∈ groundSpace A M by
    -- Apply at M = N, s = 0 to get ψ ∈ G_N
    have h0 := claim N hLN le_rfl 0 (by omega) (fun _ => ⟨0, Fin.pos'⟩)
    rwa [show (contiguousRestrictₗ 0 N (by omega) (fun _ => ⟨0, Fin.pos'⟩) ψ) = ψ from by
      ext σ; simp [contiguousRestrictₗ_apply, contiguousCfg_zero_full]] at h0
  -- By strong induction on M
  intro M
  induction M with
  | zero => intro hLM; omega
  | succ M ih =>
    intro hLM hMN s hs τ
    by_cases hbase : M + 1 ≤ L
    · -- M + 1 = L (base case)
      have : M + 1 = L := by omega
      subst this
      exact hwindow s hs τ
    · -- M ≥ L, so intersection property applies
      push Not at hbase
      apply groundSpace_intersection hA (show 1 < M from by omega)
      · -- InLeftGround: restrict the last site
        intro j
        rw [contiguousRestrictₗ_restrictLast]
        exact ih (by omega) (by omega) s (by omega) _
      · -- InRightGround: restrict the first site
        intro i
        rw [contiguousRestrictₗ_restrictFirst]
        exact ih (by omega) (by omega) (s + 1) (by omega) _

/-! ### Cyclic window extraction -/

/-- The site obtained by moving `r` steps clockwise from `i` on the cyclic chain. -/
def cyclicForwardSite {N : ℕ} (i : Fin N) (r : ℕ) : Fin N :=
  ⟨(i.val + r) % N, Nat.mod_lt _ (Fin.pos i)⟩

/-- The site obtained by moving `r` steps counterclockwise from `i` on the cyclic chain. -/
def cyclicBackwardSite {N : ℕ} (i : Fin N) (r : ℕ) : Fin N :=
  ⟨(i.val + N - r % N) % N, Nat.mod_lt _ (Fin.pos i)⟩

/-- The support of the length-`L` cyclic window starting at `i`, represented as the
finite set of sites reached from `i` by offsets below `L`, modulo the chain
length.  If `L` is larger than the chain length, repeated visits to a site are
counted only once; the parent-Hamiltonian applications use `L ≤ N`. -/
def cyclicWindowSupport (N L : ℕ) (i : Fin N) : Finset (Fin N) :=
  (Finset.range L).image fun r => cyclicForwardSite i r

/-- Cyclic-window overlap predicate for length-`L` windows on `Fin N`.

Two windows overlap when their cyclic supports share at least one site.  This is
the locality relation for translated local terms at the two starting sites.  In
row-cardinality estimates, the diagonal term j = i is excluded. -/
def cyclicWindowsOverlap (N L : ℕ) (i j : Fin N) : Prop :=
  ∃ k : Fin N, k ∈ cyclicWindowSupport N L i ∧ k ∈ cyclicWindowSupport N L j

/-- The cyclic-window overlap relation is decidable on a finite chain. -/
instance cyclicWindowsOverlap_decidableRel (N L : ℕ) :
    DecidableRel (cyclicWindowsOverlap N L) := by
  intro i j
  unfold cyclicWindowsOverlap
  exact Fintype.decidableExistsFintype

/-- Clockwise neighbours of the cyclic window starting at `i` that can overlap it
properly. -/
private def cyclicWindowClockwiseNeighbours (N L : ℕ) (i : Fin N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin (L - 1))).image fun r => cyclicForwardSite i (r.val + 1)

/-- Counterclockwise neighbours of the cyclic window starting at `i` that can
overlap it properly. -/
private def cyclicWindowCounterclockwiseNeighbours (N L : ℕ) (i : Fin N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin (L - 1))).image fun r => cyclicBackwardSite i (r.val + 1)

/-- Assemble an N-site configuration from a cyclic window at position `i`
(covering sites `i, i+1, ..., i+L-1 mod N`) and outside values `τ`.
Site `k` gets the window value `σ(offset)` where `offset = (k - i + N) % N`
if `offset < L`, otherwise it gets `τ(k)`. -/
def cyclicCfg {N : ℕ} (_hN : 0 < N) (L : ℕ)
    (i : Fin N) (σ : Fin L → Fin d) (τ : Fin N → Fin d) : Fin N → Fin d :=
  fun k =>
    if h : (k.val + N - i.val) % N < L
    then σ ⟨(k.val + N - i.val) % N, h⟩
    else τ k

/-- If a site has cyclic offset `r` from `i`, then it is the site `i + r` modulo
`N`. -/
theorem eq_cyclic_site_of_offset_eq {N : ℕ} (hN : 0 < N) {i k : Fin N} {r : ℕ}
    (h : (k.val + N - i.val) % N = r) :
    k = ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩ := by
  ext
  by_cases hik : i.val ≤ k.val
  · have hoff : (k.val + N - i.val) % N = k.val - i.val := by
      have hsum : k.val + N - i.val = k.val - i.val + N := by omega
      rw [hsum, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hr_eq : r = k.val - i.val := by omega
    have hsum : i.val + r = k.val := by omega
    have hmod : (i.val + r) % N = k.val := by
      rw [hsum]
      exact Nat.mod_eq_of_lt k.isLt
    exact hmod.symm
  · have hoff : (k.val + N - i.val) % N = k.val + N - i.val := by
      exact Nat.mod_eq_of_lt (by omega)
    have hsum : i.val + r = k.val + N := by omega
    have hmod : (i.val + r) % N = k.val := by
      rw [hsum, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt k.isLt
    exact hmod.symm

/-- Membership in a cyclic-window support is equivalently the cyclic offset from
the starting site being smaller than the window length, in the non-repeating regime
`L ≤ N`. -/
theorem mem_cyclicWindowSupport_iff {N L : ℕ} (hLN : L ≤ N) (i k : Fin N) :
    k ∈ cyclicWindowSupport N L i ↔ ((k.val + N - i.val) % N < L) := by
  constructor
  · intro hk
    rw [cyclicWindowSupport, Finset.mem_image] at hk
    rcases hk with ⟨r, hrange, hr⟩
    have hrL : r < L := Finset.mem_range.mp hrange
    have hrN : r < N := Nat.lt_of_lt_of_le hrL hLN
    rw [← hr]
    change (((i.val + r) % N + N - i.val) % N) < L
    rw [offset_mod_eq i.isLt hrN]
    exact hrL
  · intro hk
    rw [cyclicWindowSupport, Finset.mem_image]
    let r := (k.val + N - i.val) % N
    refine ⟨r, Finset.mem_range.mpr hk, ?_⟩
    have hsite :=
      (eq_cyclic_site_of_offset_eq (Fin.pos i) (i := i) (k := k) (r := r) rfl).symm
    simpa [cyclicForwardSite, r] using hsite

@[simp]
theorem cyclicForwardSite_zero {N : ℕ} (i : Fin N) :
    cyclicForwardSite i 0 = i := by
  ext
  simp [cyclicForwardSite, Nat.mod_eq_of_lt i.isLt]

@[simp]
theorem cyclicForwardSite_forwardSite {N : ℕ} (i : Fin N) (a b : ℕ) :
    cyclicForwardSite (cyclicForwardSite i a) b = cyclicForwardSite i (a + b) := by
  ext
  simp only [cyclicForwardSite, Fin.val_mk]
  rw [Nat.mod_add_mod]
  congr 1
  omega

private theorem cyclicForwardSite_eq_mod_eq {N : ℕ} (i : Fin N) {a b : ℕ}
    (h : cyclicForwardSite i a = cyclicForwardSite i b) : a % N = b % N := by
  have hval := congrArg Fin.val h
  change (i.val + a) % N = (i.val + b) % N at hval
  have hmodEq : (i.val + a) ≡ (i.val + b) [MOD N] := by
    simpa [Nat.ModEq] using hval
  have hcancel : a ≡ b [MOD N] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl i.val) hmodEq
  simpa [Nat.ModEq] using hcancel

/-- Row-cardinality estimate for cyclic support overlap in the finite-overlap
regime used by the martingale proof.

If `2 * L ≤ N`, then every length-`L` cyclic window can meet only the `L - 1`
clockwise starts and the `L - 1` counterclockwise starts.  Thus, after erasing
the window itself, at most `2 * (L - 1)` translated local terms overlap it. -/
theorem cyclicWindowsOverlap_card_le {N L : ℕ} (hLN : 2 * L ≤ N) (hL : 1 < L)
    (i : Fin N) :
    ((Finset.univ.erase i).filter (fun j => cyclicWindowsOverlap N L i j)).card ≤
      2 * (L - 1) := by
  classical
  let cw := cyclicWindowClockwiseNeighbours N L i
  let ccw := cyclicWindowCounterclockwiseNeighbours N L i
  have hLNle : L ≤ N := by omega
  have hsubset :
      (Finset.univ.erase i).filter (fun j => cyclicWindowsOverlap N L i j) ⊆
        cw ∪ ccw := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rcases hj with ⟨hjerase, hoverlap⟩
    have hji : j ≠ i := Finset.ne_of_mem_erase hjerase
    rcases hoverlap with ⟨k, hki, hkj⟩
    rw [cyclicWindowSupport, Finset.mem_image] at hki hkj
    rcases hki with ⟨a, haRange, hka⟩
    rcases hkj with ⟨b, hbRange, hkb⟩
    have haL : a < L := Finset.mem_range.mp haRange
    have hbL : b < L := Finset.mem_range.mp hbRange
    have haN : a < N := lt_of_lt_of_le haL hLNle
    have hbN : b < N := lt_of_lt_of_le hbL hLNle
    have hEq : cyclicForwardSite i a = cyclicForwardSite j b := hka.trans hkb.symm
    let x := (j.val + N - i.val) % N
    have hxN : x < N := by
      dsimp [x]
      exact Nat.mod_lt _ (Fin.pos i)
    have hjx : j = cyclicForwardSite i x := by
      simpa [x, cyclicForwardSite] using
        (eq_cyclic_site_of_offset_eq (Fin.pos i) (i := i) (k := j) (r := x) rfl)
    have hEq' : cyclicForwardSite i a = cyclicForwardSite i (x + b) := by
      simpa [hjx, cyclicForwardSite_forwardSite] using hEq
    have hmod := cyclicForwardSite_eq_mod_eq i hEq'
    have hxb_mod : (x + b) % N = a := by
      rw [Nat.mod_eq_of_lt haN] at hmod
      exact hmod.symm
    by_cases hxb_lt : x + b < N
    · -- No wraparound: the clockwise offset `x` is a positive distance below `L`.
      have hsum : x + b = a := by
        rw [Nat.mod_eq_of_lt hxb_lt] at hxb_mod
        exact hxb_mod
      have hxpos : 0 < x := by
        by_contra hxzero
        push Not at hxzero
        have hx0 : x = 0 := by omega
        apply hji
        rw [hjx, hx0]
        simp
      have hxL : x < L := by omega
      have hrlt : x - 1 < L - 1 := by omega
      apply Finset.mem_union_left
      dsimp [cw, cyclicWindowClockwiseNeighbours]
      refine Finset.mem_image.mpr ⟨⟨x - 1, hrlt⟩, Finset.mem_univ _, ?_⟩
      have hstep : (⟨x - 1, hrlt⟩ : Fin (L - 1)).val + 1 = x := by
        simp
        omega
      simpa [hstep] using hjx.symm
    · -- Wraparound: the equivalent counterclockwise distance is `b - a`, below `L`.
      have hxb_ge : N ≤ x + b := Nat.le_of_not_gt hxb_lt
      have hxb_lt_two : x + b < 2 * N := by omega
      have hmod_sub : (x + b) % N = x + b - N := by
        rw [Nat.mod_eq_sub_mod hxb_ge]
        exact Nat.mod_eq_of_lt (by omega)
      have hsum : x + b - N = a := by
        rw [hmod_sub] at hxb_mod
        exact hxb_mod
      have hab : a < b := by omega
      have hdist_pos : 0 < b - a := by omega
      have hdist_lt : b - a < L := by omega
      have hdistN : b - a < N := lt_of_lt_of_le hdist_lt hLNle
      have hx_eq : x = N + a - b := by omega
      have hjback : j = cyclicBackwardSite i (b - a) := by
        rw [hjx]
        ext
        simp only [cyclicForwardSite, cyclicBackwardSite, Fin.val_mk]
        rw [Nat.mod_eq_of_lt hdistN, hx_eq]
        congr 1
        omega
      have hrlt : b - a - 1 < L - 1 := by omega
      apply Finset.mem_union_right
      dsimp [ccw, cyclicWindowCounterclockwiseNeighbours]
      refine Finset.mem_image.mpr ⟨⟨b - a - 1, hrlt⟩, Finset.mem_univ _, ?_⟩
      have hstep : (⟨b - a - 1, hrlt⟩ : Fin (L - 1)).val + 1 = b - a := by
        simp
        omega
      simpa [hstep] using hjback.symm
  have hcw_card : cw.card ≤ L - 1 := by
    dsimp [cw, cyclicWindowClockwiseNeighbours]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin (L - 1))))
      (f := fun r : Fin (L - 1) => cyclicForwardSite i (r.val + 1)))
  have hccw_card : ccw.card ≤ L - 1 := by
    dsimp [ccw, cyclicWindowCounterclockwiseNeighbours]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin (L - 1))))
      (f := fun r : Fin (L - 1) => cyclicBackwardSite i (r.val + 1)))
  calc
    ((Finset.univ.erase i).filter (fun j => cyclicWindowsOverlap N L i j)).card ≤
        (cw ∪ ccw).card := Finset.card_le_card hsubset
    _ ≤ cw.card + ccw.card := Finset.card_union_le cw ccw
    _ ≤ (L - 1) + (L - 1) := Nat.add_le_add hcw_card hccw_card
    _ = 2 * (L - 1) := by omega

/-- Linear restriction to a cyclic window at position `i`. -/
def cyclicRestrictₗ {N : ℕ} (hN : 0 < N) (L : ℕ)
    (i : Fin N) (τ : Fin N → Fin d) : NSiteSpace d N →ₗ[ℂ] NSiteSpace d L where
  toFun ψ σ := ψ (cyclicCfg hN L i σ τ)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem cyclicRestrictₗ_apply {N : ℕ} (hN : 0 < N) (L : ℕ)
    (i : Fin N) (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (σ : Fin L → Fin d) :
    cyclicRestrictₗ hN L i τ ψ σ = ψ (cyclicCfg hN L i σ τ) := rfl

/-- Restricting the final site of a cyclic `(L + 1)`-window peels off the site with
cyclic offset `L` and records its value in the outside configuration. -/
theorem cyclicRestrictₗ_restrictLast {N L : ℕ} (hN : 0 < N)
    (i : Fin N) (τ : Fin N → Fin d) (ψ : NSiteSpace d N) (j : Fin d) :
    restrictLast (cyclicRestrictₗ hN (L + 1) i τ ψ) j =
      cyclicRestrictₗ hN L i
        (fun k => if (k.val + N - i.val) % N = L then j else τ k) ψ := by
  ext σ
  simp only [restrictLast_apply, cyclicRestrictₗ_apply]
  congr 1
  ext k
  simp only [cyclicCfg]
  by_cases hsmall : (k.val + N - i.val) % N < L
  · rw [dif_pos (Nat.lt_trans hsmall (Nat.lt_succ_self L)), dif_pos hsmall]
    simp [Fin.snoc, hsmall]
  · rw [dif_neg hsmall]
    by_cases hlast : (k.val + N - i.val) % N = L
    · rw [dif_pos (by omega : (k.val + N - i.val) % N < L + 1)]
      simp [Fin.snoc, hlast]
    · rw [dif_neg (by omega : ¬((k.val + N - i.val) % N < L + 1))]
      simp [hlast]

/-- For a non-wrapping window (`i + L ≤ N`), the cyclic config agrees with
the contiguous config. -/
theorem cyclicCfg_eq_contiguousCfg {N : ℕ} (hN : 0 < N) {L : ℕ} (hLN : L ≤ N)
    {i : Fin N} (hi : i.val + L ≤ N)
    (σ : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicCfg hN L i σ τ = contiguousCfg i.val L σ τ := by
  ext ⟨k, hk⟩
  simp only [cyclicCfg, contiguousCfg]
  -- Compute the offset
  by_cases h : i.val ≤ k ∧ k < i.val + L
  · -- k is in the non-wrapping window
    have hoff : (k + N - i.val) % N = k - i.val := by
      have : k + N - i.val = k - i.val + N := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hlt : (k + N - i.val) % N < L := by omega
    rw [dif_pos hlt, dif_pos h]
    congr 1; ext; simp [hoff]
  · -- k is outside
    have hh : ¬(i.val ≤ k ∧ k < i.val + L) := h
    have hoff_ge : ¬((k + N - i.val) % N < L) := by
      intro habs
      apply hh
      constructor
      · by_contra hlt
        push Not at hlt
        -- k < i, so (k + N - i) % N = k + N - i ≥ N - i ≥ L
        have : k + N - i.val < N := by omega
        rw [Nat.mod_eq_of_lt this] at habs
        omega
      · by_contra hge
        push Not at hge
        -- i ≤ k (since ¬(k < i) would be handled above)
        -- and k ≥ i + L
        have hile : i.val ≤ k := by
          by_contra hlt
          push Not at hlt
          have : k + N - i.val < N := by omega
          rw [Nat.mod_eq_of_lt this] at habs
          omega
        have : (k + N - i.val) % N = k - i.val := by
          have : k + N - i.val = k - i.val + N := by omega
          rw [this, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        omega
    rw [dif_neg hoff_ge, dif_neg hh]

/-- The non-wrapping window condition from the cyclic definition implies
the contiguous window condition. -/
theorem cyclicRestrictₗ_eq_contiguousRestrictₗ {N : ℕ} (hN : 0 < N)
    {L : ℕ} (hLN : L ≤ N) {i : Fin N} (hi : i.val + L ≤ N)
    (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    cyclicRestrictₗ hN L i τ ψ = contiguousRestrictₗ i.val L (by omega) τ ψ := by
  ext σ
  simp [cyclicCfg_eq_contiguousCfg hN hLN hi]

end MPSTensor
