import Mathlib.Combinatorics.SimpleGraph.Circulant
import TNLean.PEPS.InjectiveRegion

/-!
# Arcs of consecutive sites on the cycle graph

The first corollary after the general normal PEPS theorem (arXiv:1804.04964,
Section 3, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`) is set on
a closed chain of `n` sites: the sites are labelled `1, …, n` with
`n + 1 ≡ 1`, and the hypothesis is that blocking any `L` consecutive sites
gives an injective tensor.  The closed chain is the cycle graph on `Fin n`
(`SimpleGraph.cycleGraph`), and a block of consecutive sites is an arc: the
`len` consecutive vertices starting at `s` are the vertices `w` whose cyclic
distance from `s` is less than `len`.

This file records the arc geometry consumed by the cycle blocking
construction: membership, arcs described from their last site, complements of
arcs, the decomposition of a longer arc into a union of length-`L` arcs,
disjointness of two adjacent arcs, the unique nearest-neighbour pair joining
two adjacent arcs, and the resulting injectivity of all arcs of length at
least `L` from the injectivity of the length-`L` arcs.  These are the cycle
analogues of the torus rectangle lemmas of
`TNLean/PEPS/TorusRectangleRegion.lean`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, first corollary after the theorem labelled `normal`, lines
  1585--1622 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {n : ℕ}

/-! ### Cyclic distance arithmetic

The arc computations reduce to natural-number arithmetic through the
if-then-else form of the value of a difference in `Fin n`.  This is the
`ℕ`-valued counterpart of `Fin.intCast_val_sub_eq_sub_add_ite`. -/

/-- The value of a difference in `Fin n`: the plain difference when the
subtrahend value is not larger, and the wrapped difference otherwise. -/
theorem val_sub_eq_ite (u v : Fin n) :
    (u - v).val = if v.val ≤ u.val then u.val - v.val else u.val + n - v.val := by
  have h := Fin.intCast_val_sub_eq_sub_add_ite u v
  simp only [Fin.le_def] at h
  have hu := u.isLt
  split at h <;> split <;> omega

/-! ### Arcs of consecutive vertices -/

/-- The arc of `len` consecutive vertices starting at `s`: the vertices `w`
whose cyclic distance from `s` is less than `len`.  This is the block of `len`
consecutive sites of the source corollary, read clockwise from `s`.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`. -/
def cycleArcFrom (s : Fin n) (len : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun w => (w - s).val < len

@[simp] theorem mem_cycleArcFrom {s w : Fin n} {len : ℕ} :
    w ∈ cycleArcFrom s len ↔ (w - s).val < len := by
  simp [cycleArcFrom]

/-- The arc of `len` consecutive vertices ending at `t`: the vertices `w`
whose cyclic distance to `t` is less than `len`.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`. -/
def cycleArcTo (t : Fin n) (len : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun w => (t - w).val < len

@[simp] theorem mem_cycleArcTo {t w : Fin n} {len : ℕ} :
    w ∈ cycleArcTo t len ↔ (t - w).val < len := by
  simp [cycleArcTo]

/-- A nonempty arc contains its first vertex. -/
theorem start_mem_cycleArcFrom {s : Fin n} {len : ℕ} (hlen : 0 < len) :
    s ∈ cycleArcFrom s len := by
  simp [val_sub_eq_ite, hlen]

/-- A nonempty arc contains its last vertex. -/
theorem last_mem_cycleArcTo {t : Fin n} {len : ℕ} (hlen : 0 < len) :
    t ∈ cycleArcTo t len := by
  simp [val_sub_eq_ite, hlen]

/-- An arc described from its last vertex is the arc starting `len - 1`
vertices earlier. -/
theorem cycleArcTo_eq_cycleArcFrom {t : Fin n} {len : ℕ} (hlen : 0 < len) (hn : len ≤ n) :
    cycleArcTo t len = cycleArcFrom (t - ⟨len - 1, by omega⟩) len := by
  ext w
  simp only [mem_cycleArcTo, mem_cycleArcFrom, val_sub_eq_ite]
  have hw := w.isLt
  have ht := t.isLt
  split_ifs <;> omega

/-- The complement of an arc shorter than the whole cycle is the arc of the
remaining vertices, starting where the first arc ends. -/
theorem compl_cycleArcFrom {s : Fin n} {len : ℕ} (hlen : len < n) :
    Finset.univ \ cycleArcFrom s len = cycleArcFrom (s + ⟨len, hlen⟩) (n - len) := by
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_univ, mem_cycleArcFrom, true_and, not_lt,
    val_sub_eq_ite, Fin.val_add_eq_ite]
  have hw := w.isLt
  have hs := s.isLt
  split_ifs <;> omega

/-- An arc of length between `L` and `n` is the union of its length-`L`
subarcs.  This realizes a longer block of consecutive sites as a union of
length-`L` blocks, the shape to which the source's union lemma applies.

Source: arXiv:1804.04964, Section 3, Lemma labelled `injective_union` and the
examples following it, lines 1322--1430 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem cycleArcFrom_eq_biUnion {s : Fin n} {L len : ℕ} (hL : 0 < L) (hlen : L ≤ len)
    (hn : len ≤ n) :
    cycleArcFrom s len =
      (Finset.univ.filter fun c : Fin n => c.val ≤ len - L).biUnion
        (fun c => cycleArcFrom (s + c) L) := by
  ext w
  simp only [mem_cycleArcFrom, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  have hw := w.isLt
  have hs := s.isLt
  constructor
  · intro hmem
    by_cases hsmall : (w - s).val ≤ len - L
    · refine ⟨w - s, hsmall, ?_⟩
      simp only [val_sub_eq_ite, Fin.val_add_eq_ite] at hmem hsmall ⊢
      split_ifs at hmem hsmall ⊢ <;> omega
    · refine ⟨⟨len - L, by omega⟩, le_refl _, ?_⟩
      simp only [val_sub_eq_ite, Fin.val_add_eq_ite] at hmem hsmall ⊢
      split_ifs at hmem hsmall ⊢ <;> omega
  · rintro ⟨c, hc, hwc⟩
    have hclt := c.isLt
    simp only [val_sub_eq_ite, Fin.val_add_eq_ite] at hwc ⊢
    split_ifs at hwc ⊢ <;> omega

/-! ### Injectivity of arcs of length at least `L`

If every length-`L` arc is injective and injectivity is closed under unions,
then every arc of length between `L` and `n` is injective, being a union of
length-`L` arcs.  This is the source's use of the union lemma to make longer
consecutive blocks injective. -/

/-- Every arc of length between `L` and `n` is injective when every length-`L`
arc is injective and injectivity is closed under unions.

Source: arXiv:1804.04964, Section 3, Lemma labelled `injective_union`, lines
1322--1404 of `Papers/1804.04964/paper_normal.tex`, applied to blocks of
consecutive sites. -/
theorem isInjective_cycleArcFrom_of_le {κ : RegionInjectivityData (Fin n)}
    (hUnion : RegionInjectivityUnionClosure κ) {L : ℕ}
    (harc : ∀ s : Fin n, κ.IsInjective (cycleArcFrom s L)) (hL : 0 < L)
    {len : ℕ} (hlen : L ≤ len) (hn : len ≤ n) (s : Fin n) :
    κ.IsInjective (cycleArcFrom s len) := by
  rw [cycleArcFrom_eq_biUnion hL hlen hn]
  have h0 : 0 < n := by omega
  exact hUnion.biUnion_injective
    ⟨⟨0, h0⟩, by simp⟩ _ (fun c _ => harc _)

/-- Every length-`L` arc described from its last vertex is injective when
every length-`L` arc is injective.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`. -/
theorem isInjective_cycleArcTo {κ : RegionInjectivityData (Fin n)} {L : ℕ}
    (harc : ∀ s : Fin n, κ.IsInjective (cycleArcFrom s L)) (hL : 0 < L)
    (hn : L ≤ n) (t : Fin n) :
    κ.IsInjective (cycleArcTo t L) := by
  rw [cycleArcTo_eq_cycleArcFrom hL hn]
  exact harc _

section NeZero

variable [NeZero n]

/-! ### The cycle graph in successor form

The cycle-graph adjacency of Mathlib is phrased through differences of
values; the blocking construction reads it as "one endpoint is the cyclic
successor of the other". -/

theorem val_one_of_two_le (hn : 2 ≤ n) : ((1 : Fin n) : ℕ) = 1 := by
  rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)

/-- Two vertices of the cycle graph are adjacent exactly when one is the
cyclic successor of the other. -/
theorem cycleGraph_adj_iff_add_one (hn : 3 ≤ n) {u w : Fin n} :
    (SimpleGraph.cycleGraph n).Adj u w ↔ u + 1 = w ∨ w + 1 = u := by
  have h1 := val_one_of_two_le (n := n) (by omega)
  rw [SimpleGraph.cycleGraph_adj']
  simp only [Fin.ext_iff, val_sub_eq_ite, Fin.val_add_eq_ite, h1]
  have hu := u.isLt
  have hw := w.isLt
  split_ifs <;> omega

/-- On a cycle of at least three vertices, no pair of vertices is each the
cyclic successor of the other. -/
theorem not_add_one_eq_and_add_one_eq (hn : 3 ≤ n) {u w : Fin n} :
    ¬(u + 1 = w ∧ w + 1 = u) := by
  have h1 := val_one_of_two_le (n := n) (by omega)
  simp only [Fin.ext_iff, Fin.val_add_eq_ite, h1]
  have hu := u.isLt
  have hw := w.isLt
  split_ifs <;> omega

/-! ### Two adjacent arcs around an edge

For the edge between a vertex `a` and its cyclic successor `a + 1`, the source
blocks the chain into the `L` sites ending at `a`, the `L` sites starting at
`a + 1`, and the remaining `n - 2L` sites. -/

/-- The `L` sites ending at `a` and the `L` sites starting at `a + 1` are
disjoint on a cycle of at least `2L` sites. -/
theorem disjoint_cycleArcTo_cycleArcFrom_add_one {a : Fin n} {L : ℕ} (hL : 0 < L)
    (hn : 2 * L ≤ n) :
    Disjoint (cycleArcTo a L) (cycleArcFrom (a + 1) L) := by
  have h1 := val_one_of_two_le (n := n) (by omega)
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [mem_cycleArcTo, mem_cycleArcFrom, val_sub_eq_ite, Fin.val_add_eq_ite, h1]
    at hw hw'
  have hwlt := w.isLt
  have ha := a.isLt
  split_ifs at hw hw' <;> omega

/-- The vertices outside the two adjacent length-`L` arcs around the edge from
`a` to `a + 1` form the arc of the remaining `n - 2L` consecutive sites. -/
theorem compl_cycleArcTo_union_cycleArcFrom_add_one {a : Fin n} {L : ℕ} (hL : 0 < L)
    (hn : 3 * L ≤ n) :
    Finset.univ \ (cycleArcTo a L ∪ cycleArcFrom (a + 1) L) =
      cycleArcFrom (a + 1 + ⟨L, by omega⟩) (n - 2 * L) := by
  have h1 := val_one_of_two_le (n := n) (by omega)
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, mem_cycleArcTo,
    mem_cycleArcFrom, true_and, val_sub_eq_ite, Fin.val_add_eq_ite, h1, not_or, not_lt]
  have hwlt := w.isLt
  have ha := a.isLt
  split_ifs <;> omega

/-- The only nearest-neighbour pair joining the `L` sites ending at `a` to the
`L` sites starting at `a + 1` is the pair `(a, a + 1)` itself: on a cycle of
at least `3L` sites the far ends of the two arcs are separated by the
remaining `n - 2L ≥ L` sites.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1622 of `Papers/1804.04964/paper_normal.tex`,
via the blocking of the proof of Theorem 3 (lines 1475--1500). -/
theorem eq_of_adj_mem_cycleArcTo_mem_cycleArcFrom {a u w : Fin n} {L : ℕ} (hL : 0 < L)
    (hn : 3 * L ≤ n) (hadj : u + 1 = w ∨ w + 1 = u)
    (hu : u ∈ cycleArcTo a L) (hw : w ∈ cycleArcFrom (a + 1) L) :
    u = a ∧ w = a + 1 := by
  have h1 := val_one_of_two_le (n := n) (by omega)
  simp only [mem_cycleArcTo, mem_cycleArcFrom, val_sub_eq_ite, Fin.val_add_eq_ite, h1]
    at hu hw
  simp only [Fin.ext_iff, Fin.val_add_eq_ite, h1] at hadj ⊢
  have hwlt := w.isLt
  have ha := a.isLt
  have hult := u.isLt
  constructor
  · split_ifs at hu hw hadj ⊢ <;> omega
  · split_ifs at hu hw hadj ⊢ <;> omega

/-! ### One-site comparison arcs

The general normal PEPS theorem asks, at every site, for two injective
regions with injective complements differing exactly at that site.  On the
cycle these are the `L + 1` sites starting at `v` and the `L` sites starting
at `v + 1`. -/

/-- A vertex does not lie on the `L` sites starting at its cyclic successor
when `L < n`. -/
theorem self_notMem_cycleArcFrom_add_one {v : Fin n} {L : ℕ} (hL : 0 < L) (hn : L < n) :
    v ∉ cycleArcFrom (v + 1) L := by
  have h1 := val_one_of_two_le (n := n) (by omega)
  simp only [mem_cycleArcFrom, val_sub_eq_ite, Fin.val_add_eq_ite, h1, not_lt]
  have hv := v.isLt
  split_ifs <;> omega

/-- Away from `v`, the `L + 1` sites starting at `v` are the `L` sites
starting at `v + 1`. -/
theorem mem_cycleArcFrom_succ_iff_of_ne {v w : Fin n} {L : ℕ} (hn : 2 ≤ n) (hvw : w ≠ v) :
    (w ∈ cycleArcFrom v (L + 1)) ↔ w ∈ cycleArcFrom (v + 1) L := by
  have h1 := val_one_of_two_le (n := n) hn
  have hne : w.val ≠ v.val := fun h => hvw (Fin.ext h)
  simp only [mem_cycleArcFrom, val_sub_eq_ite, Fin.val_add_eq_ite, h1]
  have hv := v.isLt
  have hw := w.isLt
  split_ifs <;> omega

end NeZero

end PEPS
end TNLean
