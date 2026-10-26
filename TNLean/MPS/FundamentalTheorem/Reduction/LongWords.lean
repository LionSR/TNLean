/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# Long words in a triangular form

Let `(σ, g)` be a multi-block compression of a tensor `B` with `z` zero slots, and write
`B̂^w = g B^w g⁻¹` for the matrix of a word in the block coordinates. Expanding the product of the
block upper-triangular letters,
`(B̂^w)_{pq} = ∑_{p = p₀ ≤ p₁ ≤ ⋯ ≤ pₙ = q} B̂^{i₁}_{p₀p₁} ⋯ B̂^{iₙ}_{pₙ₋₁pₙ}`
is a sum over nondecreasing chains of positions. When no block slot sits between `p` and `q`,
every chain runs through zero slots only; a chain with `n ≥ z` steps then has an equal step,
whose factor is the zero diagonal block of a zero slot. Hence `(B̂^w)_{pq} = 0` (lecture note
MultiBlockUniqueness, Lemma 5.6 (Long words in a triangular
form)). In particular rows strictly after the last block slot and
columns strictly before the first block slot of `B̂^w` vanish.

The chain count is carried out once for an abstract block upper-triangular family whose diagonal
blocks vanish on an interval of positions (`Matrix.entry_evalWord_eq_zero_of_blockDiag'_eq_zero`).
For a strictly block upper-triangular family every diagonal block vanishes, and the lemma reduces
to the count `Matrix.entry_evalWord_eq_zero_of_lt` behind the nilpotency of the remainder.

## Main results

* `Matrix.entry_evalWord_eq_zero_of_blockDiag'_eq_zero`: the chain count.
* `MPSTensor.MultiBlockCompression.conjMatrix_evalWord_eq_zero_of_lt`: block triangularity of
  `B̂^w`.
* `MPSTensor.MultiBlockCompression.conjMatrix_evalWord_eq_zero_of_forall_notMem`: Lemma 5.6 (Long
  words in a triangular form),
  the vanishing of `(B̂^w)_{pq}` when no block slot sits in `[p, q]` and `|w| ≥ z`.
* `MPSTensor.MultiBlockCompression.conjMatrix_evalWord_eq_zero_of_forall_lt_row`,
  `MPSTensor.MultiBlockCompression.conjMatrix_evalWord_eq_zero_of_forall_lt_col`: rows after the
  last block slot and columns before the first block slot vanish, also in the form
  `conjMatrix_evalWord_eq_zero_of_maxSlotPosition_lt` and
  `conjMatrix_evalWord_eq_zero_of_lt_minSlotPosition`.

## References

Lecture note MultiBlockUniqueness, Section 5, Lemma 5.6 (Long words in a triangular form) and Figure
2.
-/

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ} {d r : ℕ} {b : o → Fin r}

/-- **The chain count** (lecture note MultiBlockUniqueness, proof of Lemma 5.6 (Long words in a
triangular form)). Let `T` be a
family of block upper-triangular matrices for an injective labelling `b` of the blocks by
positions. If every block at a position between those of `x` and `y` has zero diagonal block in
every letter, and the word is longer than the distance from the position of `x` to that of `y`,
then the `(x, y)` entry of the word vanishes: every nondecreasing chain of positions from `x` to
`y` has an equal step, whose factor is a zero diagonal block. -/
theorem entry_evalWord_eq_zero_of_blockDiag'_eq_zero (hb : Function.Injective b)
    {T : Fin d → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hT : ∀ i, (T i).BlockTriangular fun x => b x.1) :
    ∀ (w : List (Fin d)) (x y : Σ k, Fin (n k)),
      (∀ k, b x.1 ≤ b k → b k ≤ b y.1 → ∀ i, (T i).blockDiag' k = 0) →
      (b y.1 : ℕ) < (b x.1 : ℕ) + w.length → evalWord T w x y = 0 := by
  intro w
  induction w with
  | nil =>
      intro x y _ h
      simp only [List.length_nil, Nat.add_zero] at h
      have hxy : x ≠ y := by
        rintro rfl
        exact absurd h (lt_irrefl _)
      simp [evalWord, hxy]
  | cons i w' ih =>
      intro x y hdiag h
      simp only [List.length_cons] at h
      rcases lt_or_ge (b y.1) (b x.1) with hyx | hxy
      · exact blockTriangular_evalWord hT (i :: w') hyx
      simp only [evalWord, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      rcases lt_trichotomy (b z.1) (b x.1) with hzx | hzx | hzx
      · rw [hT i hzx, zero_mul]
      · obtain ⟨kz, jz⟩ := z
        obtain ⟨kx, jx⟩ := x
        obtain rfl : kz = kx := hb hzx
        have h0 := congrFun (congrFun (hdiag kz le_rfl hxy i) jx) jz
        rw [blockDiag'_apply, zero_apply] at h0
        rw [h0, zero_mul]
      · have hzx' : (b x.1 : ℕ) < (b z.1 : ℕ) := Fin.lt_def.mp hzx
        have hzy : (b y.1 : ℕ) < (b z.1 : ℕ) + w'.length := by omega
        rw [ih z y (fun k hk hk' => hdiag k (hzx.le.trans hk) hk') hzy, mul_zero]

end Matrix

namespace MPSTensor

namespace MultiBlockCompression

variable {d DB : ℕ} {ι : Type*} {D : ι → ℕ} [DecidableEq ι] {B : MPSTensor d DB}
  {S : Finset ι} {C : ∀ s, MPSTensor d (D s)} (P : MultiBlockCompression B S C)

/-- **Block triangularity of a word** in the coordinates of a multi-block compression: the
entry `(B̂^w)_{xy}` vanishes when `x` sits at a later position than `y`. -/
theorem conjMatrix_evalWord_eq_zero_of_lt (w : List (Fin d)) {x y : BlockSpace D S P.z}
    (hyx : P.ord y.1 < P.ord x.1) : conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 := by
  rw [← evalWord_conjMatrix]
  exact Matrix.blockTriangular_evalWord P.triangular w hyx

/-- If every position in `[p, q]` carries a zero slot, the interval has at most `z` positions. -/
theorem le_add_z_of_forall_notMem {p q : Fin (S.card + P.z)}
    (hS : ∀ s : {s // s ∈ S}, P.ord (Sum.inl s) ∉ Set.Icc p q) :
    (q : ℕ) + 1 ≤ p + P.z := by
  have hsub : Finset.Icc p q ⊆ Finset.univ.image fun t : Fin P.z => P.ord (Sum.inr t) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_image]
    rcases hk : P.ord.symm m with s | t
    · exact absurd (by rw [← hk, Equiv.apply_symm_apply]; exact hm) (hS s)
    · exact ⟨t, Finset.mem_univ _, by rw [← hk, Equiv.apply_symm_apply]⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Fin.card_Icc, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- **Long words in a triangular form** (lecture note MultiBlockUniqueness, Lemma 5.6 (Long words in
a triangular form)). For a
word with `|w| ≥ z`, the entry `(B̂^w)_{xy}` of the word in the block coordinates vanishes
unless some block slot sits at a position `m` with `p ≤ m ≤ q`, where `p` and `q` are the
positions of `x` and `y`. -/
theorem conjMatrix_evalWord_eq_zero_of_forall_notMem (w : List (Fin d)) (hw : P.z ≤ w.length)
    {x y : BlockSpace D S P.z}
    (hS : ∀ s : {s // s ∈ S}, P.ord (Sum.inl s) ∉ Set.Icc (P.ord x.1) (P.ord y.1)) :
    conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 := by
  rw [← evalWord_conjMatrix]
  refine Matrix.entry_evalWord_eq_zero_of_blockDiag'_eq_zero P.ord.injective P.triangular w x y
    ?_ ?_
  · rintro (s | t) hk hk' i
    · exact absurd ⟨hk, hk'⟩ (hS s)
    · exact P.unmatched i t
  · have := P.le_add_z_of_forall_notMem hS
    omega

/-- **Rows after the last block slot vanish** (lecture note MultiBlockUniqueness, Lemma 5.6 (Long
words in a triangular form),
`B^w ℂ^{D_B} ⊆ M_{k_max}`, in coordinates). For `|w| ≥ z`, the row of `B̂^w` at a coordinate
whose position is later than that of every block slot is zero. -/
theorem conjMatrix_evalWord_eq_zero_of_forall_lt_row (w : List (Fin d)) (hw : P.z ≤ w.length)
    {x : BlockSpace D S P.z} (hx : ∀ s : {s // s ∈ S}, P.ord (Sum.inl s) < P.ord x.1)
    (y : BlockSpace D S P.z) : conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 :=
  P.conjMatrix_evalWord_eq_zero_of_forall_notMem w hw fun s hs => (hx s).not_ge hs.1

/-- **Columns before the first block slot vanish** (lecture note MultiBlockUniqueness,
Lemma 5.6 (Long words in a triangular form), `B^w M_{k_min - 1} = 0`, in
coordinates). For `|w| ≥ z`, the column of `B̂^w` at a
coordinate whose position is earlier than that of every block slot is zero. -/
theorem conjMatrix_evalWord_eq_zero_of_forall_lt_col (w : List (Fin d)) (hw : P.z ≤ w.length)
    {y : BlockSpace D S P.z} (hy : ∀ s : {s // s ∈ S}, P.ord y.1 < P.ord (Sum.inl s))
    (x : BlockSpace D S P.z) : conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 :=
  P.conjMatrix_evalWord_eq_zero_of_forall_notMem w hw fun s hs => (hy s).not_ge hs.2

/-- The last position carrying a block slot (`k_max` of lecture note MultiBlockUniqueness,
Lemma 5.6 (Long words in a triangular form)). -/
def maxSlotPosition (hS : S.Nonempty) : Fin (S.card + P.z) :=
  S.attach.sup' (Finset.attach_nonempty_iff.mpr hS) fun s => P.ord (Sum.inl s)

/-- The first position carrying a block slot (`k_min` of lecture note MultiBlockUniqueness,
Lemma 5.6 (Long words in a triangular form)). -/
def minSlotPosition (hS : S.Nonempty) : Fin (S.card + P.z) :=
  S.attach.inf' (Finset.attach_nonempty_iff.mpr hS) fun s => P.ord (Sum.inl s)

/-- Rows of `B̂^w` at positions after `k_max` vanish for `|w| ≥ z` (lecture note
MultiBlockUniqueness, Lemma 5.6 (Long words in a triangular form)). -/
theorem conjMatrix_evalWord_eq_zero_of_maxSlotPosition_lt (hS : S.Nonempty) (w : List (Fin d))
    (hw : P.z ≤ w.length) {x : BlockSpace D S P.z} (hx : P.maxSlotPosition hS < P.ord x.1)
    (y : BlockSpace D S P.z) : conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 :=
  P.conjMatrix_evalWord_eq_zero_of_forall_lt_row w hw
    (fun s => (Finset.le_sup' (fun s => P.ord (Sum.inl s)) (Finset.mem_attach S s)).trans_lt hx) y

/-- Columns of `B̂^w` at positions before `k_min` vanish for `|w| ≥ z` (lecture note
MultiBlockUniqueness, Lemma 5.6 (Long words in a triangular form)). -/
theorem conjMatrix_evalWord_eq_zero_of_lt_minSlotPosition (hS : S.Nonempty) (w : List (Fin d))
    (hw : P.z ≤ w.length) {y : BlockSpace D S P.z} (hy : P.ord y.1 < P.minSlotPosition hS)
    (x : BlockSpace D S P.z) : conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 :=
  P.conjMatrix_evalWord_eq_zero_of_forall_lt_col w hw
    (fun s => hy.trans_le (Finset.inf'_le (fun s => P.ord (Sum.inl s)) (Finset.mem_attach S s))) x

end MultiBlockCompression

end MPSTensor
