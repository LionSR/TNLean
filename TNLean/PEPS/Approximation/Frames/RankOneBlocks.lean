/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EncodedFrame

/-!
# Rank-one operators on blocks of sites

The last step of the proof of Lemma 6.3 of the polynomial-PEPS manuscript reads a product of
normalized vectors and covectors on groups of sites, each group on at most two parties, as a
monomial allowed by Theorem 5.2. This file provides the operators of that reading.

* `EncodedFrame.RankOneBlock`: a block of sites split into a part `T` and a part `U`, with the
  complement `E`, and two unit vectors on `(T → Fin q) × (U → Fin q)`; its operator is
  `|v⟩⟨w|_{T ∪ U} ⊗ 1_E` (`RankOneBlock.op`, `RankOneBlock.op_apply`). Products of operators of
  pairwise disjoint blocks are computed entrywise (`RankOneBlock.prod_op_apply`).
* `EncodedFrame.zeroPair`, `EncodedFrame.exists_pairVec`: the zero basis vector of a block and a
  vector on the sites of a group read on its two parts.

## Main definitions

* `EncodedFrame.RankOneBlock`, `EncodedFrame.RankOneBlock.op`, `EncodedFrame.zeroPair`.

## Main results

* `EncodedFrame.RankOneBlock.op_apply`, `EncodedFrame.RankOneBlock.prod_op_apply`.
* `EncodedFrame.exists_pairVec`: a vector on the sites of a group read on its two parts.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 306–316; allowed monomials, `04-compression.tex`, lines 32–35.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

noncomputable section

open Matrix

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

variable (ι q) in
/-- A rank-one block: the sites outside `E`, split into `T` and `U = (T ∪ E)ᶜ`, carry the
rank-one map `|v⟩⟨w|`, with `v` and `w` vectors on `(T → Fin q) × (U → Fin q)`; the sites of
`E` are untouched. -/
structure RankOneBlock where
  /-- The first part of the block. -/
  T : Finset ι
  /-- The sites outside the block. -/
  E : Finset ι
  /-- The first part of the block lies in the block. -/
  disj : Disjoint T E
  /-- The output vector. -/
  ket : EuclideanSpace ℂ ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q))
  /-- The input vector. -/
  bra : EuclideanSpace ℂ ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q))

namespace RankOneBlock

variable (b : RankOneBlock ι q)

/-- The output vector read on a configuration of all sites. -/
def ketAt (c : ι → Fin q) : ℂ :=
  b.ket ((fun x : b.T => c x), (fun x : {v // v ∉ b.T ∪ b.E} => c x))

/-- The input vector read on a configuration of all sites. -/
def braAt (c : ι → Fin q) : ℂ :=
  b.bra ((fun x : b.T => c x), (fun x : {v // v ∉ b.T ∪ b.E} => c x))

/-- The operator `|v⟩⟨w|_{T ∪ U} ⊗ 1_E` of a block, entry by entry: the entry at `(c', c)` is
`v(c') \overline{w(c)}` when `c'` and `c` agree on `E`, and `0` otherwise. -/
def op : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  Matrix.of fun c' c ↦ if ∀ x ∈ b.E, c' x = c x then b.ketAt c' * star (b.braAt c) else 0

/-- The entries of the operator of a block. -/
theorem op_apply (c' c : ι → Fin q) :
    b.op c' c = if ∀ x ∈ b.E, c' x = c x then b.ketAt c' * star (b.braAt c) else 0 :=
  rfl

omit [Fintype ι] in
private theorem notMem_E_of_mem_T {x : ι} (hx : x ∈ b.T) : x ∉ b.E :=
  Finset.disjoint_left.mp b.disj hx

omit [Fintype ι] in
/-- Two configurations agreeing outside `E` agree on both parts of the block. -/
private theorem restrict_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) :
    ((fun x : b.T => c x) = fun x : b.T => c' x) ∧
      ((fun x : {v // v ∉ b.T ∪ b.E} => c x) = fun x : {v // v ∉ b.T ∪ b.E} => c' x) :=
  ⟨funext fun x => h x (b.notMem_E_of_mem_T x.2),
    funext fun x => h x fun hx => x.2 (Finset.mem_union_right _ hx)⟩

omit [Fintype ι] in
theorem ketAt_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) : b.ketAt c = b.ketAt c' := by
  obtain ⟨h₁, h₂⟩ := b.restrict_congr h
  rw [ketAt, ketAt, h₁, h₂]

omit [Fintype ι] in
theorem braAt_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) : b.braAt c = b.braAt c' := by
  obtain ⟨h₁, h₂⟩ := b.restrict_congr h
  rw [braAt, braAt, h₁, h₂]

/-- **Products of disjoint blocks.** If every site lies outside all blocks of the list but at
most one, the product of their operators has the entry `∏_b v_b(c') \overline{w_b(c)}` when `c'`
and `c` agree outside all blocks, and `0` otherwise. -/
theorem prod_op_apply : (bs : List (RankOneBlock ι q)) →
    bs.Pairwise (fun b b' => ∀ x, x ∈ b.E ∨ x ∈ b'.E) → (c' c : ι → Fin q) →
    (bs.map op).prod c' c = if ∀ x, (∀ b ∈ bs, x ∈ b.E) → c' x = c x then
      (bs.map fun b => b.ketAt c' * star (b.braAt c)).prod else 0
  | [], _, c', c => by
      have h : (c' = c) ↔ ∀ x, (∀ b ∈ ([] : List (RankOneBlock ι q)), x ∈ b.E) → c' x = c x :=
        ⟨fun h x _ => congrFun h x, fun h => funext fun x => h x fun b hb => absurd hb
          List.not_mem_nil⟩
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply, h]
  | b :: bs, hd, c', c => by
      have hdb : ∀ b' ∈ bs, ∀ x, x ∈ b.E ∨ x ∈ b'.E := (List.pairwise_cons.mp hd).1
      have ih := prod_op_apply bs (List.pairwise_cons.mp hd).2
      set c₀ : ι → Fin q := fun x => if x ∈ b.E then c' x else c x with hc₀
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply,
        Finset.sum_eq_single c₀ (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ _) h)]
      · rw [op_apply, ih, ite_eq_left fun x hx => by rw [hc₀]; simp [hx]]
        have hrest : ∀ x, (∀ b' ∈ bs, x ∈ b'.E) → c₀ x = c x ↔
            (∀ b' ∈ b :: bs, x ∈ b'.E) → c' x = c x := by
          intro x
          by_cases hx : x ∈ b.E
          · simp [hc₀, hx]
          · simp only [hc₀, hx, ite_false, List.mem_cons, forall_eq_or_imp, false_and,
              false_implies, iff_true]
            simp
        have hb : b.braAt c₀ = b.braAt c := b.braAt_congr fun x hx => by simp [hc₀, hx]
        have hk : (bs.map fun b' => b'.ketAt c₀ * star (b'.braAt c)) =
            bs.map fun b' => b'.ketAt c' * star (b'.braAt c) := by
          refine List.map_congr_left fun b' hb' => ?_
          rw [b'.ketAt_congr fun x hx => ?_]
          rcases hdb b' hb' x with h | h
          · simp [hc₀, h]
          · exact absurd h hx
        simp only [forall_congr' hrest, hb, hk, List.map_cons, List.prod_cons]
        split_ifs <;> ring
      · rw [op_apply, ih]
        split_ifs with h₁ h₂
        · refine absurd (funext fun x => ?_) ha
          by_cases hx : x ∈ b.E
          · rw [← h₁ x hx]
            simp [hc₀, hx]
          · rw [h₂ x fun b' hb' => (hdb b' hb' x).resolve_left hx]
            simp [hc₀, hx]
        all_goals simp

end RankOneBlock

/-- The basis vector of the zero configuration on `(T → Fin q) × (U → Fin q)`, the analogue of
`zeroVec` on the two parts of a block. -/
def zeroPair [NeZero q] (T E : Finset ι) :
    EuclideanSpace ℂ ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q)) :=
  EuclideanSpace.single (0, 0) 1

theorem norm_zeroPair [NeZero q] (T E : Finset ι) : ‖zeroPair (q := q) T E‖ = 1 := by
  simp [zeroPair]

/-- The zero basis vector read on a configuration: `1` if the configuration vanishes on
`T ∪ U`, and `0` otherwise. -/
theorem zeroPair_apply [NeZero q] (T E : Finset ι) (h : Disjoint T E) (c : ι → Fin q) :
    zeroPair (q := q) T E ((fun x : T => c x), (fun x : {v // v ∉ T ∪ E} => c x)) =
      if ∀ x ∉ E, c x = 0 then 1 else 0 := by
  rw [zeroPair, PiLp.single_apply]
  congr 1
  apply propext
  constructor
  · intro hc x hx
    by_cases hT : x ∈ T
    · exact congrFun (congrArg Prod.fst hc) ⟨x, hT⟩
    · exact congrFun (congrArg Prod.snd hc) ⟨x, by simp [hT, hx]⟩
  · intro hc
    refine Prod.ext (funext fun x => hc x (Finset.disjoint_left.mp h x.2))
      (funext fun x => hc x fun hx => x.2 (Finset.mem_union_right _ hx))

/-- **A vector on a group of sites, read on two parts.** Let the group be the set of sites
satisfying `O`, with complement `E`, and let `T` be part of it. Every vector `f` on the
configurations of the group is a vector of the same norm on `(T → Fin q) × (U → Fin q)`,
`U = (T ∪ E)ᶜ`, with the same values on every configuration. -/
theorem exists_pairVec (O : ι → Prop) [DecidablePred O] {T : Finset ι} (hT : ∀ x ∈ T, O x)
    (f : EuclideanSpace ℂ ({x // O x} → Fin q)) :
    ∃ v : EuclideanSpace ℂ
        ((T → Fin q) × ({v // v ∉ T ∪ Finset.univ.filter fun x => ¬O x} → Fin q)),
      ‖v‖ = ‖f‖ ∧ ∀ c : ι → Fin q,
        v ((fun x : T => c x),
          (fun x : {v // v ∉ T ∪ Finset.univ.filter fun x => ¬O x} => c x)) =
          f fun x => c x.1 := by
  set E := Finset.univ.filter fun x => ¬O x
  have hU : ∀ x : {x // O x}, x.1 ∉ T → x.1 ∉ T ∪ E := fun x hx => by
    simp [E, hx, x.2]
  have hO : ∀ x : {v // v ∉ T ∪ E}, O x.1 := fun x => by
    have : (x : ι) ∉ T ∪ E := x.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_not, E] at this
    exact this.2
  let e : ((T → Fin q) × ({v // v ∉ T ∪ E} → Fin q)) ≃ ({x // O x} → Fin q) :=
    { toFun := fun ab x => if hx : x.1 ∈ T then ab.1 ⟨x.1, hx⟩ else ab.2 ⟨x.1, hU x hx⟩
      invFun := fun d => (fun x => d ⟨x.1, hT x.1 x.2⟩, fun x => d ⟨x.1, hO x⟩)
      left_inv := fun ab => by
        refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
        · simp [x.2]
        · have hx : x.1 ∉ T := fun h => x.2 (Finset.mem_union_left _ h)
          simp [hx]
      right_inv := fun d => funext fun x => by
        by_cases hx : x.1 ∈ T <;> simp [hx] }
  refine ⟨WithLp.toLp 2 fun ab => f (e ab), ?_, fun c => ?_⟩
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp e (fun d => ‖f d‖ ^ 2)
  · change f (e _) = _
    refine congrArg (fun d => f d) (funext fun x => ?_)
    by_cases hx : x.1 ∈ T <;> simp [e, hx]

end TNLean.PEPS.EncodedFrame
