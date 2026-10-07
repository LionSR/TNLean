/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicRouting
import TNLean.PEPS.Approximation.RoutedContraction
import TNLean.PEPS.SquareLatticeGraph

/-!
# Folding the dyadic routing into the genuine square

The horizontal-then-vertical walks of the padded square `{0, …, N - 1} ^ 2` are folded into
the genuine `L × L` square by the reflection `f` in both coordinates. Folded walks are walks of
the open square-lattice graph, the fold fixes the genuine coordinates, and every edge of the
genuine square has at most four padded unit-edge preimages, so the folded congestion is at most
four times the padded congestion, counting repeated folded traversals.

Combined with the exact routed contraction, a party network on dyadic anchors with boundedly
many parties per block, bounded degree, and link separation bounded by a fixed multiple of the
endpoint scales is exactly a PEPS on the open `L × L` square-lattice graph. Its bond dimensions
are at most `(max D 1) ^ χ` when every link has dimension at most `D`, with
`χ = 8 (2 c + 1) B Δ` depending only on the separation constant `c`, the block bound `B` and
the degree bound `Δ`.

The source additionally records that the two endpoint scales of every link are equal or
adjacent; the bounds here do not use it, so it is not assumed.

## Main results

* `TNLean.PEPS.Approximation.foldedRouting_card_traversal_le`: the folded congestion bound,
  Lemma 8.2 `lem:routing`.
* `TNLean.PEPS.Approximation.exists_squarePEPS_of_dyadicRouting`: the routed party network is
  exactly a PEPS on the genuine square with bond dimension at most `D ^ χ`, equation
  `eq:final-bond`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.2 `lem:routing`, its proof, and equation
  `eq:final-bond`, `07-assembly.tex:102–177`.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Finset

variable {L : ℕ}

/-! ### Folding points and steps -/

/-- The fold of a padded point into the genuine square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:148–154`. -/
def foldVertex (hL : 0 < L) (q : ℕ × ℕ) : SquareLatticeVertex L L :=
  (⟨foldCoord L q.1, foldCoord_lt hL _⟩, ⟨foldCoord L q.2, foldCoord_lt hL _⟩)

/-- The fold fixes the genuine points: physical output coordinates are unchanged.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:124–126` and
`07-assembly.tex:158–159`. -/
theorem foldVertex_of_lt (hL : 0 < L) {q : ℕ × ℕ} (h1 : q.1 < L) (h2 : q.2 < L) :
    foldVertex hL q = (⟨q.1, h1⟩, ⟨q.2, h2⟩) := by
  simp [foldVertex, foldCoord_of_lt h1, foldCoord_of_lt h2]

/-- Folding a unit step of the padded square gives an edge of the genuine square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:155`. -/
theorem foldVertex_adj (hL : 0 < L) {p q : ℕ × ℕ} (hp : p.1 + 1 < 2 * L ∧ p.2 + 1 < 2 * L)
    (hq : q.1 + 1 < 2 * L ∧ q.2 + 1 < 2 * L) (h : IsUnitStep p q) :
    (squareLatticeGraph L L).Adj (foldVertex hL p) (foldVertex hL q) := by
  simp only [squareLatticeGraph_adj, squareLatticeHorizontalNeighbor,
    squareLatticeVerticalNeighbor, foldVertex, Fin.mk.injEq]
  rcases h with ⟨hy, hx | hx⟩ | ⟨hx, hy | hy⟩
  · have := foldCoord_succ (L := L) (x := p.1) (by omega)
    rw [hx] at this
    exact Or.inl ⟨by rw [hy], by omega⟩
  · have := foldCoord_succ (L := L) (x := q.1) (by omega)
    rw [hx] at this
    exact Or.inl ⟨by rw [hy], by omega⟩
  · have := foldCoord_succ (L := L) (x := p.2) (by omega)
    rw [hy] at this
    exact Or.inr ⟨by rw [hx], by omega⟩
  · have := foldCoord_succ (L := L) (x := q.2) (by omega)
    rw [hy] at this
    exact Or.inr ⟨by rw [hx], by omega⟩

/-- A padded unit step whose fold traverses the genuine horizontal edge from `(u, v)` to
`(u + 1, v)` traverses one of at most four padded horizontal unit edges.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:155–158`. -/
theorem exists_padded_horizontal {p q : ℕ × ℕ} (hp : p.1 + 1 < 2 * L ∧ p.2 + 1 < 2 * L)
    (hq : q.1 + 1 < 2 * L ∧ q.2 + 1 < 2 * L) (hs : IsUnitStep p q) {u v : ℕ}
    (h : (foldCoord L p.1 = u ∧ foldCoord L p.2 = v ∧
        foldCoord L q.1 = u + 1 ∧ foldCoord L q.2 = v) ∨
      (foldCoord L p.1 = u + 1 ∧ foldCoord L p.2 = v ∧
        foldCoord L q.1 = u ∧ foldCoord L q.2 = v)) :
    ∃ xy ∈ ({u, 2 * L - 3 - u} : Finset ℕ) ×ˢ ({v, 2 * (L - 1) - v} : Finset ℕ),
      IsUnitCrossing p q (xy.1, xy.2) (xy.1 + 1, xy.2) := by
  have hy := eq_or_eq_of_foldCoord_eq (L := L) (x := p.2) (u := v) (by omega) (by tauto)
  rcases hs with ⟨hpq, hx | hx⟩ | ⟨hx, _⟩
  · have := eq_or_eq_of_foldCoord_interval (L := L) (x := p.1) (u := u) (by omega)
      (by rw [hx]; tauto)
    refine ⟨(p.1, p.2), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simp only [mem_product, mem_insert, mem_singleton]; omega
    · ext <;> simp [← hx, hpq]
  · have := eq_or_eq_of_foldCoord_interval (L := L) (x := q.1) (u := u) (by omega)
      (by rw [hx]; tauto)
    refine ⟨(q.1, p.2), ?_, Or.inr ⟨?_, ?_⟩⟩
    · simp only [mem_product, mem_insert, mem_singleton]; omega
    · ext <;> simp [← hx]
    · ext <;> simp [hpq]
  · rw [hx] at h; omega

/-- A padded unit step whose fold traverses the genuine vertical edge from `(u, v)` to
`(u, v + 1)` traverses one of at most four padded vertical unit edges.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:155–158`. -/
theorem exists_padded_vertical {p q : ℕ × ℕ} (hp : p.1 + 1 < 2 * L ∧ p.2 + 1 < 2 * L)
    (hq : q.1 + 1 < 2 * L ∧ q.2 + 1 < 2 * L) (hs : IsUnitStep p q) {u v : ℕ}
    (h : (foldCoord L p.1 = u ∧ foldCoord L p.2 = v ∧
        foldCoord L q.1 = u ∧ foldCoord L q.2 = v + 1) ∨
      (foldCoord L p.1 = u ∧ foldCoord L p.2 = v + 1 ∧
        foldCoord L q.1 = u ∧ foldCoord L q.2 = v)) :
    ∃ xy ∈ ({u, 2 * (L - 1) - u} : Finset ℕ) ×ˢ ({v, 2 * L - 3 - v} : Finset ℕ),
      IsUnitCrossing p q (xy.1, xy.2) (xy.1, xy.2 + 1) := by
  have hx' := eq_or_eq_of_foldCoord_eq (L := L) (x := p.1) (u := u) (by omega) (by tauto)
  rcases hs with ⟨hy, _⟩ | ⟨hpq, hy | hy⟩
  · rw [hy] at h; omega
  · have := eq_or_eq_of_foldCoord_interval (L := L) (x := p.2) (u := v) (by omega)
      (by rw [hy]; tauto)
    refine ⟨(p.1, p.2), ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simp only [mem_product, mem_insert, mem_singleton]; omega
    · ext <;> simp [← hy, hpq]
  · have := eq_or_eq_of_foldCoord_interval (L := L) (x := q.2) (u := v) (by omega)
      (by rw [hy]; tauto)
    refine ⟨(p.1, q.2), ?_, Or.inr ⟨?_, ?_⟩⟩
    · simp only [mem_product, mem_insert, mem_singleton]; omega
    · ext <;> simp [← hy]
    · ext <;> simp [hpq]

/-- A product of two sets with at most two elements each has at most four elements. -/
private theorem card_pair_product_pair_le (a b c' e : ℕ) :
    #(({a, b} : Finset ℕ) ×ˢ ({c', e} : Finset ℕ)) ≤ 4 := by
  rw [card_product]
  exact le_trans (Nat.mul_le_mul (card_insert_le _ _) (card_insert_le _ _)) (by simp)

/-! ### The folded routing -/

namespace DyadicPlacement

variable {P : Type*} (A : DyadicPlacement P)

/-- Every dyadic block lies in the square of side `M`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:105–114`. -/
def InGrid (M : ℕ) : Prop :=
  ∀ p, 2 ^ A.scale p * (A.blockX p + 1) ≤ M ∧ 2 ^ A.scale p * (A.blockY p + 1) ≤ M

/-- The anchor of a party whose block lies in the square of side `M` lies in that square. -/
theorem anchor_lt {M : ℕ} (h : A.InGrid M) (p : P) :
    (A.anchor p).1 < M ∧ (A.anchor p).2 < M :=
  ⟨dyadicAnchor_lt (h p).1, dyadicAnchor_lt (h p).2⟩

end DyadicPlacement

variable {P Λ : Type*} [Fintype P] [DecidableEq P] [Fintype Λ] [DecidableEq Λ] {d : ℕ}

omit [Fintype P] [DecidableEq P] [Fintype Λ] [DecidableEq Λ] in
/-- A padded walk point lies in the padded square, hence below `2 L - 1`. -/
theorem linkRoute_lt (hL : 0 < L) (A : DyadicPlacement P) (src tgt : Λ → P)
    (hgrid : A.InGrid (paddedSide L)) (ℓ : Λ) {i : ℕ} (hi : i ≤ A.linkLength src tgt ℓ) :
    (A.linkRoute src tgt ℓ i).1 + 1 < 2 * L ∧ (A.linkRoute src tgt ℓ i).2 + 1 < 2 * L := by
  have hM := paddedSide_lt_two_mul hL
  have := hvRoute_lt (A.anchor_lt hgrid (src ℓ)) (A.anchor_lt hgrid (tgt ℓ)) hi
  unfold DyadicPlacement.linkRoute
  omega

/-- The padded horizontal-then-vertical walks folded into the genuine square, as a routing of
the party network on the open square-lattice graph. Party `p` sits at the fold of its anchor.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:128–161`. -/
def foldedRouting (hL : 0 < L) (N : PartyNetwork P Λ d) (A : DyadicPlacement P)
    (hgrid : A.InGrid (paddedSide L)) :
    Routing (squareLatticeGraph L L) N (fun p => foldVertex hL (A.anchor p)) where
  len := A.linkLength N.src N.tgt
  route ℓ i := foldVertex hL (A.linkRoute N.src N.tgt ℓ i)
  route_zero ℓ := by simp [DyadicPlacement.linkRoute]
  route_last ℓ := by
    simp [DyadicPlacement.linkRoute, DyadicPlacement.linkLength, hvRoute_hvLength]
  route_adj ℓ i :=
    foldVertex_adj hL (linkRoute_lt hL A _ _ hgrid ℓ (by simp only [Fin.val_castSucc]; omega))
      (linkRoute_lt hL A _ _ hgrid ℓ (by simp only [Fin.val_succ]; omega))
      (hvRoute_isUnitStep _ _ i.2)

omit [DecidableEq Λ] in
/-- **Lemma 8.2 (routing), folded congestion.** Under the dyadic hypotheses, every edge of the
genuine `L × L` square is traversed by at most `8 (2 c + 1) B Δ` steps of the folded walks,
counting repeated folded traversals. The constant depends only on `c`, `B` and `Δ`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.2 `lem:routing`,
`07-assembly.tex:122–161`. -/
theorem foldedRouting_card_traversal_le (hL : 0 < L) (N : PartyNetwork P Λ d)
    (A : DyadicPlacement P) (hgrid : A.InGrid (paddedSide L)) {B Δ c : ℕ}
    (hB : A.BlockBounded B) (hΔ : DyadicPlacement.DegreeBounded N.src N.tgt Δ)
    (hsep : A.SeparationBounded N.src N.tgt c) (e : Edge (squareLatticeGraph L L)) :
    Fintype.card ((foldedRouting hL N A hgrid).Traversal e) ≤
      8 * (2 * c + 1) * B * Δ := by
  classical
  have hcard : Fintype.card ((foldedRouting hL N A hgrid).Traversal e) =
      #{t : Σ ℓ, Fin (A.linkLength N.src N.tgt ℓ) |
        IsCrossing (foldVertex hL (A.linkRoute N.src N.tgt t.1 t.2))
          (foldVertex hL (A.linkRoute N.src N.tgt t.1 (t.2 + 1))) e} := by
    rw [Fintype.card_subtype]; rfl
  rw [hcard]
  -- The step bounds needed to apply the folding lemmas.
  have hb : ∀ t : Σ ℓ, Fin (A.linkLength N.src N.tgt ℓ),
      ((A.linkRoute N.src N.tgt t.1 t.2).1 + 1 < 2 * L ∧
        (A.linkRoute N.src N.tgt t.1 t.2).2 + 1 < 2 * L) ∧
      ((A.linkRoute N.src N.tgt t.1 (t.2 + 1)).1 + 1 < 2 * L ∧
        (A.linkRoute N.src N.tgt t.1 (t.2 + 1)).2 + 1 < 2 * L) ∧
      IsUnitStep (A.linkRoute N.src N.tgt t.1 t.2) (A.linkRoute N.src N.tgt t.1 (t.2 + 1)) :=
    fun t => ⟨linkRoute_lt hL A _ _ hgrid t.1 t.2.2.le, linkRoute_lt hL A _ _ hgrid t.1 t.2.2,
      hvRoute_isUnitStep _ _ t.2.2⟩
  rcases squareLatticeEdge_horizontal_or_vertical e with he | he
  · obtain ⟨hy, hx⟩ := horizontalSquareLatticeEdge_coords e he
    let S := ({e.1.1.1.1, 2 * L - 3 - e.1.1.1.1} : Finset ℕ) ×ˢ
      ({e.1.1.2.1, 2 * (L - 1) - e.1.1.2.1} : Finset ℕ)
    calc _ ≤ #(S.biUnion fun xy => ({t : Σ ℓ, Fin (A.linkLength N.src N.tgt ℓ) |
            IsUnitCrossing (A.linkRoute N.src N.tgt t.1 t.2)
              (A.linkRoute N.src N.tgt t.1 (t.2 + 1))
              (xy.1, xy.2) (xy.1 + 1, xy.2)} : Finset _)) := by
          refine card_le_card fun t ht => ?_
          simp only [mem_filter, mem_univ, true_and] at ht
          simp only [mem_biUnion, mem_filter, mem_univ, true_and]
          obtain ⟨h1, h2, h3⟩ := hb t
          refine exists_padded_horizontal h1 h2 h3 ?_
          simp only [IsCrossing, foldVertex, Prod.ext_iff, Fin.ext_iff] at ht
          rw [← hx, ← hy] at ht
          tauto
      _ ≤ ∑ xy ∈ S, A.load N.src N.tgt (xy.1, xy.2) (xy.1 + 1, xy.2) := card_biUnion_le
      _ ≤ ∑ _xy ∈ S, 2 * (2 * c + 1) * B * Δ :=
          sum_le_sum fun xy _ => A.load_horizontal_le _ _ hB hΔ hsep _ _
      _ ≤ 4 * (2 * (2 * c + 1) * B * Δ) := by
          rw [sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (card_pair_product_pair_le _ _ _ _)
      _ = 8 * (2 * c + 1) * B * Δ := by ring
  · obtain ⟨hx, hy⟩ := verticalSquareLatticeEdge_coords e he
    let S := ({e.1.1.1.1, 2 * (L - 1) - e.1.1.1.1} : Finset ℕ) ×ˢ
      ({e.1.1.2.1, 2 * L - 3 - e.1.1.2.1} : Finset ℕ)
    calc _ ≤ #(S.biUnion fun xy => ({t : Σ ℓ, Fin (A.linkLength N.src N.tgt ℓ) |
            IsUnitCrossing (A.linkRoute N.src N.tgt t.1 t.2)
              (A.linkRoute N.src N.tgt t.1 (t.2 + 1))
              (xy.1, xy.2) (xy.1, xy.2 + 1)} : Finset _)) := by
          refine card_le_card fun t ht => ?_
          simp only [mem_filter, mem_univ, true_and] at ht
          simp only [mem_biUnion, mem_filter, mem_univ, true_and]
          obtain ⟨h1, h2, h3⟩ := hb t
          refine exists_padded_vertical h1 h2 h3 ?_
          simp only [IsCrossing, foldVertex, Prod.ext_iff, Fin.ext_iff] at ht
          rw [← hx, ← hy] at ht
          tauto
      _ ≤ ∑ xy ∈ S, A.load N.src N.tgt (xy.1, xy.2) (xy.1, xy.2 + 1) := card_biUnion_le
      _ ≤ ∑ _xy ∈ S, 2 * (2 * c + 1) * B * Δ :=
          sum_le_sum fun xy _ => A.load_vertical_le _ _ hB hΔ hsep _ _
      _ ≤ 4 * (2 * (2 * c + 1) * B * Δ) := by
          rw [sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (card_pair_product_pair_le _ _ _ _)
      _ = 8 * (2 * c + 1) * B * Δ := by ring

/-- **Lemma 8.2 with the PEPS assembly.** A party network on dyadic anchors of the padded
square, with at most `B` parties per dyadic block, at most `Δ` links per party, link
separation at most `c` times either endpoint scale, and link dimensions at most `D`, is
exactly a PEPS on the open `L × L` square-lattice graph. Every party's physical index is read
at the fold of its anchor, which is the anchor itself whenever the anchor is a genuine site
(`foldVertex_of_lt`). Every bond dimension is at most `(max D 1) ^ χ`, which is `D ^ χ` whenever
`D ≥ 1`, with `χ = 8 (2 c + 1) B Δ`,
independent of `L` and of the number of dyadic levels. No injectivity, isometry, or
translation-invariance assumption is made.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.2 `lem:routing` and equation
`eq:final-bond`, `07-assembly.tex:102–177`. -/
theorem exists_squarePEPS_of_dyadicRouting (hL : 0 < L) (N : PartyNetwork P Λ d)
    (A : DyadicPlacement P) (hgrid : A.InGrid (paddedSide L)) {B Δ c D : ℕ}
    (hB : A.BlockBounded B) (hΔ : DyadicPlacement.DegreeBounded N.src N.tgt Δ)
    (hsep : A.SeparationBounded N.src N.tgt c) (hdim : ∀ ℓ, N.dim ℓ ≤ D) :
    ∃ T : Tensor (squareLatticeGraph L L) d,
      (∀ σ, stateCoeff T σ = N.coeff (fun p => foldVertex hL (A.anchor p)) σ) ∧
        ∀ e, T.bondDim e ≤ (max D 1) ^ (8 * (2 * c + 1) * B * Δ) :=
  (foldedRouting hL N A hgrid).exists_tensor_of_congestion_le hdim
    (foldedRouting_card_traversal_le hL N A hgrid hB hΔ hsep)

end TNLean.PEPS.Approximation
