/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualRectangle
import TNLean.PEPS.TorusDualWinding

/-!
# Classification of full-support dual-path homotopies

Two finite labelled torus dual paths with the same endpoints are related by
the generated square and backtrack moves on the whole torus exactly when
their lifted integer displacements agree. Every path is lifted into a finite
rectangle whose margin is its length, and the rectangle comb gives the
homotopy. Edge labels are retained at periods one and two.

Source: SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214.

**Scope restriction (full swept support):** This classifies the homotopies
with every primal vertex allowed as a square-move support. It does not
classify homotopies constrained to avoid an arbitrary region, equate paths
with different winding, or assert vacuum reduced-density equality. See
`docs/paper-gaps/scp10_dual_flux_homotopy_classification.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local instance : Quiver X := torusDualQuiver width height

private theorem displacement_bounds {a b : X} (p : TorusDualPath a b) :
    -(p.length : ℤ) ≤ (torusDualPathDisplacement p).1 ∧
      (torusDualPathDisplacement p).1 ≤ p.length ∧
      -(p.length : ℤ) ≤ (torusDualPathDisplacement p).2 ∧
      (torusDualPathDisplacement p).2 ≤ p.length := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rcases ih with ⟨hx, hx', hy, hy'⟩
    cases e <;>
      simp only [Quiver.Path.length_cons, torusDualPathDisplacement_cons,
        TorusDualStep.displacement, Prod.fst_add, Prod.snd_add, Nat.cast_add,
        Nat.cast_one] <;> omega

private theorem exists_rectStep (x : ZMod width) (y : ZMod height)
    {W H : ℕ} {a b : X} (e : TorusDualStep a b)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hiW : i < W) (hjH : j < H)
    (ha : (torusRectCoord x i, torusRectCoord y j) = a) :
    ∃ c : ℕ × ℕ, (torusRectCoord x c.1, torusRectCoord y c.2) = b ∧
      ∃ f : RectDualStep W H (i, j) c,
        HEq (f.toTorus x y) e ∧
          (c.1 : ℤ) = i + e.displacement.1 ∧
          (c.2 : ℤ) = j + e.displacement.2 := by
  cases e with
  | east u v =>
    obtain ⟨hx, hy⟩ := Prod.mk.inj ha
    cases hx
    cases hy
    refine ⟨(i + 1, j), rfl, .east i j hiW (Nat.le_of_lt hjH), HEq.rfl, ?_, ?_⟩
    all_goals simp [TorusDualStep.displacement]
  | west u v =>
    cases i with
    | zero => omega
    | succ i =>
      have hx : torusRectCoord x i = u := by
        have h := congrArg Prod.fst ha
        change torusRectCoord x i + 1 = u + 1 at h
        exact add_right_cancel h
      have hy := congrArg Prod.snd ha
      cases hx
      cases hy
      refine ⟨(i, j), rfl, .west i j (by omega) (Nat.le_of_lt hjH), HEq.rfl, ?_, ?_⟩
      all_goals simp [TorusDualStep.displacement]
  | north u v =>
    obtain ⟨hx, hy⟩ := Prod.mk.inj ha
    cases hx
    cases hy
    refine ⟨(i, j + 1), rfl, .north i j (Nat.le_of_lt hiW) hjH, HEq.rfl, ?_, ?_⟩
    all_goals simp [TorusDualStep.displacement]
  | south u v =>
    cases j with
    | zero => omega
    | succ j =>
      have hx := congrArg Prod.fst ha
      have hy : torusRectCoord y j = v := by
        have h := congrArg Prod.snd ha
        change torusRectCoord y j + 1 = v + 1 at h
        exact add_right_cancel h
      cases hx
      cases hy
      refine ⟨(i, j), rfl, .south i j (Nat.le_of_lt hiW) (by omega), HEq.rfl, ?_, ?_⟩
      all_goals simp [TorusDualStep.displacement]

private theorem exists_rectLift {a b : X} (p : TorusDualPath a b) :
    ∀ (x : ZMod width) (y : ZMod height) (W H i j : ℕ),
      (torusRectCoord x i, torusRectCoord y j) = a →
      p.length ≤ i → i + p.length ≤ W → p.length ≤ j → j + p.length ≤ H →
      ∃ c : ℕ × ℕ,
        ((c.1 : ℤ) = i + (torusDualPathDisplacement p).1 ∧
          (c.2 : ℤ) = j + (torusDualPathDisplacement p).2) ∧
        (torusRectCoord x c.1, torusRectCoord y c.2) = b ∧
        ∃ r : @Quiver.Path (ℕ × ℕ) (rectDualQuiver W H) (i, j) c,
          HEq (rectDualPathToTorus x y r) p := by
  induction p with
  | nil =>
    intro x y W H i j ha _ _ _ _
    let : Quiver (ℕ × ℕ) := rectDualQuiver W H
    refine ⟨(i, j), by simp, ha, .nil, ?_⟩
    cases ha
    rfl
  | @cons b c p e ih =>
    intro x y W H i j ha hi hiW hj hjH
    let : Quiver (ℕ × ℕ) := rectDualQuiver W H
    simp only [Quiver.Path.length_cons] at hi hiW hj hjH
    obtain ⟨z, hz, hb, r, hr⟩ := ih x y W H i j ha
      (by omega) (by omega) (by omega) (by omega)
    obtain ⟨hx, hx', hy, hy'⟩ := displacement_bounds p
    have hzi : 0 < z.1 := by omega
    have hzj : 0 < z.2 := by omega
    have hziW : z.1 < W := by omega
    have hzjH : z.2 < H := by omega
    obtain ⟨z', hc, s, hs, hsi, hsj⟩ :=
      exists_rectStep x y e z.1 z.2 hzi hzj hziW hzjH hb
    refine ⟨z', ?_, hc, r.cons s, ?_⟩
    · simp only [torusDualPathDisplacement_cons, Prod.fst_add, Prod.snd_add]
      constructor <;> omega
    · change HEq ((rectDualPathToTorus x y r).cons (s.toTorus x y)) (p.cons e)
      cases ha
      cases hb
      cases hc
      exact heq_of_eq (congrArg₂ (fun r s ↦ r.cons s) (eq_of_heq hr) (eq_of_heq hs))

private theorem homotopy_of_heq {R : Set X} {a b a' b' : X}
    {p q : TorusDualPath a b} {p' q' : TorusDualPath a' b'}
    (ha : a' = a) (hb : b' = b) (hp : HEq p' p) (hq : HEq q' q)
    (h : TorusDualHomotopy R p' q') : TorusDualHomotopy R p q := by
  cases ha
  cases hb
  simpa only [eq_of_heq hp, eq_of_heq hq] using h

/-- The generated homotopy relation on the full labelled torus is classified
by lifted integer displacement. The converse derives rectangular lifts of both
paths and normalizes them by square moves and backtracks. No side-length or
positive-period hypothesis is needed. Source: SCP10, Lemma 6.14. -/
theorem torusDualHomotopy_univ_iff_displacement_eq {a b : X}
    (p q : TorusDualPath a b) :
    TorusDualHomotopy Set.univ p q ↔
      torusDualPathDisplacement p = torusDualPathDisplacement q := by
  refine ⟨TorusDualHomotopy.displacement_eq, ?_⟩
  intro h
  let N := p.length + q.length
  let x := a.1 - (N : ZMod width)
  let y := a.2 - (N : ZMod height)
  have ha : (torusRectCoord x N, torusRectCoord y N) = a := by
    simp [torusRectCoord_eq, x, y]
  obtain ⟨c, hc, hb, p', hp⟩ := exists_rectLift p x y (2 * N) (2 * N) N N ha
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨d, hd, _, q', hq⟩ := exists_rectLift q x y (2 * N) (2 * N) N N ha
    (by omega) (by omega) (by omega) (by omega)
  have hcd : c = d := by
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    apply Prod.ext <;> omega
  subst d
  exact homotopy_of_heq ha hb hp hq ((rectDualPath_homotopy x y p' q').mono (Set.subset_univ _))

end TNLean.PEPS
