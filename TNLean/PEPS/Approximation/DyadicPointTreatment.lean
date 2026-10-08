/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import TNLean.PEPS.Approximation.DyadicRepaintingSchedule

/-!
# Point treatment of the large-scale dyadic repainting

With `t = D log L` and the hole radius `h_n = ε₀ min(n, t)`, a large-scale repainting (`n > K₀ t`)
treats the marked points of each elementary operation: before the operation every involved sheet
is homogenized to the surrounding label `P∘` (to `C` for an exchange) inside the open sup square
of radius `t` around every mark, and the encoded holes at the true vertices have outer squares of
radius `2 h_n`. This file proves the geometric estimates of this point treatment:

* the logarithmic floor `eq:geometry-floor`: after homogenization every point `y` of the remaining
  closed changed region is at distance at least `a₀ max(t, min(n, d_V(y)))` from the other labels,
  and every point of the remaining noncommon-`C` set of an exchange is at that distance from the
  lens boundary;
* the birth-side enlargement: a true vertex of the surrounding guide lies in the closure of the
  other labels, and enlarging it to its outer hole square of radius `2 ε₀ t` halves the floor
  once `2 ε₀ ≤ a₀ / 2`;
* the exchange side: the Lipschitz step from a hole center to every point of its outer square,
  instantiated with the distance from a lens boundary point and the mark distance, the fact that
  every outer hole square of radius `2 ε₀ t` about a true vertex of either sheet then lies on one
  side of the lens boundary, and the tapering separation of the inside positions from the outside
  ones, since a segment from inside to outside crosses the boundary.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the scales
  `eq:geometry-scales` (lines 102–117), the point treatment (lines 328–373), and the exchange
  (lines 389–430).
-/

namespace TNLean.PEPS.Approximation

open Set Metric SquareEdge

/-! ### Scales and homogenization -/

/-- The hole radius `h_n = ε₀ min(n, t)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-scales`,
`06-geometry.tex:102–108`. -/
noncomputable def holeRadius (ε₀ n t : ℝ) : ℝ := ε₀ * min n t

/-- In the large-scale case `t ≤ n`, the hole radius is `ε₀ t`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:371`. -/
theorem holeRadius_of_le {ε₀ n t : ℝ} (h : t ≤ n) : holeRadius ε₀ n t = ε₀ * t := by
  rw [holeRadius, min_eq_right h]

open Classical in
/-- The guide `f` homogenized to the label `P` on the set `U`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–336`. -/
noncomputable def homogenize {X ι : Type*} (U : Set X) (P : ι) (f : X → ι) : X → ι :=
  fun p => if p ∈ U then P else f p

section Homogenize

variable {X ι : Type*} {U : Set X} {P : ι}

theorem homogenize_of_notMem {f : X → ι} {p : X} (hp : p ∉ U) : homogenize U P f p = f p := by
  classical
  simp only [homogenize, hp, ↓reduceIte]

theorem homogenize_of_mem {f : X → ι} {p : X} (hp : p ∈ U) : homogenize U P f p = P := by
  classical
  simp only [homogenize, hp, ↓reduceIte]

/-- Homogenization changes nothing off `U` and leaves no change on `U`. -/
theorem homogenize_changed_subset (f g : X → ι) :
    {p | homogenize U P f p ≠ homogenize U P g p} ⊆ {p | f p ≠ g p} ∩ Uᶜ := by
  intro p hp
  by_cases hU : p ∈ U
  · exact absurd (by rw [homogenize_of_mem hU, homogenize_of_mem hU]) hp
  · rw [mem_ofPred_eq, homogenize_of_notMem hU, homogenize_of_notMem hU] at hp
    exact ⟨hp, hU⟩

/-- Homogenization to the surrounding label only removes positions of other labels.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:359–360`. -/
theorem homogenize_ne_subset (f : X → ι) :
    {p | homogenize U P f p ≠ P} ⊆ {p | f p ≠ P} := by
  intro p hp
  by_cases hU : p ∈ U
  · exact absurd (homogenize_of_mem hU) hp
  · rwa [mem_ofPred_eq, homogenize_of_notMem hU] at hp

theorem homogenize_noncommon_subset (f g : X → ι) :
    {p | homogenize U P f p ≠ P ∨ homogenize U P g p ≠ P} ⊆ {p | f p ≠ P ∨ g p ≠ P} ∩ Uᶜ := by
  intro p hp
  by_cases hU : p ∈ U
  · simp [homogenize_of_mem hU] at hp
  · rw [mem_ofPred_eq, homogenize_of_notMem hU, homogenize_of_notMem hU] at hp
    exact ⟨hp, hU⟩

end Homogenize

/-! ### The logarithmic floor -/

/-- **Logarithmic floor, abstract form.** Let `T'` lie in `T` and outside the open set `U`, on
whose complement the mark distance is at least `t ≤ n`. If every point of the closure of `T` has
the conical clearance `a min(n, d_V(y))` from every point of `Z`, then every point of the closure
of `T'` has the clearance `a max(t, min(n, d_V(y)))` from every point of `Z`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:357–367`. -/
theorem floor_of_subset {X : Type*} [PseudoMetricSpace X] {T T' U Z : Set X} {dV : X → ℝ}
    {a t n : ℝ} (hU : IsOpen U) (hT : T' ⊆ T ∩ Uᶜ) (htn : t ≤ n) (hdV : ∀ y ∉ U, t ≤ dV y)
    (H : ∀ y ∈ closure T, ∀ z ∈ Z, a * min n (dV y) ≤ dist y z) {y : X} (hy : y ∈ closure T')
    {z : X} (hz : z ∈ Z) : a * max t (min n (dV y)) ≤ dist y z := by
  have hy' := closure_mono hT hy
  have hyT : y ∈ closure T := closure_mono inter_subset_left hy'
  have hyU : y ∉ U := closure_minimal inter_subset_right hU.isClosed_compl hy'
  rw [max_eq_right (le_min htn (hdV y hyU))]
  exact H y hyT z hz

/-- The open squares of radius `t` about the two endpoints of an edge, treated before an edge
operation.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
def edgeTreated (n : ℝ) (e : SquareEdge) (t : ℝ) : Set (ℝ × ℝ) :=
  ball (e.point n 0 0) t ∪ ball (e.point n n 0) t

/-- The open squares of radius `t` about the four corners, treated before the central birth.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
def cornerTreated (n t : ℝ) : Set (ℝ × ℝ) :=
  (ball (0, 0) t ∪ ball (n, 0) t) ∪ (ball (0, n) t ∪ ball (n, n) t)

theorem isOpen_edgeTreated (n : ℝ) (e : SquareEdge) (t : ℝ) : IsOpen (edgeTreated n e t) :=
  isOpen_ball.union isOpen_ball

theorem isOpen_cornerTreated (n t : ℝ) : IsOpen (cornerTreated n t) :=
  (isOpen_ball.union isOpen_ball).union (isOpen_ball.union isOpen_ball)

/-- Outside the treated squares the mark distance is at least `t`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:357–359`. -/
theorem le_edgeMarkDist_of_notMem {n t : ℝ} {e : SquareEdge} {y : ℝ × ℝ}
    (hy : y ∉ edgeTreated n e t) : t ≤ edgeMarkDist n e y := by
  simp only [edgeTreated, mem_union, mem_ball, not_or, not_lt] at hy
  exact le_min hy.1 hy.2

theorem le_cornerMarkDist_of_notMem {n t : ℝ} {y : ℝ × ℝ} (hy : y ∉ cornerTreated n t) :
    t ≤ cornerMarkDist n y := by
  simp only [cornerTreated, mem_union, mem_ball, not_or, not_lt] at hy
  exact le_min (le_min hy.1.1 hy.1.2) (le_min hy.2.1 hy.2.2)

/-- **Logarithmic floor for an edge birth or death.** Homogenize the before, after and surrounding
guides of an elementary operation performed by band updates to its surrounding label on the
treated squares of radius `t ≤ n`. Every point `y` of the closure of the remaining changed region
lies at distance at least `a₀ max(t, min(n, d_V(y)))` from every position of another label in the
homogenized surrounding guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-floor`,
`06-geometry.tex:357–367`. -/
theorem BandOperation.floor_bandUpdate {ι : Type*} (op : BandOperation ι) {n t : ℝ}
    (htn : t ≤ n) (e : SquareEdge) (g : ℝ × ℝ → ι) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
      homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p})
    {z : ℝ × ℝ}
    (hz : homogenize (edgeTreated n e t) op.label (bandUpdate n e op.surrounding g) z ≠ op.label) :
    angularConstant * max t (min n (edgeMarkDist n e y)) ≤ dist y z :=
  floor_of_subset (isOpen_edgeTreated n e t) (homogenize_changed_subset _ _) htn
    (fun _ hy => le_edgeMarkDist_of_notMem hy)
    (fun _ hy _ hz => op.clearance_bandUpdate e g hy hz) hy (homogenize_ne_subset _ hz)

/-- **Logarithmic floor for the central birth.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-floor`,
`06-geometry.tex:357–367`. -/
theorem RepaintingBaseline.floor_central {ι : Type*} (R : RepaintingBaseline ι) {t : ℝ}
    (htn : t ≤ R.n) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | homogenize (cornerTreated R.n t) R.oldLabel R.guide p ≠
      homogenize (cornerTreated R.n t) R.oldLabel R.centralGuide p})
    {z : ℝ × ℝ} (hz : homogenize (cornerTreated R.n t) R.oldLabel R.guide z ≠ R.oldLabel) :
    angularConstant * max t (min R.n (cornerMarkDist R.n y)) ≤ dist y z :=
  floor_of_subset (isOpen_cornerTreated R.n t) (homogenize_changed_subset _ _) htn
    (fun _ hy => le_cornerMarkDist_of_notMem hy)
    (fun _ hy _ hz => R.clearance_central hy hz) hy (homogenize_ne_subset _ hz)

/-- **Logarithmic floor for the lens exchange.** Homogenize both sheets to `C_e` on the treated
squares of radius `t ≤ n`. Every point `y` in the closure of the remaining positions that are not
common `C_e` lies at distance at least `a₀ max(t, min(n, d_V(y)))` from the lens boundary.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:389–392`. -/
theorem RepaintingBaseline.floor_exchange {ι : Type*} (R : RepaintingBaseline ι) {t : ℝ}
    (htn : t ≤ R.n) (E : List SquareEdge) (e : SquareEdge) {y : ℝ × ℝ}
    (hy : y ∈ closure {p |
      homogenize (edgeTreated R.n e t) (R.nbrLabel e)
          (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e))) p ≠
        R.nbrLabel e ∨
      homogenize (edgeTreated R.n e t) (R.nbrLabel e)
          (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e))) p ≠ R.nbrLabel e})
    {z : ℝ × ℝ} (hz : z ∈ frontier (edgeLens R.n e)) :
    angularConstant * max t (min R.n (edgeMarkDist R.n e y)) ≤ dist y z :=
  floor_of_subset (isOpen_edgeTreated R.n e t) (homogenize_noncommon_subset _ _) htn
    (fun _ hy => le_edgeMarkDist_of_notMem hy)
    (fun _ hy _ hz => R.clearance_exchange E e hy hz) hy hz

/-! ### True vertices and the birth-side enlargement -/

/-- A true vertex of a guide: a point in the closures of the regions of three distinct labels.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:109–111`. -/
def IsTrueVertex {X ι : Type*} [TopologicalSpace X] (f : X → ι) (c : X) : Prop :=
  ∃ l₁ l₂ l₃ : ι, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧ c ∈ closure (f ⁻¹' {l₁}) ∧
    c ∈ closure (f ⁻¹' {l₂}) ∧ c ∈ closure (f ⁻¹' {l₃})

/-- A true vertex lies in the closure of the positions of labels other than any given label.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:368–369, 393–395, 400–401`. -/
theorem IsTrueVertex.mem_closure_ne {X ι : Type*} [TopologicalSpace X] {f : X → ι} {c : X}
    (h : IsTrueVertex f c) (P : ι) : c ∈ closure {p | f p ≠ P} := by
  obtain ⟨l₁, l₂, -, h12, -, -, h1, h2, -⟩ := h
  by_cases hP : l₁ = P
  · subst hP
    exact closure_mono (fun p (hp : f p = l₂) => by rw [mem_ofPred_eq, hp]; exact Ne.symm h12) h2
  · exact closure_mono (fun p (hp : f p = l₁) => by rw [mem_ofPred_eq, hp]; exact hP) h1

/-- **Outer-hole enlargement on the birth side.** If a point `y` has clearance `a Q` from every
point of `Z`, where `t ≤ Q`, then it has clearance `(a / 2) Q` from every point within `2 ε t` of
the closure of `Z`, once `2 ε ≤ a / 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:368–373`. -/
theorem le_dist_of_dist_le_closure {X : Type*} [PseudoMetricSpace X] {Z : Set X} {y c x : X}
    {a t Q ε : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (htQ : t ≤ Q) (hε : 2 * ε ≤ a / 2)
    (H : ∀ z ∈ Z, a * Q ≤ dist y z) (hc : c ∈ closure Z) (hx : dist x c ≤ 2 * ε * t) :
    a / 2 * Q ≤ dist y x := by
  have hyc : a * Q ≤ dist y c := le_dist_of_mem_closure H hc
  have htri := dist_triangle y x c
  have h1 : 2 * ε * t ≤ a / 2 * t := mul_le_mul_of_nonneg_right hε ht
  have h2 : a / 2 * t ≤ a / 2 * Q := mul_le_mul_of_nonneg_left htQ (by linarith)
  linarith

/-- **Birth-side floor at outer hole sites.** In the setting of
`BandOperation.floor_bandUpdate`, every point within `2 ε₀ t` of a true vertex of the homogenized
surrounding guide lies at distance at least `(a₀ / 2) max(t, min(n, d_V(y)))` from every point `y`
of the closure of the remaining changed region, once `2 ε₀ ≤ a₀ / 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:368–373`. -/
theorem BandOperation.floor_outerHole {ι : Type*} (op : BandOperation ι) {n t ε₀ : ℝ}
    (ht : 0 ≤ t) (htn : t ≤ n) (hε : 2 * ε₀ ≤ angularConstant / 2) (e : SquareEdge)
    (g : ℝ × ℝ → ι) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
      homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p})
    {c : ℝ × ℝ}
    (hc : IsTrueVertex (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.surrounding g))
      c) {x : ℝ × ℝ} (hx : dist x c ≤ 2 * (ε₀ * t)) :
    angularConstant / 2 * max t (min n (edgeMarkDist n e y)) ≤ dist y x := by
  rw [← mul_assoc] at hx
  exact le_dist_of_dist_le_closure angularConstant_pos.le ht (le_max_left _ _) hε
    (fun _ hz => op.floor_bandUpdate htn e g hy hz) (hc.mem_closure_ne op.label) hx

/-- **Birth-side floor at outer hole sites, central birth.** In the setting of
`RepaintingBaseline.floor_central`, every point within `2 ε₀ t` of a true vertex of the homogenized
starting guide lies at distance at least `(a₀ / 2) max(t, min(n, d_V(y)))` from every point `y` of
the closure of the remaining changed region, once `2 ε₀ ≤ a₀ / 2`; here `V` is the four corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:368–373`. -/
theorem RepaintingBaseline.floor_central_outerHole {ι : Type*} (R : RepaintingBaseline ι)
    {t ε₀ : ℝ} (ht : 0 ≤ t) (htn : t ≤ R.n) (hε : 2 * ε₀ ≤ angularConstant / 2) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | homogenize (cornerTreated R.n t) R.oldLabel R.guide p ≠
      homogenize (cornerTreated R.n t) R.oldLabel R.centralGuide p})
    {c : ℝ × ℝ} (hc : IsTrueVertex (homogenize (cornerTreated R.n t) R.oldLabel R.guide) c)
    {x : ℝ × ℝ} (hx : dist x c ≤ 2 * (ε₀ * t)) :
    angularConstant / 2 * max t (min R.n (cornerMarkDist R.n y)) ≤ dist y x := by
  rw [← mul_assoc] at hx
  exact le_dist_of_dist_le_closure angularConstant_pos.le ht (le_max_left _ _) hε
    (fun _ hz => R.floor_central htn hy hz) (hc.mem_closure_ne R.oldLabel) hx

/-! ### The exchange side -/

/-- **Lipschitz step of the outer-hole enlargement.** Let `g` (the distance from the lens boundary)
and `h` (the mark distance) be `1`-Lipschitz, let `t > 0`, and suppose `2 ε₀ (a + 1) ≤ a / 2`. If a
hole center `c` has the tapered clearance `g c ≥ a max(t, min(n, h c))`, then every point `x` with
`|x - c| ≤ 2 ε₀ t` has `g x ≥ (a / 2) max(t, min(n, h x))`. It is instantiated with the distance
from a lens boundary point and the mark distance in `lens_clearance_of_center`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:405–415`. -/
theorem tapered_clearance_of_center {X : Type*} [PseudoMetricSpace X] {g h : X → ℝ}
    (hg : ∀ x c, g c ≤ g x + dist x c) (hh : ∀ x c, h x ≤ h c + dist x c)
    {a ε t n : ℝ} (ha : 0 < a) (ht : 0 < t) (haε : 2 * ε * (a + 1) ≤ a / 2)
    {x c : X} (hc : a * max t (min n (h c)) ≤ g c) (hx : dist x c ≤ 2 * ε * t) :
    a / 2 * max t (min n (h x)) ≤ g x := by
  set δ := dist x c
  have hδ : 0 ≤ δ := dist_nonneg
  have hQ : max t (min n (h x)) ≤ max t (min n (h c)) + δ := by
    refine max_le (by linarith [le_max_left t (min n (h c))]) ?_
    have := hh x c
    rcases le_total n (h c) with h1 | h1
    · have : min n (h x) ≤ n := min_le_left _ _
      have : n = min n (h c) := (min_eq_left h1).symm
      linarith [le_max_right t (min n (h c))]
    · have : min n (h x) ≤ h x := min_le_right _ _
      have : h c = min n (h c) := (min_eq_right h1).symm
      linarith [le_max_right t (min n (h c))]
  have htQ : t ≤ max t (min n (h x)) := le_max_left _ _
  have h1 := hg x c
  have h2 : a * max t (min n (h x)) ≤ a * max t (min n (h c)) + a * δ := by nlinarith
  have h3 : (a + 1) * δ ≤ (a + 1) * (2 * ε * t) := mul_le_mul_of_nonneg_left hx (by linarith)
  have h4 : (a + 1) * (2 * ε * t) ≤ a / 2 * t := by nlinarith
  have h5 : a / 2 * t ≤ a / 2 * max t (min n (h x)) := mul_le_mul_of_nonneg_left htQ (by linarith)
  nlinarith

/-- **The Lipschitz step, instantiated.** If a hole center `c` has clearance
`a max(t, min(n, d_V(c)))` from every point of the lens boundary, then so, with `a / 2`, does every
point within `2 ε t` of it, once `2 ε (a + 1) ≤ a / 2`: the distance from a boundary point and the
mark distance are `1`-Lipschitz.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:400–415`. -/
theorem lens_clearance_of_center {n t a ε : ℝ} (e : SquareEdge) (ha : 0 < a) (ht : 0 < t)
    (haε : 2 * ε * (a + 1) ≤ a / 2) {c x : ℝ × ℝ}
    (hc : ∀ z ∈ frontier (edgeLens n e), a * max t (min n (edgeMarkDist n e c)) ≤ dist c z)
    (hx : dist x c ≤ 2 * ε * t) :
    ∀ z ∈ frontier (edgeLens n e), a / 2 * max t (min n (edgeMarkDist n e x)) ≤ dist x z :=
  fun z hz => tapered_clearance_of_center (g := fun w => dist w z)
    (fun x c => by linarith [dist_triangle c x z, dist_comm c x])
    (fun x c => edgeMarkDist_le_add n e x c) ha ht haε (hc z hz) hx

/-- **Exchange floor at outer hole sites.** Every point within `2 ε₀ t` of a true vertex of either
homogenized sheet has clearance `(a₀ / 2) max(t, min(n, d_V(x)))` from the lens boundary, once
`2 ε₀ (a₀ + 1) ≤ a₀ / 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:393–415`. -/
theorem RepaintingBaseline.floor_exchange_outerHole {ι : Type*} (R : RepaintingBaseline ι)
    {t ε₀ : ℝ} (ht : 0 < t) (htn : t ≤ R.n) (hε : 2 * ε₀ * (angularConstant + 1) ≤
      angularConstant / 2) (E : List SquareEdge) (e : SquareEdge) {c : ℝ × ℝ}
    (hc : IsTrueVertex (homogenize (edgeTreated R.n e t) (R.nbrLabel e)
        (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e)))) c ∨
      IsTrueVertex (homogenize (edgeTreated R.n e t) (R.nbrLabel e)
        (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e)))) c)
    {x : ℝ × ℝ} (hx : dist x c ≤ 2 * ε₀ * t) :
    ∀ z ∈ frontier (edgeLens R.n e),
      angularConstant / 2 * max t (min R.n (edgeMarkDist R.n e x)) ≤ dist x z := by
  refine lens_clearance_of_center e angularConstant_pos ht hε (fun z hz => ?_) hx
  refine R.floor_exchange htn E e ?_ hz
  rcases hc with hc | hc
  · exact closure_mono (fun p hp => Or.inl hp) (hc.mem_closure_ne (R.nbrLabel e))
  · exact closure_mono (fun p hp => Or.inr hp) (hc.mem_closure_ne (R.nbrLabel e))

/-- A preconnected set that does not meet the boundary of `Y` lies in `Y` or in its complement. -/
theorem subset_or_subset_compl_of_disjoint_frontier {X : Type*} [TopologicalSpace X]
    {s Y : Set X} (hs : IsPreconnected s) (h : ∀ x ∈ s, x ∉ frontier Y) : s ⊆ Y ∨ s ⊆ Yᶜ := by
  rcases isPreconnected_iff_subset_of_disjoint.1 hs (interior Y) (closure Y)ᶜ isOpen_interior
      isClosed_closure.isOpen_compl (fun x hx => by
        by_contra hc
        rw [mem_union, not_or, mem_compl_iff, not_not] at hc
        exact h x hx ⟨hc.2, hc.1⟩)
      (by
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
          not_not]
        exact fun _ hx => subset_closure (interior_subset hx)) with h' | h'
  · exact Or.inl (h'.trans interior_subset)
  · exact Or.inr (h'.trans (compl_subset_compl.2 subset_closure))

/-- **An outer hole square lies on one side of the lens boundary.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:403–405, 415–417`. -/
theorem closedBall_subset_or_subset_compl {Y : Set (ℝ × ℝ)} {c : ℝ × ℝ} {r b : ℝ} (hb : 0 < b)
    (h : ∀ x ∈ closedBall c r, ∀ z ∈ frontier Y, b ≤ dist x z) :
    closedBall c r ⊆ Y ∨ closedBall c r ⊆ Yᶜ :=
  subset_or_subset_compl_of_disjoint_frontier (convex_closedBall c r).isPreconnected
    fun x hx hxY => by
      have := h x hx x hxY
      rw [dist_self] at this
      linarith

/-- **The outer hole squares of an exchange lie on one side of the lens boundary.** For a true
vertex `c` of either homogenized sheet of the exchange along `e`, the closed sup square of radius
`2 ε₀ t` about `c`, its outer hole square, lies in the lens `Y` or in its complement, once
`2 ε₀ (a₀ + 1) ≤ a₀ / 2`: by `RepaintingBaseline.floor_exchange_outerHole` each of its points is
at distance at least `(a₀ / 2) t > 0` from the boundary of `Y`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:400–405, 415–417`. -/
theorem RepaintingBaseline.outerHole_subset_or_subset_compl {ι : Type*}
    (R : RepaintingBaseline ι) {t ε₀ : ℝ} (ht : 0 < t) (htn : t ≤ R.n)
    (hε : 2 * ε₀ * (angularConstant + 1) ≤ angularConstant / 2) (E : List SquareEdge)
    (e : SquareEdge) {c : ℝ × ℝ}
    (hc : IsTrueVertex (homogenize (edgeTreated R.n e t) (R.nbrLabel e)
        (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e)))) c ∨
      IsTrueVertex (homogenize (edgeTreated R.n e t) (R.nbrLabel e)
        (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e)))) c) :
    closedBall c (2 * ε₀ * t) ⊆ edgeLens R.n e ∨
      closedBall c (2 * ε₀ * t) ⊆ (edgeLens R.n e)ᶜ := by
  have ha := angularConstant_pos
  refine closedBall_subset_or_subset_compl (b := angularConstant / 2 * t) (by positivity)
    fun x hx z hz => ?_
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans
    (R.floor_exchange_outerHole ht htn hε E e hc (mem_closedBall.1 hx) z hz)

/-- A segment from a point of `Y` to a point outside `Y` meets the boundary of `Y` within its
length.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:424–426`. -/
theorem exists_mem_frontier_dist_le {Y : Set (ℝ × ℝ)} {x z : ℝ × ℝ} (hx : x ∈ Y) (hz : z ∉ Y) :
    ∃ w ∈ frontier Y, dist x w ≤ dist x z := by
  by_contra hne
  push Not at hne
  have hs : ∀ w ∈ segment ℝ x z, w ∉ frontier Y := fun w hw hwY => by
    have := hne w hwY
    have := dist_add_dist_of_mem_segment hw
    linarith [dist_nonneg (x := w) (y := z)]
  rcases subset_or_subset_compl_of_disjoint_frontier (convex_segment x z).isPreconnected hs with
    h | h
  · exact hz (h (right_mem_segment ℝ x z))
  · exact h (left_mem_segment ℝ x z) hx

/-- **Tapering separation across the lens boundary.** A clearance from the boundary of `Y` is a
clearance from every point on the other side of it.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:421–429`. -/
theorem le_dist_of_frontier {Y : Set (ℝ × ℝ)} {x z : ℝ × ℝ} {b : ℝ}
    (h : ∀ w ∈ frontier Y, b ≤ dist x w) (hxz : (x ∈ Y ∧ z ∉ Y) ∨ (x ∉ Y ∧ z ∈ Y)) :
    b ≤ dist x z := by
  rcases hxz with ⟨hx, hz⟩ | ⟨hx, hz⟩
  · obtain ⟨w, hw, hd⟩ := exists_mem_frontier_dist_le hx hz
    exact (h w hw).trans hd
  · obtain ⟨w, hw, hd⟩ := exists_mem_frontier_dist_le (Y := Yᶜ) hx (not_not.2 hz)
    rw [frontier_compl] at hw
    exact (h w hw).trans hd

end TNLean.PEPS.Approximation
