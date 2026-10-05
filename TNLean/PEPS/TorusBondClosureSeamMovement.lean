/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBondFlatConnection
import TNLean.PEPS.TorusMatchedCutClosureMembership

/-!
# Moving commuting closures on native labelled torus bonds

The seam deformation of SCP10, Theorem 5.5 and equation
`eq:2d:move-strings`, is a group-valued vertex gauge transformation.
Consequently averaging any function of the bond labels is independent of the
chosen seams. The statements impose no virtual dimensions or representations,
and apply to all positive periods, including periods one and two.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {G : Type*} [Group G] {width height : ℕ}

/-- Native closure labels supported on arbitrary horizontal and vertical seams.
Source: SCP10, Definition 5.6 and equation `eq:2d:peps-with-ug-uh`. -/
def torusBondClosureLabelsAt (g h : G) (c : ZMod width) (r : ZMod height) :
    TorusBondLabels width height G :=
  (fun v ↦ if v.1 + 1 = c then h else 1,
    fun v ↦ if v.2 + 1 = r then g else 1)

/-- The zero seams give the standard closure labels. -/
@[simp]
theorem torusBondClosureLabelsAt_zero (g h : G) :
    torusBondClosureLabelsAt (width := width) (height := height) g h 0 0 =
      torusBondClosureLabels g h := rfl

variable [NeZero width] [NeZero height]

/-- Moving both seams by a horizontal gauge followed by a vertical gauge.
The inverse vertical label accounts for the native downward bond orientation.
Source: SCP10, equation `eq:2d:move-strings`. -/
def torusBondClosureSeamGauge (g h : G) (c : ZMod width) (r : ZMod height)
    (v : TorusVertex width height) : G :=
  torusSeamGauge g⁻¹ r v.2 * torusSeamGauge h c v.1

omit [NeZero height] in
/-- The horizontal seam movement preserves the commuting vertical insertion.
Source: SCP10, equation `eq:2d:move-strings`. -/
theorem torusBondGauge_horizontalClosureAt (g h : G) (hgh : Commute g h)
    (c : ZMod width) (r : ZMod height) :
    torusBondGauge (fun v ↦ torusSeamGauge h c v.1)
        (torusBondClosureLabelsAt g h 0 r) = torusBondClosureLabelsAt g h c r := by
  apply Prod.ext
  · funext v
    exact (torusSeamGauge_horizontal h c v.1).symm
  · funext v
    have hc : torusSeamGauge h c v.1 * g * (torusSeamGauge h c v.1)⁻¹ = g :=
      (torusSeamGauge_commute hgh.symm c v.1).mul_inv_cancel
    simp only [torusBondGauge, torusBondClosureLabelsAt]
    split_ifs <;> simp [hc]

omit [NeZero width] in
/-- The vertical seam movement preserves the commuting horizontal insertion.
Source: SCP10, equation `eq:2d:move-strings`. -/
theorem torusBondGauge_verticalClosureAt (g h : G) (hgh : Commute g h)
    (c : ZMod width) (r : ZMod height) :
    torusBondGauge (fun v ↦ torusSeamGauge g⁻¹ r v.2)
        (torusBondClosureLabelsAt g h c 0) = torusBondClosureLabelsAt g h c r := by
  apply Prod.ext
  · funext v
    have hc : torusSeamGauge g⁻¹ r v.2 * h * (torusSeamGauge g⁻¹ r v.2)⁻¹ = h :=
      (torusSeamGauge_commute hgh.inv_left r v.2).mul_inv_cancel
    simp only [torusBondGauge, torusBondClosureLabelsAt]
    split_ifs <;> simp [hc]
  · funext v
    exact (torusSeamGauge_vertical g r v.2).symm

/-- An explicit vertex gauge moves a commuting closure onto arbitrary seams.
This group-valued identity is independent of all virtual bond dimensions.
Source: SCP10, Theorem 5.5 and equation `eq:2d:move-strings`. -/
theorem torusBondGauge_closureSeamGauge (g h : G) (hgh : Commute g h)
    (c : ZMod width) (r : ZMod height) :
    torusBondGauge (torusBondClosureSeamGauge g h c r) (torusBondClosureLabels g h) =
      torusBondClosureLabelsAt g h c r := by
  change torusBondGauge
      ((fun v ↦ torusSeamGauge g⁻¹ r v.2) * (fun v ↦ torusSeamGauge h c v.1))
      (torusBondClosureLabelsAt g h 0 0) = _
  rw [← torusBondGauge_mul, torusBondGauge_horizontalClosureAt g h hgh,
    torusBondGauge_verticalClosureAt g h hgh]

/-- Any two commuting closure seams are gauge equivalent to the standard pair.
Source: SCP10, Theorem 5.5 and equation `eq:2d:move-strings`. -/
theorem exists_torusBondGauge_eq_closureAt (g h : G) (hgh : Commute g h)
    (c : ZMod width) (r : ZMod height) :
    ∃ q : TorusVertex width height → G,
      torusBondGauge q (torusBondClosureLabels g h) = torusBondClosureLabelsAt g h c r :=
  ⟨torusBondClosureSeamGauge g h c r, torusBondGauge_closureSeamGauge g h hgh c r⟩

/-- Averaging any function over all vertex gauges gives the same result for
shifted and standard commuting closure labels. No representation or virtual
coordinate alphabet appears in this statement. Source: SCP10, Theorem 5.5,
the seam deformation used in the first inclusion. -/
theorem sum_torusBondGauge_closureAt [Fintype G] {A : Type*} [AddCommMonoid A]
    (f : TorusBondLabels width height G → A) (g h : G) (hgh : Commute g h)
    (c : ZMod width) (r : ZMod height) :
    (∑ q, f (torusBondGauge q (torusBondClosureLabelsAt g h c r))) =
      ∑ q, f (torusBondGauge q (torusBondClosureLabels g h)) := by
  rw [← torusBondGauge_closureSeamGauge g h hgh c r]
  exact sum_torusBondGauge f (torusBondClosureSeamGauge g h c r) (torusBondClosureLabels g h)

end TNLean.PEPS
