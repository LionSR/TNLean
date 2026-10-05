/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutCoefficientExtraction
import TNLean.PEPS.TorusFlatConnectionGauge

/-!
# Flat connections on the actual labelled torus bonds

Horizontal and vertical bonds are indexed separately by their initial vertex.
In particular, the eight bonds of a two-by-two torus remain distinct. The vertical
label convention is opposite to upward parallel transport, as in the native
four-leg contraction. Flatness reduces these labels to two commuting seam labels
for all positive periods, including period two.

This is the group-theoretic closure reduction in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Theorem 5.5 and `eq:2d:move-strings`. No simple-graph encoding or
lower bound of three on the periods is used in these statements.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {G : Type*} [Group G] {width height : ℕ}

/-- Change of vertex gauge on the actual horizontal and vertical bond labels. -/
def torusBondGauge (q : TorusVertex width height → G)
    (p : TorusBondLabels width height G) : TorusBondLabels width height G :=
  (fun v ↦ q (v.1 + 1, v.2) * p.1 v * (q v)⁻¹,
    fun v ↦ q v * p.2 v * (q (v.1, v.2 + 1))⁻¹)

/-- Flatness of the four bonds surrounding every plaquette, in the native
horizontal and vertical insertion conventions. -/
def IsTorusBondFlat (p : TorusBondLabels width height G) : Prop :=
  ∀ v, p.2 (v.1 + 1, v.2) * p.1 (v.1, v.2 + 1) = p.1 v * p.2 v

/-- Two seam insertions, with horizontal label `h` and vertical label `g`. -/
def torusBondClosureLabels (g h : G) : TorusBondLabels width height G :=
  (fun v ↦ if v.1 + 1 = 0 then h else 1,
    fun v ↦ if v.2 + 1 = 0 then g else 1)

/-- The identity vertex gauge does not change the bond labels. -/
@[simp]
theorem torusBondGauge_one (p : TorusBondLabels width height G) :
    torusBondGauge 1 p = p := by
  ext v <;> simp [torusBondGauge]

/-- Applying two vertex gauges multiplies them pointwise in application order. -/
theorem torusBondGauge_mul (q r : TorusVertex width height → G)
    (p : TorusBondLabels width height G) :
    torusBondGauge q (torusBondGauge r p) = torusBondGauge (q * r) p := by
  ext v <;> simp [torusBondGauge, mul_assoc]

/-- Inverting the vertex gauge reverses its action. -/
@[simp]
theorem torusBondGauge_inv (q : TorusVertex width height → G)
    (p : TorusBondLabels width height G) :
    torusBondGauge q⁻¹ (torusBondGauge q p) = p := by
  rw [torusBondGauge_mul, inv_mul_cancel, torusBondGauge_one]

/-- Gauge changes preserve each plaquette's flatness equation. -/
theorem IsTorusBondFlat.torusBondGauge {p : TorusBondLabels width height G}
    (hp : IsTorusBondFlat p) (q : TorusVertex width height → G) :
    IsTorusBondFlat (torusBondGauge q p) := by
  intro v
  have h := congrArg (fun z ↦ q (v.1 + 1, v.2) * z * (q (v.1, v.2 + 1))⁻¹) (hp v)
  simpa only [TNLean.PEPS.torusBondGauge, mul_assoc, inv_mul_cancel_left] using h

/-- Flatness is equivalent before and after a vertex gauge change. -/
@[simp]
theorem isTorusBondFlat_torusBondGauge_iff (q : TorusVertex width height → G)
    (p : TorusBondLabels width height G) :
    IsTorusBondFlat (torusBondGauge q p) ↔ IsTorusBondFlat p := by
  constructor
  · intro hp
    simpa only [torusBondGauge_inv] using hp.torusBondGauge q⁻¹
  · exact fun hp ↦ hp.torusBondGauge q

/-- Inverting vertical labels converts native flatness to parallel-transport
flatness. This identification uses no graph and retains all labelled bonds. -/
theorem isTorusBondFlat_iff_isTorusFlat (p : TorusBondLabels width height G) :
    IsTorusBondFlat p ↔ IsTorusFlat p.1 (fun v ↦ (p.2 v)⁻¹) := by
  constructor
  · intro hp v
    have h := congrArg (fun z ↦ (p.2 (v.1 + 1, v.2))⁻¹ * z * (p.2 v)⁻¹) (hp v)
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h.symm
  · intro hp v
    have h := congrArg (fun z ↦ p.2 (v.1 + 1, v.2) * z * p.2 v) (hp v)
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one] using h.symm

/-- Flatness of the standard two-seam closure is exactly commutation. -/
theorem isTorusBondFlat_closure_iff (g h : G) :
    IsTorusBondFlat (torusBondClosureLabels (width := width) (height := height) g h) ↔
      Commute g h := by
  constructor
  · intro hp
    change g * h = h * g
    simpa only [torusBondClosureLabels, neg_add_cancel, ite_true] using hp (-1, -1)
  · intro hgh v
    simp only [torusBondClosureLabels]
    split_ifs <;> simp_all [Commute.eq hgh]

/-- Relative bond labels produced by a family of vertex group elements. -/
def torusBondRelativeLabels (q : TorusVertex width height → G) :
    TorusBondLabels width height G := torusBondGauge q 1

/-- Relative labels satisfy every plaquette's compatibility relation. -/
theorem isTorusBondFlat_relativeLabels (q : TorusVertex width height → G) :
    IsTorusBondFlat (torusBondRelativeLabels q) := by
  apply IsTorusBondFlat.torusBondGauge
  intro v
  simp

variable [NeZero width] [NeZero height]

/-- The inverse rooted-tree transport, expressed in native bond conventions. -/
def torusBondTreeGauge (p : TorusBondLabels width height G)
    (v : TorusVertex width height) : G :=
  (torusTreeGauge p.1 (fun w ↦ (p.2 w)⁻¹) v)⁻¹

/-- The tree gauge leaves only the two based holonomies on the wrapping bonds. -/
theorem IsTorusBondFlat.torusBondGauge_tree {p : TorusBondLabels width height G}
    (hp : IsTorusBondFlat p) :
    TNLean.PEPS.torusBondGauge (torusBondTreeGauge p) p =
      torusBondClosureLabels
        (zmodTransport (fun y ↦ (p.2 (0, y))⁻¹) height)⁻¹
        (zmodTransport (fun x ↦ p.1 (x, 0)) width) := by
  have hf := (isTorusBondFlat_iff_isTorusFlat p).mp hp
  apply Prod.ext
  · funext v
    simpa only [TNLean.PEPS.torusBondGauge, torusBondTreeGauge, inv_inv, torusBondClosureLabels]
      using hf.torusTreeGauge_right v
  · funext v
    have h := congrArg Inv.inv (hf.torusTreeGauge_up v)
    simpa only [TNLean.PEPS.torusBondGauge, torusBondTreeGauge, torusBondClosureLabels,
      mul_inv_rev, inv_inv, apply_ite, inv_one, mul_assoc] using h

/-- Every flat assignment to the actual labelled torus bonds is gauge equivalent
to two commuting closure seams. This includes the two-by-two torus used in
SCP10, Theorem 5.5, without identifying its parallel bonds. -/
theorem exists_torusBondGauge_eq_closure (p : TorusBondLabels width height G)
    (hp : IsTorusBondFlat p) :
    ∃ (q : TorusVertex width height → G) (g h : G),
      Commute g h ∧ torusBondGauge q p = torusBondClosureLabels g h := by
  have hf := (isTorusBondFlat_iff_isTorusFlat p).mp hp
  exact ⟨torusBondTreeGauge p,
    (zmodTransport (fun y ↦ (p.2 (0, y))⁻¹) height)⁻¹,
    zmodTransport (fun x ↦ p.1 (x, 0)) width,
    hf.commute_holonomies.symm.inv_left, hp.torusBondGauge_tree⟩

/-- The flat bond assignments are exactly the vertex-gauge orbits of commuting
seam closures. The orientation also expresses a given flat assignment as a
gauge transform of a closure, for use in the physical averaging argument. -/
theorem isTorusBondFlat_iff_exists_eq_gauge_closure (p : TorusBondLabels width height G) :
    IsTorusBondFlat p ↔
      ∃ (q : TorusVertex width height → G) (g h : G),
        Commute g h ∧ p = torusBondGauge q (torusBondClosureLabels g h) := by
  constructor
  · intro hp
    obtain ⟨q, g, h, hgh, heq⟩ := exists_torusBondGauge_eq_closure p hp
    refine ⟨q⁻¹, g, h, hgh, ?_⟩
    rw [← heq, torusBondGauge_inv]
  · rintro ⟨q, g, h, hgh, rfl⟩
    exact ((isTorusBondFlat_closure_iff g h).mpr hgh).torusBondGauge q

/-- Averaging any function over all vertex gauges is unchanged by first applying
a fixed gauge. This is the finite-sum reindexing behind closure-state equality. -/
theorem sum_torusBondGauge [Fintype G] {A : Type*} [AddCommMonoid A]
    (f : TorusBondLabels width height G → A) (q : TorusVertex width height → G)
    (p : TorusBondLabels width height G) :
    (∑ r, f (torusBondGauge r (torusBondGauge q p))) =
      ∑ r, f (torusBondGauge r p) := by
  simp only [torusBondGauge_mul]
  exact Equiv.sum_comp (Equiv.mulRight q) (fun r ↦ f (torusBondGauge r p))

end TNLean.PEPS
