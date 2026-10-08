/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusMatchedProjectorExpansion
import TNLean.PEPS.TorusCutClosureMembership

/-!
# Matched commuting closures in every actual torus cut space

Independent representations on individual oriented bonds still permit the seam
movement of SCP10, equation `eq:2d:move-strings`. The group-valued change of basis
is evaluated in each bond's own representation. Thus every commuting closure of
site-dependent invariant tensors lies in every actual cut space, and its span
lies in the intersection of the four two-by-two cut spaces of Theorem 5.5.

The common finite coordinate alphabet is the only remaining dimensional scope
restriction here. No uniform representation, injectivity, semi-regularity,
unitarity, or contracted-region Gram identity is assumed for this inclusion.
-/

namespace TNLean.PEPS

variable {G V Phys : Type*} [Group G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The horizontal seam uses each crossed bond's own representation.
Source: SCP10, Definition 5.6 and equation `eq:2d:peps-with-ug-uh`. -/
def torusMatchedHorizontalClosureAt
    (Uh : TorusVertex width height → G →* Matrix V V ℂ) (h : G) (c : ZMod width)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  if v.1 + 1 = c then Uh v h else 1

/-- The downward vertical seam uses each crossed bond's own representation.
Source: SCP10, Definition 5.6 and equation `eq:2d:peps-with-ug-uh`. -/
def torusMatchedVerticalClosureAt
    (Uv : TorusVertex width height → G →* Matrix V V ℂ) (g : G) (r : ZMod height)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  if v.2 + 1 = r then Uv v g else 1

/-- The actual native closure with independent matching representations and
site-dependent tensors. Source: SCP10, Theorem 5.5 and Definition 5.6. -/
def matchedTorusGClosure
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (g h : G) (σ : TorusVertex width height → Phys) : ℂ :=
  torusBondNetwork (fun v t ↦ a v t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
    (torusMatchedHorizontalClosureAt Uh h 0) (torusMatchedVerticalClosureAt Uv g 0)

/-- Uniform bond representations recover the existing sitewise native closure. -/
@[simp]
theorem matchedTorusGClosure_const (U : G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ) (g h : G) :
    matchedTorusGClosure (fun _ ↦ U) (fun _ ↦ U) a g h =
      sitewiseTorusGClosure U a g h := rfl

/-- Group-valued gauge moving a cyclic seam to the column or row `c`. -/
def torusSeamGauge {n : ℕ} [NeZero n] (k : G) (c x : ZMod n) : G :=
  if x.val < c.val then k⁻¹ else 1

/-- Moving a positively oriented seam is a vertex gauge transformation. -/
theorem torusSeamGauge_horizontal {n : ℕ} [NeZero n] (k : G) (c x : ZMod n) :
    (if x + 1 = c then k else 1) =
      torusSeamGauge k c (x + 1) * (if x + 1 = 0 then k else 1) * (torusSeamGauge k c x)⁻¹ := by
  have hx := ZMod.val_lt x
  have hc := ZMod.val_lt c
  have hcast : x + 1 = ((x.val + 1 : ℕ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  by_cases h0 : x + 1 = 0
  · have hlast : x.val + 1 = n := by
      have hdiv : n ∣ x.val + 1 := (ZMod.natCast_eq_zero_iff _ _).mp (hcast.symm.trans h0)
      have := Nat.le_of_dvd (Nat.succ_pos _) hdiv
      omega
    have hnx : ¬x.val < c.val := by omega
    simp [torusSeamGauge, h0, hnx, eq_comm]
  · have hn : x.val + 1 < n := by
      have hne : x.val + 1 ≠ n := fun h => h0 (by rw [hcast, h, ZMod.natCast_self])
      omega
    have hv : (x + 1).val = x.val + 1 := by rw [hcast, ZMod.val_natCast_of_lt hn]
    have he : x + 1 = c ↔ x.val + 1 = c.val := by
      rw [← ZMod.val_injective n |>.eq_iff, hv]
    simp only [torusSeamGauge, h0, ite_false, mul_one, hv, he]
    split_ifs <;> simp_all <;> omega

/-- The downward-oriented seam uses the inverse gauge. -/
theorem torusSeamGauge_vertical {n : ℕ} [NeZero n] (k : G) (c x : ZMod n) :
    (if x + 1 = c then k else 1) =
      torusSeamGauge k⁻¹ c x * (if x + 1 = 0 then k else 1) *
        (torusSeamGauge k⁻¹ c (x + 1))⁻¹ := by
  have h := congrArg Inv.inv (torusSeamGauge_horizontal k⁻¹ c x)
  simpa only [apply_ite Inv.inv, inv_inv, inv_one, mul_inv_rev, mul_assoc] using h

/-- A seam gauge commutes with any element commuting with its label. -/
theorem torusSeamGauge_commute {n : ℕ} [NeZero n] {k l : G} (hkl : Commute k l)
    (c x : ZMod n) : Commute (torusSeamGauge k c x) l := by
  unfold torusSeamGauge
  split_ifs
  · exact hkl.inv_left
  · exact Commute.one_left l

/-- Commuting closure labels can be placed on any two seams without changing the
physical vector, with independently varying matching bond representations and
site-dependent invariant tensors. Source: SCP10, Theorem 5.5 and equation
`eq:2d:move-strings`, lines 1622–1647. -/
theorem torusBondNetwork_matchedClosureAt_eq_matchedTorusGClosure
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v x, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v x = siteMap (a v))
    (g h : G) (hgh : Commute g h) (c : ZMod width) (r : ZMod height)
    (σ : TorusVertex width height → Phys) :
    torusBondNetwork (fun v b ↦ a v b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
        (torusMatchedHorizontalClosureAt Uh h c) (torusMatchedVerticalClosureAt Uv g r) =
      matchedTorusGClosure Uh Uv a g h σ := by
  let Φh : TorusVertex width height → G := fun v ↦ torusSeamGauge h c v.1
  have hh : torusMatchedHorizontalClosureAt Uh h c =
      fun v ↦ Uh v (Φh (v.1 + 1, v.2)) *
        torusMatchedHorizontalClosureAt Uh h 0 v * Uh v (Φh v)⁻¹ := by
    funext v
    simpa only [torusMatchedHorizontalClosureAt, Φh,
      map_mul, map_one, apply_ite (Uh v)] using congrArg (Uh v) (torusSeamGauge_horizontal h c v.1)
  have hv : torusMatchedVerticalClosureAt Uv g r =
      fun v ↦ Uv v (Φh v) * torusMatchedVerticalClosureAt Uv g r v *
        Uv v (Φh (v.1, v.2 + 1))⁻¹ := by
    funext v
    have hc : Φh v * g * (Φh v)⁻¹ = g := by
      rw [(torusSeamGauge_commute hgh.symm c v.1).eq, mul_inv_cancel_right]
    simp only [torusMatchedVerticalClosureAt, Φh]
    split_ifs <;> simp [← map_mul, hc, Φh]
  have horizontal :
      torusBondNetwork (fun v b ↦ a v b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
          (torusMatchedHorizontalClosureAt Uh h c) (torusMatchedVerticalClosureAt Uv g r) =
        torusBondNetwork (fun v b ↦ a v b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
          (torusMatchedHorizontalClosureAt Uh h 0) (torusMatchedVerticalClosureAt Uv g r) := by
    calc
      _ = torusBondNetwork (fun v b ↦ a v b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
          (fun v ↦ Uh v (Φh (v.1 + 1, v.2)) *
        torusMatchedHorizontalClosureAt Uh h 0 v * Uh v (Φh v)⁻¹)
          (fun v ↦ Uv v (Φh v) * torusMatchedVerticalClosureAt Uv g r v *
            Uv v (Φh (v.1, v.2 + 1))⁻¹) := congrArg₂ _ hh hv
      _ = _ := torusBondNetwork_matchedVertexGauge Uh Uv a ha σ Φh _ _
  rw [horizontal]
  let Φv : TorusVertex width height → G := fun v ↦ torusSeamGauge g⁻¹ r v.2
  have hh' : torusMatchedHorizontalClosureAt Uh h 0 =
      fun v ↦ Uh v (Φv (v.1 + 1, v.2)) *
        torusMatchedHorizontalClosureAt Uh h 0 v * Uh v (Φv v)⁻¹ := by
    funext v
    have hc : Φv v * h * (Φv v)⁻¹ = h := by
      rw [(torusSeamGauge_commute hgh.inv_left r v.2).eq, mul_inv_cancel_right]
    simp only [torusMatchedHorizontalClosureAt, Φv]
    split_ifs <;> simp [← map_mul, hc, Φv]
  have hv' : torusMatchedVerticalClosureAt Uv g r =
      fun v ↦ Uv v (Φv v) * torusMatchedVerticalClosureAt Uv g 0 v *
        Uv v (Φv (v.1, v.2 + 1))⁻¹ := by
    funext v
    simpa only [torusMatchedVerticalClosureAt, Φv,
      map_mul, map_one, apply_ite (Uv v)] using congrArg (Uv v) (torusSeamGauge_vertical g r v.2)
  calc
    _ = torusBondNetwork (fun v b ↦ a v b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
        (fun v ↦ Uh v (Φv (v.1 + 1, v.2)) *
        torusMatchedHorizontalClosureAt Uh h 0 v * Uh v (Φv v)⁻¹)
        (fun v ↦ Uv v (Φv v) * torusMatchedVerticalClosureAt Uv g 0 v *
          Uv v (Φv (v.1, v.2 + 1))⁻¹) := congrArg₂ _ hh' hv'
    _ = _ := torusBondNetwork_matchedVertexGauge Uh Uv a ha σ Φv _ _

/-- Each matched closure has an explicit boundary tensor on every cut. The
boundary contains exactly the matrices of the representations on the cut bonds.
Source: SCP10, Theorem 5.5, the first inclusion in its proof. -/
theorem torusCutMap_matchedClosureBoundary
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap (a v))
    (g h : G) (hgh : Commute g h) (c : ZMod width) (r : ZMod height) :
    torusCutMap a c r (torusCutBondBoundary c r (fun v ↦ Uh v h) (fun v ↦ Uv v g)) =
      matchedTorusGClosure Uh Uv a g h := by
  funext σ
  rw [torusCutMap_apply, torusCutCoeff_bondBoundary]
  exact torusBondNetwork_matchedClosureAt_eq_matchedTorusGClosure Uh Uv a ha g h hgh c r σ

/-- Actual commuting closures for independent matched bond representations lie
in every actual arbitrary-boundary cut space. Source: SCP10, Theorem 5.5. -/
theorem matchedTorusGClosure_mem_torusCutSpace
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap (a v))
    (g h : G) (hgh : Commute g h) (c : ZMod width) (r : ZMod height) :
    matchedTorusGClosure Uh Uv a g h ∈ torusCutSpace a c r :=
  ⟨torusCutBondBoundary c r (fun v ↦ Uh v h) (fun v ↦ Uv v g),
    torusCutMap_matchedClosureBoundary Uh Uv a ha g h hgh c r⟩

/-- The commuting closure span with independently varying matching
representations on actual oriented bonds. Source: SCP10, Theorem 5.5. -/
def matchedCommutingClosureSpan
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ) :
    Submodule ℂ ((TorusVertex width height → Phys) → ℂ) :=
  Submodule.span ℂ (Set.range fun p : {p : G × G // Commute p.1 p.2} ↦
    matchedTorusGClosure Uh Uv a p.1.1 p.1.2)

/-- The first inclusion of the actual four-block closure theorem allows a
different matching bond representation on each of the eight native bonds.
Source: SCP10, Theorem 5.5, the first sentence of its proof. -/
theorem matchedCommutingClosureSpan_le_fourTorusCutSpace
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap (a v)) :
    matchedCommutingClosureSpan Uh Uv a ≤ fourTorusCutSpace a := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  apply (mem_fourTorusCutSpace_iff a _).mpr
  intro c r
  exact (mem_torusCutSpace_iff a c r _).mp
    (matchedTorusGClosure_mem_torusCutSpace Uh Uv a ha p.1.1 p.1.2 p.2 c r)

end TNLean.PEPS
