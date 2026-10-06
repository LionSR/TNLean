/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGClosure

/-!
# Displacing the seams of commuting torus closures

A torus closure with commuting group labels is independent of the positions of its
horizontal and vertical seams. The proof changes basis at the vertices between the old
and new seams and uses only invariance of the local tensor under the virtual group action.
The vertical change of basis is the inverse of the horizontal one, in accordance with the
downward orientation of vertical bonds.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, equation `eq:2d:move-strings`,
`Papers/1001.3807/paper_v3.tex` lines 1622–1647. This supplies seam deformation for the
commuting closure sectors used in Theorem 6.9; no entropy assertion is made here.
The source uses a square lattice; the algebraic identity also holds on rectangular tori,
including dimensions equal to one.
-/

namespace TNLean.PEPS

variable {G V Phys : Type*} [Group G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- A horizontal closure across the seam whose head column is `c`.
Source: arXiv:1001.3807, `eq:2d:move-strings`, lines 1622–1647. -/
def torusHorizontalClosureAt (U : G →* Matrix V V ℂ) (h : G) (c : ZMod width)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  if v.1 + 1 = c then U h else 1

/-- A downward vertical closure across the seam with upper row `r`.
Source: arXiv:1001.3807, `eq:2d:move-strings`, lines 1622–1647. -/
def torusVerticalClosureAt (U : G →* Matrix V V ℂ) (g : G) (r : ZMod height)
    (v : TorusVertex width height) : Matrix V V ℂ :=
  if v.2 + 1 = r then U g else 1

omit [NeZero width] [NeZero height] in
@[simp]
theorem torusHorizontalClosureAt_zero (U : G →* Matrix V V ℂ) (h : G) :
    torusHorizontalClosureAt (height := height) U h (0 : ZMod width) =
      torusHorizontalClosure U h := rfl

omit [NeZero width] [NeZero height] in
@[simp]
theorem torusVerticalClosureAt_zero (U : G →* Matrix V V ℂ) (g : G) :
    torusVerticalClosureAt (width := width) U g (0 : ZMod height) =
      torusVerticalClosure U g := rfl

private def seamGauge {n : ℕ} [NeZero n] (k : G) (c x : ZMod n) : G :=
  if x.val < c.val then k⁻¹ else 1

private theorem seamGauge_horizontal {n : ℕ} [NeZero n] (k : G) (c x : ZMod n) :
    (if x + 1 = c then k else 1) =
      seamGauge k c (x + 1) * (if x + 1 = 0 then k else 1) * (seamGauge k c x)⁻¹ := by
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
    simp [seamGauge, h0, hnx, eq_comm]
  · have hn : x.val + 1 < n := by
      have hne : x.val + 1 ≠ n := fun h => h0 (by rw [hcast, h, ZMod.natCast_self])
      omega
    have hv : (x + 1).val = x.val + 1 := by rw [hcast, ZMod.val_natCast_of_lt hn]
    have he : x + 1 = c ↔ x.val + 1 = c.val := by
      rw [← ZMod.val_injective n |>.eq_iff, hv]
    simp only [seamGauge, h0, ite_false, mul_one, hv, he]
    split_ifs <;> simp_all <;> omega

private theorem seamGauge_vertical {n : ℕ} [NeZero n] (k : G) (c x : ZMod n) :
    (if x + 1 = c then k else 1) =
      seamGauge k⁻¹ c x * (if x + 1 = 0 then k else 1) *
        (seamGauge k⁻¹ c (x + 1))⁻¹ := by
  have h := congrArg Inv.inv (seamGauge_horizontal k⁻¹ c x)
  simpa only [apply_ite Inv.inv, inv_inv, inv_one, mul_inv_rev, mul_assoc] using h

private theorem seamGauge_commute {n : ℕ} [NeZero n] {k l : G} (hkl : Commute k l)
    (c x : ZMod n) : Commute (seamGauge k c x) l := by
  unfold seamGauge
  split_ifs
  · exact hkl.inv_left
  · exact Commute.one_left l

private theorem torusBondNetwork_vertexGauge (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a)
    (σ : TorusVertex width height → Phys) (Φ : TorusVertex width height → G)
    (Oh Ov : TorusVertex width height → Matrix V V ℂ) :
    torusBondNetwork (fun v c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v ↦ U (Φ (v.1 + 1, v.2)) * Oh v * U (Φ v)⁻¹)
        (fun v ↦ U (Φ v) * Ov v * U (Φ (v.1, v.2 + 1))⁻¹) =
      torusBondNetwork (fun v c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov := by
  rw [torusBondNetwork_gauge _ Oh Ov (fun v ↦ U (Φ v)) (fun v ↦ U (Φ v)⁻¹)]
  congr 1
  funext v
  exact vecMul_torusLegMatrix_of_comp_eq U a ha (Φ v) (σ v)

/-- Commuting torus closure labels can be placed on any horizontal and vertical seams
without changing the physical vector. Only local virtual invariance is needed.
Source: arXiv:1001.3807, `eq:2d:move-strings`, lines 1622–1647, for the commuting
closure sectors used in Theorem 6.9, lines 2027–2072. -/
theorem torusBondNetwork_closureAt_eq_torusGClosure (U : G →* Matrix V V ℂ)
    (a : V → V → V → V → Phys → ℂ)
    (ha : ∀ x, siteMap a ∘ₗ torusLegRep U x = siteMap a)
    (g h : G) (hgh : Commute g h) (c : ZMod width) (r : ZMod height)
    (σ : TorusVertex width height → Phys) :
    torusBondNetwork (fun v b ↦ a b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
        (torusHorizontalClosureAt U h c) (torusVerticalClosureAt U g r) =
      torusGClosure U a g h σ := by
  let Φh : TorusVertex width height → G := fun v ↦ seamGauge h c v.1
  have hh : torusHorizontalClosureAt (height := height) U h c =
      fun v ↦ U (Φh (v.1 + 1, v.2)) * torusHorizontalClosure U h v * U (Φh v)⁻¹ := by
    funext v
    simpa only [torusHorizontalClosureAt, torusHorizontalClosure, Φh,
      map_mul, map_one, apply_ite U] using congrArg U (seamGauge_horizontal h c v.1)
  have hv : torusVerticalClosureAt (width := width) U g r =
      fun v ↦ U (Φh v) * torusVerticalClosureAt U g r v *
        U (Φh (v.1, v.2 + 1))⁻¹ := by
    funext v
    have hc : Φh v * g * (Φh v)⁻¹ = g := by
      rw [(seamGauge_commute hgh.symm c v.1).eq, mul_inv_cancel_right]
    simp only [torusVerticalClosureAt, Φh]
    split_ifs <;> simp [← map_mul, hc, Φh]
  have horizontal :
      torusBondNetwork (fun v b ↦ a b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
          (torusHorizontalClosureAt U h c) (torusVerticalClosureAt U g r) =
        torusBondNetwork (fun v b ↦ a b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
          (torusHorizontalClosure U h) (torusVerticalClosureAt U g r) := by
    calc
      _ = torusBondNetwork (fun v b ↦ a b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
          (fun v ↦ U (Φh (v.1 + 1, v.2)) * torusHorizontalClosure U h v * U (Φh v)⁻¹)
          (fun v ↦ U (Φh v) * torusVerticalClosureAt U g r v *
            U (Φh (v.1, v.2 + 1))⁻¹) := congrArg₂ _ hh hv
      _ = _ := torusBondNetwork_vertexGauge U a ha σ Φh _ _
  rw [horizontal]
  let Φv : TorusVertex width height → G := fun v ↦ seamGauge g⁻¹ r v.2
  have hh' : torusHorizontalClosure (height := height) U h =
      fun v ↦ U (Φv (v.1 + 1, v.2)) * torusHorizontalClosure U h v * U (Φv v)⁻¹ := by
    funext v
    have hc : Φv v * h * (Φv v)⁻¹ = h := by
      rw [(seamGauge_commute hgh.inv_left r v.2).eq, mul_inv_cancel_right]
    simp only [torusHorizontalClosure, Φv]
    split_ifs <;> simp [← map_mul, hc, Φv]
  have hv' : torusVerticalClosureAt (width := width) U g r =
      fun v ↦ U (Φv v) * torusVerticalClosure U g v *
        U (Φv (v.1, v.2 + 1))⁻¹ := by
    funext v
    simpa only [torusVerticalClosureAt, torusVerticalClosure, Φv,
      map_mul, map_one, apply_ite U] using congrArg U (seamGauge_vertical g r v.2)
  calc
    _ = torusBondNetwork (fun v b ↦ a b.1 b.2.1 b.2.2.1 b.2.2.2 (σ v))
        (fun v ↦ U (Φv (v.1 + 1, v.2)) * torusHorizontalClosure U h v * U (Φv v)⁻¹)
        (fun v ↦ U (Φv v) * torusVerticalClosure U g v *
          U (Φv (v.1, v.2 + 1))⁻¹) := congrArg₂ _ hh' hv'
    _ = _ := torusBondNetwork_vertexGauge U a ha σ Φv _ _

end TNLean.PEPS
