/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TNLean.PEPS.Approximation.DyadicPointTreatment

/-!
# The constants of the dyadic distribution protocol

The proof of Proposition 7.1 (`prop:protocol`) fixes its constants in one acyclic order
(`06-geometry.tex`, lines 559–570): first the band templates and their clearance constant `a₀`,
then `K₀`, then `ε₀`, then the mesh parameter `ν`, then the clearance `a`, then the information
scale constant `D` with `t = D log L`, and finally `B₀`. This file records that choice and checks
that, with `t > 0`, the separation inequalities consumed by the step lemmas hold at every scale at
once.

The radii are those of the source: the hole radius at scale `n` is `h_n = ε₀ min(n, t)`
(`holeRadius`, lines 102–117), and a patch at scale `s` has inner radius `u = ν s / 2`
(`patchRadius`), so that its outer square has radius `2 u = ν s`, the footprint radius of the
footprint-ratio theorems. The scale `s` is `n` for a direct repainting at level `n`
(lines 507–527), `N` for the resize of a hole of a guide uniform on the `N`-blocks
(lines 529–541), and `t` for a point treatment (lines 481–505).

The order is `IsProtocolConstants`. Each later constant is constrained only by smallness or
largeness conditions relative to the earlier ones, and `exists_isProtocolConstants` shows that any
family of such conditions can be met in the source's order. With `0 < t`, the inequalities are:

* direct repainting at level `n`: `3 u + 4 r < n` and `(2 (n / 2 + 2 r + u) / u + 1)² ≤ b`, the
  premises of `directRepainting_step`;
* resize on the `N`-blocks: `4 R + 3 u < N`, the premise of `exists_resize_planeConditions`, and
  `(2 (2 R + u) / u + 1)² ≤ b`, for `R = h_N`;
* point treatment at a level `n > K₀ t`: `2 t + 6 r + 3 u < n`, the premise of
  `exists_pointTreatment_planeConditions`, the local form
  `max t (t + 2 r) + 3 u + 4 r < n - t` of `exists_local_planeConditions` with `ρ₀ = ρ₁ = t` and
  `ρ₂ = n - t`, and `(2 (t + 2 r + u) / u + 1)² ≤ b`;
* `18 ≤ b` for the one patch bound `b = protocolPatchBound ε₀ ν`;
* every hole radius and every patch radius of scale at most `K₀ t`, outer radii included, is at
  most `B₀ log L` (lines 564–567).

These are collected in `ProtocolSeparations`, which holds for all sufficiently large `L`
(`IsProtocolConstants.eventually_protocolSeparations`).

## Main results

* `TNLean.PEPS.Approximation.IsProtocolConstants`
* `TNLean.PEPS.Approximation.exists_isProtocolConstants`
* `TNLean.PEPS.Approximation.ProtocolSeparations`
* `TNLean.PEPS.Approximation.IsProtocolConstants.protocolSeparations`
* `TNLean.PEPS.Approximation.IsProtocolConstants.eventually_protocolSeparations`

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the scales
  `eq:geometry-scales` (lines 102–117), the choice of `K₀` and `ε₀` (lines 341–351), the choice of
  `a` and `D` (lines 440–445), the small-patch covers (lines 447–541), and the order of the
  constants (lines 559–570).
-/

open Filter

namespace TNLean.PEPS.Approximation

/-- The inner radius `u = ν s / 2` of a patch at scale `s`: its outer square has radius `ν s`, the
footprint radius `ν s` of the footprint-ratio theorems.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 491–499 and 520–525. -/
noncomputable def patchRadius (ν s : ℝ) : ℝ := ν * s / 2

/-- One bound `b` on the number of patches of a direct repainting, a resize and a point
treatment, together with the `18` required by `directRepainting_step`:
`max 18 ⌈((4 + 8 ε₀ + 2 ν) / ν + 1)²⌉`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 498–499, 520–521 and 535–538. -/
noncomputable def protocolPatchBound (ε₀ ν : ℝ) : ℕ :=
  max 18 ⌈((4 + 8 * ε₀ + 2 * ν) / ν + 1) ^ 2⌉₊

/-- **The constants of the protocol, in the source's order.** After the band templates fix
`a₀ = angularConstant`:

* `K₀` makes the tenfold enlargements of the treated squares disjoint once `n > K₀ t`
  (lines 341–343): `20 ≤ K₀`;
* `ε₀ > 0` is small compared with `a₀` (lines 349–350 and 415): `2 ε₀ (a₀ + 1) ≤ a₀ / 2`;
* the mesh parameter `ν > 0` is small (lines 491 and 520–525): `2 ε₀ + 3 ν < 1`;
* the clearance `a > 0` is below the surviving tapering constants (line 440): `a ≤ a₀ / 2`;
* the information scale constant is positive, `0 < D` (lines 441–443);
* `B₀` is a fixed multiple of `K₀ D` (lines 564–567): `K₀ D ≤ B₀`.

The conditions coming from the compactness observation (the footprint ratios, the rim
separations) and from Proposition 3.4 are further smallness or largeness conditions on the same
constants, met in the same order by `exists_isProtocolConstants`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 559–570. -/
structure IsProtocolConstants (K₀ ε₀ ν a D B₀ : ℝ) : Prop where
  twenty_le_K₀ : 20 ≤ K₀
  ε₀_pos : 0 < ε₀
  ε₀_small : 2 * ε₀ * (angularConstant + 1) ≤ angularConstant / 2
  ν_pos : 0 < ν
  ν_small : 2 * ε₀ + 3 * ν < 1
  a_pos : 0 < a
  a_le : a ≤ angularConstant / 2
  D_pos : 0 < D
  B₀_ge : K₀ * D ≤ B₀

/-- **There is no circular choice of constants.** Let `PK`, `Pε`, `Pν`, `Pa`, `PD`, `PB` be
conditions on `K₀`, then `ε₀`, then `ν`, then `a`, then `D`, then `B₀`, each depending only on
the earlier constants: `K₀` and `B₀` large enough, `ε₀`, `ν` and `a` small enough, and some
positive `D` for each positive `a` (as Proposition 3.4 supplies). Then constants satisfying all
of them and `IsProtocolConstants` exist.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 559–570. -/
theorem exists_isProtocolConstants (PK : ℝ → Prop) (Pε : ℝ → ℝ → Prop)
    (Pν : ℝ → ℝ → ℝ → Prop) (Pa : ℝ → ℝ → ℝ → ℝ → Prop) (PD : ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (PB : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) (hK : ∃ K, ∀ K₀, K ≤ K₀ → PK K₀)
    (hε : ∀ K₀, ∃ ε > 0, ∀ ε₀, 0 < ε₀ → ε₀ ≤ ε → Pε K₀ ε₀)
    (hν : ∀ K₀ ε₀, 0 < ε₀ → ∃ ν' > 0, ∀ ν, 0 < ν → ν ≤ ν' → Pν K₀ ε₀ ν)
    (ha : ∀ K₀ ε₀ ν, 0 < ε₀ → 0 < ν → ∃ a' > 0, ∀ a, 0 < a → a ≤ a' → Pa K₀ ε₀ ν a)
    (hD : ∀ K₀ ε₀ ν a, 0 < a → ∃ D > 0, PD K₀ ε₀ ν a D)
    (hB : ∀ K₀ ε₀ ν a D, ∃ B, ∀ B₀, B ≤ B₀ → PB K₀ ε₀ ν a D B₀) :
    ∃ K₀ ε₀ ν a D B₀, IsProtocolConstants K₀ ε₀ ν a D B₀ ∧ PK K₀ ∧ Pε K₀ ε₀ ∧ Pν K₀ ε₀ ν ∧
      Pa K₀ ε₀ ν a ∧ PD K₀ ε₀ ν a D ∧ PB K₀ ε₀ ν a D B₀ := by
  have ha₀ : angularConstant = 1 / 5000 := rfl
  obtain ⟨K, hK⟩ := hK
  set K₀ := max K 20
  obtain ⟨ε, hε0, hε⟩ := hε K₀
  set ε₀ := min ε (1 / 30000)
  have hε₀ : 0 < ε₀ := lt_min hε0 (by norm_num)
  have hε₀' : ε₀ ≤ 1 / 30000 := min_le_right _ _
  obtain ⟨ν', hν0, hν⟩ := hν K₀ ε₀ hε₀
  set ν := min ν' (1 / 6)
  have hν₀ : 0 < ν := lt_min hν0 (by norm_num)
  have hν₀' : ν ≤ 1 / 6 := min_le_right _ _
  obtain ⟨a', ha0, ha⟩ := ha K₀ ε₀ ν hε₀ hν₀
  set a := min a' (angularConstant / 2)
  have ha₁ : 0 < a := lt_min ha0 (by rw [ha₀]; norm_num)
  obtain ⟨D, hD0, hD⟩ := hD K₀ ε₀ ν a ha₁
  obtain ⟨B, hB⟩ := hB K₀ ε₀ ν a D
  refine ⟨K₀, ε₀, ν, a, D, max B (K₀ * D), ⟨le_max_right _ _, hε₀, ?_, hν₀, ?_, ha₁,
    min_le_right _ _, hD0, le_max_right _ _⟩, hK _ (le_max_left _ _), hε _ hε₀ (min_le_left _ _),
    hν _ hν₀ (min_le_left _ _), ha _ ha₁ (min_le_left _ _), hD, hB _ (le_max_left _ _)⟩
  · rw [ha₀]; nlinarith
  · linarith

namespace IsProtocolConstants

variable {K₀ ε₀ ν a D B₀ : ℝ}

theorem ε₀_lt (h : IsProtocolConstants K₀ ε₀ ν a D B₀) : ε₀ < 1 / 8000 := by
  have := h.ε₀_small
  have ha₀ : angularConstant = 1 / 5000 := rfl
  rw [ha₀] at this
  linarith

theorem ν_lt_one (h : IsProtocolConstants K₀ ε₀ ν a D B₀) : ν < 1 := by
  linarith [h.ν_small, h.ε₀_pos]

end IsProtocolConstants

/-- A hole radius is at most `ε₀ n`. -/
theorem holeRadius_le_mul {ε₀ n t : ℝ} (hε : 0 ≤ ε₀) : holeRadius ε₀ n t ≤ ε₀ * n :=
  mul_le_mul_of_nonneg_left (min_le_left n t) hε

/-- A hole radius is at most `ε₀ t`. -/
theorem holeRadius_le_mul_right {ε₀ n t : ℝ} (hε : 0 ≤ ε₀) : holeRadius ε₀ n t ≤ ε₀ * t :=
  mul_le_mul_of_nonneg_left (min_le_right n t) hε

/-- A hole radius is positive for positive `ε₀`, `n` and `t`. -/
theorem holeRadius_pos {ε₀ n t : ℝ} (hε : 0 < ε₀) (hn : 0 < n) (ht : 0 < t) :
    0 < holeRadius ε₀ n t :=
  mul_pos hε (lt_min hn ht)

/-- A hole radius is nonnegative for nonnegative `ε₀`, `n` and `t`. -/
theorem holeRadius_nonneg {ε₀ n t : ℝ} (hε : 0 ≤ ε₀) (hn : 0 ≤ n) (ht : 0 ≤ t) :
    0 ≤ holeRadius ε₀ n t :=
  mul_nonneg hε (le_min hn ht)

theorem two_mul_patchRadius (ν s : ℝ) : 2 * patchRadius ν s = ν * s := by
  rw [patchRadius]; ring

theorem patchRadius_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 0 < patchRadius ν s := by
  unfold patchRadius; positivity

theorem eighteen_le_protocolPatchBound (ε₀ ν : ℝ) : 18 ≤ protocolPatchBound ε₀ ν :=
  le_max_left _ _

/-- A nonnegative number at most `(4 + 8 ε₀ + 2 ν) / ν + 1` has square at most the patch bound. -/
theorem sq_le_protocolPatchBound {ε₀ ν x : ℝ} (hx : 0 ≤ x)
    (hxb : x ≤ (4 + 8 * ε₀ + 2 * ν) / ν + 1) : x ^ 2 ≤ protocolPatchBound ε₀ ν := by
  calc x ^ 2 ≤ ((4 + 8 * ε₀ + 2 * ν) / ν + 1) ^ 2 := pow_le_pow_left₀ hx hxb 2
    _ ≤ ⌈((4 + 8 * ε₀ + 2 * ν) / ν + 1) ^ 2⌉₊ := Nat.le_ceil _
    _ ≤ protocolPatchBound ε₀ ν := by exact_mod_cast le_max_right _ _

/-- **The separations of the step lemmas at one value of `t = D log L`.** Here `ℓ = log L`, the
hole radius at scale `n` is `r = h_n = ε₀ min(n, t)`, the patch radius at scale `s` is
`u = ν s / 2`, and `b` is `protocolPatchBound ε₀ ν`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 481–570. -/
structure ProtocolSeparations (K₀ ε₀ ν B₀ t ℓ : ℝ) : Prop where
  t_pos : 0 < t
  /-- Direct repainting at level `n` (lines 507–527): the premises of `directRepainting_step`. -/
  direct : ∀ n, 0 < n → 0 < holeRadius ε₀ n t ∧ 0 < patchRadius ν n ∧
    2 * patchRadius ν n = ν * n ∧ 3 * patchRadius ν n + 4 * holeRadius ε₀ n t < n ∧
    (2 * (n / 2 + 2 * holeRadius ε₀ n t + patchRadius ν n) / patchRadius ν n + 1) ^ 2 ≤
      (protocolPatchBound ε₀ ν : ℝ)
  /-- Resize of a hole of a guide uniform on the `N`-blocks (lines 529–541), with `R = h_N` the
  larger of the two radii: the premise of `exists_resize_planeConditions` and its patch count. -/
  resize : ∀ N, 0 < N → 0 < holeRadius ε₀ N t ∧ 0 < patchRadius ν N ∧
    2 * patchRadius ν N = ν * N ∧ 4 * holeRadius ε₀ N t + 3 * patchRadius ν N < N ∧
    (2 * (2 * holeRadius ε₀ N t + patchRadius ν N) / patchRadius ν N + 1) ^ 2 ≤
      (protocolPatchBound ε₀ ν : ℝ)
  /-- Point treatment at a level `n > K₀ t` (lines 481–505): the premise of
  `exists_pointTreatment_planeConditions`, the separation of `exists_local_planeConditions`
  with `ρ₀ = ρ₁ = t` and `ρ₂ = n - t`, and the patch count. -/
  point : ∀ n, K₀ * t < n → 0 < holeRadius ε₀ n t ∧ 0 < patchRadius ν t ∧
    2 * patchRadius ν t = ν * t ∧
    2 * t + 6 * holeRadius ε₀ n t + 3 * patchRadius ν t < n ∧
    max t (t + 2 * holeRadius ε₀ n t) + 3 * patchRadius ν t + 4 * holeRadius ε₀ n t < n - t ∧
    (2 * (t + 2 * holeRadius ε₀ n t + patchRadius ν t) / patchRadius ν t + 1) ^ 2 ≤
      (protocolPatchBound ε₀ ν : ℝ)
  /-- `18 ≤ b`, the remaining premise of `directRepainting_step`. -/
  eighteen_le : 18 ≤ protocolPatchBound ε₀ ν
  /-- Every outer hole radius is at most `B₀ log L` (lines 564–567). -/
  hole_le : ∀ n, 2 * holeRadius ε₀ n t ≤ B₀ * ℓ
  /-- Every outer patch radius at a scale at most `K₀ t` is at most `B₀ log L`: the direct
  patches (`n ≤ K₀ t`), the point patches (scale `t`) and the resize patches (scale `2 n < 2 t`)
  (lines 564–567). -/
  patch_le : ∀ s, s ≤ K₀ * t → 2 * patchRadius ν s ≤ B₀ * ℓ

namespace IsProtocolConstants

variable {K₀ ε₀ ν a D B₀ : ℝ}

/-- **The separations hold at every positive `log L`.** For constants chosen in the source's
order and `ℓ > 0`, with `t = D ℓ`, every separation inequality of the step lemmas holds at once.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 481–570. -/
theorem protocolSeparations (h : IsProtocolConstants K₀ ε₀ ν a D B₀) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ProtocolSeparations K₀ ε₀ ν B₀ (D * ℓ) ℓ := by
  have hε := h.ε₀_pos
  have hε' := h.ε₀_lt
  have hν := h.ν_pos
  have hνs := h.ν_small
  have hK := h.twenty_le_K₀
  have ht : 0 < D * ℓ := mul_pos h.D_pos hℓ
  set t := D * ℓ with ht_def
  have hKt : K₀ * t ≤ B₀ * ℓ := by
    rw [ht_def, ← mul_assoc]; exact mul_le_mul_of_nonneg_right h.B₀_ge hℓ.le
  refine ⟨ht, fun n hn => ?_, fun N hN => ?_, fun n hn => ?_, eighteen_le_protocolPatchBound _ _,
    fun n => ?_, fun s hs => ?_⟩
  · -- direct repainting
    have hr0 := holeRadius_pos hε hn ht
    have hr := holeRadius_le_mul (n := n) (t := t) hε.le
    have hu := patchRadius_pos hν hn
    refine ⟨hr0, hu, two_mul_patchRadius _ _, ?_, ?_⟩
    · unfold patchRadius; nlinarith
    · refine sq_le_protocolPatchBound (by positivity) (add_le_add ?_ le_rfl)
      rw [div_le_div_iff₀ hu hν]
      unfold patchRadius at hu ⊢
      nlinarith [mul_le_mul_of_nonneg_left hr hν.le, mul_pos hν hn]
  · -- resize
    have hr0 := holeRadius_pos hε hN ht
    have hr := holeRadius_le_mul (n := N) (t := t) hε.le
    have hu := patchRadius_pos hν hN
    refine ⟨hr0, hu, two_mul_patchRadius _ _, ?_, ?_⟩
    · unfold patchRadius; nlinarith
    · refine sq_le_protocolPatchBound (by positivity) (add_le_add ?_ le_rfl)
      rw [div_le_div_iff₀ hu hν]
      unfold patchRadius at hu ⊢
      nlinarith [mul_le_mul_of_nonneg_left hr hν.le, mul_pos hν hN]
  · -- point treatment
    have htn : t ≤ n := by nlinarith
    have hn0 : 0 < n := by linarith
    have hr0 := holeRadius_pos hε hn0 ht
    have hr : holeRadius ε₀ n t = ε₀ * t := holeRadius_of_le htn
    have hu := patchRadius_pos hν ht
    have hsep : 2 * t + 6 * holeRadius ε₀ n t + 3 * patchRadius ν t < n := by
      rw [hr]; unfold patchRadius; nlinarith
    refine ⟨hr0, hu, two_mul_patchRadius _ _, hsep, ?_, ?_⟩
    · rw [max_eq_right (by linarith)]; linarith
    · refine sq_le_protocolPatchBound (by positivity) (add_le_add (le_of_eq ?_) le_rfl)
      rw [hr, patchRadius]
      field_simp
      ring
  · -- holes
    have := holeRadius_le_mul_right (n := n) (t := t) hε.le
    nlinarith
  · -- patches
    unfold patchRadius
    rcases le_total 0 s with hs0 | hs0
    · nlinarith [h.ν_lt_one]
    · nlinarith

/-- **The separations hold for all sufficiently large `L`.** For constants chosen in the source's
order, for all sufficiently large `L`, with `t = D log L`, every separation inequality of the step
lemmas holds at once, at every scale.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 481–570. -/
theorem eventually_protocolSeparations (h : IsProtocolConstants K₀ ε₀ ν a D B₀) :
    ∀ᶠ L : ℕ in atTop,
      ProtocolSeparations K₀ ε₀ ν B₀ (D * Real.log L) (Real.log L) := by
  filter_upwards [eventually_ge_atTop 2] with L hL
  refine h.protocolSeparations (Real.log_pos ?_)
  exact_mod_cast hL

end IsProtocolConstants

end TNLean.PEPS.Approximation
