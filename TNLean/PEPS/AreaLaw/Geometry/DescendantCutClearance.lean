/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairInduction
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendantScales
import TNLean.PEPS.AreaLaw.Geometry.RepairInitialMarkFacts
import TNLean.PEPS.AreaLaw.Geometry.LayerPartition
import TNLean.PEPS.AreaLaw.Geometry.BeltMarks
import TNLean.PEPS.AreaLaw.Geometry.DistanceLayers
import TNLean.PEPS.AreaLaw.Geometry.Templates
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth

/-!
# Cut clearance of belt and descendant birth templates

The belt and replacement templates of Proposition 11.2 stay far from the cut
endpoints `Z` compared with their size. An initial belt cell in the layer `D_k`
has endpoint distance at least `C₀ r`, with `r = 2 ^ k`, and so has every mark
on its closure. Every descendant birth region of an initial mark of scale
`S = t_k` lies within `2 d(S) ≤ 2 t_k ^ ρ₀` of that mark (Lemma 11.4), so for
every sufficiently large lower layer index `k₀` all descendant birth regions,
including replacements reaching into the dummy region, have endpoint distance
at least `(C₀ - 1) r`. The side scale of a belt or replacement template is at
most `2 t_k = o(r)`, so that distance exceeds both `4 D₀ s₀` and `2 n ^ β`
for the scanner scale `n = ⌈C_B u⌉`.

The template constant `D₀`, the belt scale constant `C_B` and the layer width
`C₀` are arbitrary; the threshold on `k₀` is chosen after them. In particular
the conclusions hold for every `D₀`, as the final two-family decomposition
requires.

## Main statements

* `repairStage_zero_endpoint_dist_ge`: an initial mark of scale `t_k` has
  endpoint distance at least `C₀ 2 ^ k`.
* `repairStage_birth_endpoint_dist_ge`: under the descendant bound of
  Lemma 11.4, a replacement birth region has endpoint distance at least
  `C₀ 2 ^ k - 2 d(t_k)`, where `t_k` is the scale of its initial ancestor, and
  its removal half-side is at most `t_k`.
* `Template.cutClearance_of_endpoint_dist_ge`: endpoint distance at least
  `(C₀ - 1) 2 ^ k` gives both template clearances once the side scale is at most
  `2 t_k` and the layer is late.
* `initialBelt_birthTemplate_cutClearance`: the clearances for initial belt tiles.
* `descendant_birthTemplate_cutClearance`: the clearances for every replacement.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, lines 742–750, with
  `geometry:layer-distance` (lines 179–189), the belt and replacement scanner
  scales (lines 732–740), and Lemma 11.4 (`geometry:repair-induction`,
  lines 471–485).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Scalar estimates -/

/-- The fine side `t_k = 2 ^ ⌊ζ k⌋` is at most `(2 ^ k) ^ ζ`.
Source: area-law Section 11, lines 200–207. -/
theorem two_pow_fineScaleIndex_le_rpow (k : ℕ) :
    (2 : ℝ) ^ fineScaleIndex k ≤ ((2 : ℝ) ^ k) ^ (Exponents.zeta : ℝ) := by
  have hζ : (0 : ℝ) ≤ (Exponents.zeta : ℝ) := by
    norm_num [Exponents.zeta, Exponents.geometryDelta]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [mul_comm]
  exact Nat.floor_le (mul_nonneg hζ (Nat.cast_nonneg k))

/-- Beyond the power-ratio threshold `P(M, 1/2, 1 - a)`, `M R ^ a < R`. -/
private theorem mul_rpow_lt_of_powerRatioThreshold_le {M a R : ℝ} (hM : 0 ≤ M) (ha : a < 1)
    (hR : Real.powerRatioThreshold M (1 / 2) (1 - a) ≤ R) : M * R ^ a < R := by
  have hR0 : 0 < R := one_pos.trans_le ((Real.one_le_powerRatioThreshold _ _ _).trans hR)
  have h := Real.mul_rpow_le_mul_rpow_of_powerRatioThreshold_le hM (by norm_num) ha hR
  rw [Real.rpow_one] at h
  linarith

/-- The layer threshold for the descendant cut-clearance scale inequalities: the
dyadic index of the largest of the power-ratio thresholds for
`2 R ^ (ζ ρ₀) ≤ R / 2`, `8 max(D₀, 0) R ^ ζ ≤ R / 2` and
`2 (max C_B 0 + 1) ^ β R ^ (ζ β) ≤ R / 2`, at `R = 2 ^ k`. Auxiliary to the
explicit constant of Theorem 1.1 (`docs/notes/arealaw2d_explicit_constant.tex`,
rows 37–38). -/
def descendantCutClearanceThreshold (D₀ CB : ℝ) : ℕ :=
  dyadicIndexThreshold (max
    (Real.powerRatioThreshold 2 (1 / 2) (1 - (Exponents.zeta : ℝ) * Exponents.rho))
    (max (Real.powerRatioThreshold (8 * max D₀ 0) (1 / 2) (1 - (Exponents.zeta : ℝ)))
      (Real.powerRatioThreshold (2 * (max CB 0 + 1) ^ (Exponents.beta : ℝ)) (1 / 2)
        (1 - (Exponents.zeta : ℝ) * Exponents.beta))))

/-- **The scale inequalities for late layers, explicitly.** Every layer
`k ≥ descendantCutClearanceThreshold D₀ C_B` satisfies `2 t_k ^ ρ₀ ≤ 2 ^ k`,
`4 D₀ (2 t_k) < 2 ^ k` and `2 ⌈C_B t_k⌉ ^ β < 2 ^ k`.
Source: area-law Section 11, lines 742–750, with the scanner scales of
lines 732–737. -/
theorem descendant_cutClearance_scales_of_le {D₀ CB : ℝ} {k : ℕ}
    (hk : descendantCutClearanceThreshold D₀ CB ≤ k) :
    2 * ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) ≤ (2 : ℝ) ^ k ∧
      4 * D₀ * (2 * (2 : ℝ) ^ fineScaleIndex k) < (2 : ℝ) ^ k ∧
      2 * (⌈CB * (2 : ℝ) ^ fineScaleIndex k⌉₊ : ℝ) ^ (Exponents.beta : ℝ) <
        (2 : ℝ) ^ k := by
  have hζ0 : (0 : ℝ) ≤ (Exponents.zeta : ℝ) := by
    norm_num [Exponents.zeta, Exponents.geometryDelta]
  have hζ1 : (Exponents.zeta : ℝ) < 1 := by exact_mod_cast Exponents.geometry_gaps.2.1
  have hρ0 : (0 : ℝ) ≤ (Exponents.rho : ℝ) := rho_pos_lt_one.1.le
  have hρ1 : (Exponents.rho : ℝ) < 1 := rho_pos_lt_one.2
  have hβ0 : (0 : ℝ) ≤ (Exponents.beta : ℝ) := by
    norm_num [Exponents.beta, Exponents.boxError]
  have hβ1 : (Exponents.beta : ℝ) < 1 := by
    have h := Exponents.geometry_gaps.2.2.2.2
    have : (Exponents.beta : ℝ) < (Exponents.rho : ℝ) := by exact_mod_cast h.1
    linarith
  have hzρ : (Exponents.zeta : ℝ) * (Exponents.rho : ℝ) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hζ0 hρ1.le) hζ1
  have hzβ : (Exponents.zeta : ℝ) * (Exponents.beta : ℝ) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hζ0 hβ1.le) hζ1
  set B := max CB 0 + 1 with hB
  have hB1 : 1 ≤ B := by have := le_max_right CB 0; linarith
  have hRT := le_two_pow_of_dyadicIndexThreshold_le hk
  have h₁ := mul_rpow_lt_of_powerRatioThreshold_le (by norm_num) hzρ
    ((le_max_left _ _).trans hRT)
  have h₂ := mul_rpow_lt_of_powerRatioThreshold_le (by positivity) hζ1
    (((le_max_left _ _).trans (le_max_right _ _)).trans hRT)
  have h₃ := mul_rpow_lt_of_powerRatioThreshold_le (by positivity) hzβ
    (((le_max_right _ _).trans (le_max_right _ _)).trans hRT)
  set R : ℝ := (2 : ℝ) ^ k
  set t : ℝ := (2 : ℝ) ^ fineScaleIndex k
  have hR0 : 0 ≤ R := by positivity
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  have ht0 : 0 ≤ t := by linarith
  have htR : t ≤ R ^ (Exponents.zeta : ℝ) := two_pow_fineScaleIndex_le_rpow k
  have hpow (e : ℝ) (he : 0 ≤ e) : t ^ e ≤ R ^ ((Exponents.zeta : ℝ) * e) := by
    rw [Real.rpow_mul hR0]
    exact Real.rpow_le_rpow ht0 htR he
  refine ⟨?_, ?_, ?_⟩
  · calc 2 * t ^ (Exponents.rho : ℝ) ≤ 2 * R ^ ((Exponents.zeta : ℝ) * Exponents.rho) := by
          gcongr
          exact hpow _ hρ0
      _ ≤ R := h₁.le
  · calc 4 * D₀ * (2 * t) ≤ 8 * max D₀ 0 * t := by
          nlinarith [le_max_left D₀ 0]
      _ ≤ 8 * max D₀ 0 * R ^ (Exponents.zeta : ℝ) := by
          gcongr
      _ < R := h₂
  · have hceil : (⌈CB * t⌉₊ : ℝ) ≤ B * t := by
      have hmono : (⌈CB * t⌉₊ : ℝ) ≤ ⌈max CB 0 * t⌉₊ := by
        exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left CB 0) ht0)
      have hlt := Nat.ceil_lt_add_one (mul_nonneg (le_max_right CB 0) ht0)
      nlinarith
    calc 2 * (⌈CB * t⌉₊ : ℝ) ^ (Exponents.beta : ℝ)
        ≤ 2 * (B * t) ^ (Exponents.beta : ℝ) := by
          gcongr
      _ = 2 * B ^ (Exponents.beta : ℝ) * t ^ (Exponents.beta : ℝ) := by
          rw [Real.mul_rpow (by linarith) ht0]
          ring
      _ ≤ 2 * B ^ (Exponents.beta : ℝ) * R ^ ((Exponents.zeta : ℝ) * Exponents.beta) := by
          gcongr
          exact hpow _ hβ0
      _ < R := h₃

/-- **The scale inequalities for late layers.** For every `D₀` and `C_B`, every
sufficiently late layer `k` satisfies `2 t_k ^ ρ₀ ≤ 2 ^ k`,
`4 D₀ (2 t_k) < 2 ^ k` and `2 ⌈C_B t_k⌉ ^ β < 2 ^ k`, because
`t_k ≤ (2 ^ k) ^ ζ` with `ζ < 1`, `ρ₀ < 1` and `β < 1`. The threshold is
`descendantCutClearanceThreshold D₀ C_B`.
Source: area-law Section 11, lines 742–750 (`2 t_k ^ ρ₀ = o(t_k)`, side scales
`≤ 2 t_k = o(r)`), with the scanner scales `n = ⌈C_B u⌉` of lines 732–737. -/
theorem eventually_descendant_cutClearance_scales (D₀ CB : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      2 * ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) ≤ (2 : ℝ) ^ k ∧
      4 * D₀ * (2 * (2 : ℝ) ^ fineScaleIndex k) < (2 : ℝ) ^ k ∧
      2 * (⌈CB * (2 : ℝ) ^ fineScaleIndex k⌉₊ : ℝ) ^ (Exponents.beta : ℝ) < (2 : ℝ) ^ k :=
  eventually_atTop.2 ⟨descendantCutClearanceThreshold D₀ CB,
    fun _ hk ↦ descendant_cutClearance_scales_of_le hk⟩

/-- A repair half-side of a scale at least one is at least one. -/
private theorem one_le_repairHalfSide {S : ℝ} (hS : 1 ≤ S) : 1 ≤ repairHalfSide S :=
  one_le_zpow₀ (by norm_num)
    (Int.floor_nonneg.mpr (mul_nonneg rho_pos_lt_one.1.le (Real.logb_nonneg one_lt_two hS)))

/-- A repair half-side of a scale at least one is at most that scale. -/
private theorem repairHalfSide_le_self {S : ℝ} (hS : 1 ≤ S) : repairHalfSide S ≤ S :=
  (repairHalfSide_le_rpow (by linarith)).trans
    ((Real.rpow_le_rpow_of_exponent_le hS rho_pos_lt_one.2.le).trans_eq (Real.rpow_one S))

/-- Iterated repair half-sides of a scale at least one stay between one and that scale. -/
private theorem repairHalfSide_iterate_mem {S : ℝ} (hS : 1 ≤ S) :
    ∀ n : ℕ, 1 ≤ repairHalfSide^[n] S ∧ repairHalfSide^[n] S ≤ S
  | 0 => ⟨hS, le_rfl⟩
  | n + 1 => by
    obtain ⟨h₁, h₂⟩ := repairHalfSide_iterate_mem hS n
    rw [Function.iterate_succ_apply']
    exact ⟨one_le_repairHalfSide h₁, (repairHalfSide_le_self h₁).trans h₂⟩

/-- The real sup distance of two lattice points is their integer sup distance. -/
private theorem dist_integerPoint_eq (t z : ℤ × ℤ) :
    dist (integerPoint t) (integerPoint z) = (Scan.ambientSupDistance t z : ℝ) := by
  simp [integerPoint, Prod.dist_eq, Real.dist_eq, Scan.ambientSupDistance]

/-! ### Template clearances from endpoint distance -/

/-- **Both template clearances from the endpoint distance.** Let a template
lie at endpoint distance at least `(C₀ - 1) 2 ^ k` with `C₀ ≥ 2`, and let its
piece size and scanner scale satisfy `s₀ ≤ 2 u` and `n ≤ ⌈C_B u⌉` for some
`0 ≤ u ≤ t_k`. If the layer `k` satisfies the late-layer inequalities
`4 D₀ (2 t_k) < 2 ^ k` and `2 ⌈C_B t_k⌉ ^ β < 2 ^ k`, the template satisfies
the clearance `dist_∞(T, Z) > 4 D₀ s₀` of Definition 9.3 and the cut clearance
`dist_∞(T, Z) > 2 n ^ β` of `geometry:cut-clearance`.
Source: area-law Section 11, lines 748–750; Definition 9.3 (`scanner:template`)
and `prop:two-families`, `geometry:cut-clearance`, lines 119–128. -/
theorem Template.cutClearance_of_endpoint_dist_ge {Ctpl D₀ CB u : ℝ} {n s₀ : ℕ}
    {Z : Finset (ℤ × ℤ)} {k C : ℕ} (T : Template Ctpl n s₀) (hC : 2 ≤ C)
    (hk₁ : 4 * D₀ * (2 * (2 : ℝ) ^ fineScaleIndex k) < (2 : ℝ) ^ k)
    (hk₂ : 2 * (⌈CB * (2 : ℝ) ^ fineScaleIndex k⌉₊ : ℝ) ^ (Exponents.beta : ℝ) < (2 : ℝ) ^ k)
    (hu₀ : 0 ≤ u) (hu : u ≤ (2 : ℝ) ^ fineScaleIndex k)
    (hdist : ∀ t ∈ T.points, ∀ z ∈ Z,
      ((C : ℝ) - 1) * 2 ^ k ≤ dist (integerPoint t) (integerPoint z))
    (hs : (s₀ : ℝ) ≤ 2 * u) (hn : n ≤ ⌈CB * u⌉₊) :
    T.IsSeparated D₀ Z ∧ ∀ t ∈ T.points, ∀ z ∈ Z,
      2 * (n : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t z : ℝ) := by
  set R : ℝ := (2 : ℝ) ^ k
  set tk : ℝ := (2 : ℝ) ^ fineScaleIndex k
  have hR0 : 0 < R := by positivity
  have hC1 : (1 : ℝ) ≤ (C : ℝ) - 1 := by
    have : (2 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  have hRle : R ≤ ((C : ℝ) - 1) * R := le_mul_of_one_le_left hR0.le hC1
  have hfar : ∀ t ∈ T.points, ∀ z ∈ Z, R ≤ (Scan.ambientSupDistance t z : ℝ) :=
    fun t ht z hz ↦ hRle.trans ((hdist t ht z hz).trans_eq (dist_integerPoint_eq t z))
  refine ⟨fun t ht z hz ↦ ?_, fun t ht z hz ↦ ?_⟩
  · have hD : 4 * D₀ * s₀ < R := by
      rcases le_or_gt 0 D₀ with hD₀ | hD₀
      · calc 4 * D₀ * s₀ ≤ 4 * D₀ * (2 * tk) := by
              gcongr
              linarith
          _ < R := hk₁
      · have : 4 * D₀ * (s₀ : ℝ) ≤ 0 := by
          nlinarith [Nat.cast_nonneg (α := ℝ) s₀]
        linarith
    have h := hfar t ht z hz
    rw [← dist_integerPoint_eq] at h
    simp only [integerPoint, Prod.dist_eq, Real.dist_eq] at h
    linarith
  · have hn' : n ≤ ⌈CB * tk⌉₊ := by
      refine hn.trans ?_
      rcases le_or_gt 0 CB with hCB | hCB
      · exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hu hCB)
      · have : ⌈CB * u⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by nlinarith)
        omega
    have hβ0 : (0 : ℝ) ≤ (Exponents.beta : ℝ) := by
      norm_num [Exponents.beta, Exponents.boxError]
    have hpow : (n : ℝ) ^ (Exponents.beta : ℝ) ≤ (⌈CB * tk⌉₊ : ℝ) ^ (Exponents.beta : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn') hβ0
    linarith [hfar t ht z hz]

/-! ### Endpoint distance of initial marks and descendants -/

section Stages

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- **An initial mark is far from the cut.** Every initial mark is a mark of a
belt cell of some layer `k ≥ k₀` whose fine side `t_k` is the mark's scale, and
it lies at endpoint distance at least `C₀ 2 ^ k`.
Source: area-law Section 11, lines 743–745 ("an initial belt cell in `D_k` has
endpoint distance at least `C₀ r`; a mark on its closure has the same lower
bound"), with `geometry:layer-distance`, lines 179–189, and the initial marks,
lines 325–330. -/
theorem repairStage_zero_endpoint_dist_ge (p : (𝔇 0).markIndex) :
    ∃ k, k₀ ≤ k ∧ (𝔇 0).scale p = (2 : ℝ) ^ fineScaleIndex k ∧
      ∀ z ∈ boundaryEndpoints Λ A,
        (C : ℝ) * 2 ^ k ≤ dist ((𝔇 0).location p) (integerPoint z) := by
  have hspec := initialRepairStage_mark_spec o Λ A C k₀ hC h₀
  dsimp only at hspec
  obtain ⟨-, -, hinc, -⟩ := hspec
  obtain ⟨-, k, w, hk, hw, hloc, hscale⟩ := hinc p
  refine ⟨k, hk, hscale, fun z hz ↦ dyadicLayer_dist_lower o k _ C _ ?_ z hz⟩
  exact closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
    (fineScaleIndex k) _ C w (fineScaleIndex_le k) (Finset.mem_filter.mp hw).1)
    (beltCellMarks_subset_closure_dyadicCell o _ w (Finset.mem_coe.mpr hloc))

/-- **A descendant birth region is far from the cut.** Assume the descendant
bound of Lemma 11.4 for the repair stages. Let a replacement of generation
`j + 1` have parent mark `m`, and let its initial ancestor have scale `t_k`,
for a layer `k ≥ k₀`. Then the removal half-side `d(S_m)` is at most `t_k`,
and every point of the replacement's birth region has endpoint distance at
least `C₀ 2 ^ k - 2 d(t_k)`. No layer of the birth region is used, so this
covers replacements extending into the dummy region.
Source: area-law Section 11, lines 745–750, with the descendant bound of
Lemma 11.4 (`geometry:repair-induction`, lines 482–484) and the child scales
`d(S)`, lines 380–409. -/
theorem repairStage_birth_endpoint_dist_ge {a₀ : ℝ}
    (hU : IsUniformRepairInduction o Λ A C k₀ hC h₀ Sstar a₀) (j : ℕ)
    (x : (𝔇 (j + 1)).regionIndex) (m : (𝔇 j).markIndex)
    (hx : repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m) :
    ∃ k, k₀ ≤ k ∧ repairHalfSide ((𝔇 j).scale m) ≤ (2 : ℝ) ^ fineScaleIndex k ∧
      ∀ y ∈ (𝔇 (j + 1)).birth x, ∀ z ∈ boundaryEndpoints Λ A,
        (C : ℝ) * 2 ^ k - 2 * repairHalfSide ((2 : ℝ) ^ fineScaleIndex k) ≤
          dist y (integerPoint z) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = 0 + n := ⟨j, (zero_add j).symm⟩
  have hiter := repairStage_scale_eq_iterate o Λ A C k₀ hC h₀ Sstar 0 n m
  have hball := fun y (hy : y ∈ (𝔇 (0 + n + 1)).birth x) ↦
    hU.birth_descendant_subset 0 n x m hx hy
  generalize repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 n m = q at hiter hball
  obtain ⟨k, hk, hscale, hfar⟩ := repairStage_zero_endpoint_dist_ge o Λ A C k₀ hC h₀ Sstar q
  have ht1 : (1 : ℝ) ≤ (2 : ℝ) ^ fineScaleIndex k := one_le_pow₀ (by norm_num)
  refine ⟨k, hk, ?_, fun y hy z hz ↦ ?_⟩
  · rw [hiter, hscale, ← Function.iterate_succ_apply' repairHalfSide n]
    exact (repairHalfSide_iterate_mem ht1 (n + 1)).2
  · have hb := hball y hy
    rw [Metric.mem_closedBall, hscale] at hb
    have htri := dist_triangle ((𝔇 0).location q) y (integerPoint z)
    rw [dist_comm ((𝔇 0).location q) y] at htri
    linarith [hfar z hz]

end Stages

/-! ### Cut clearance of belt and descendant templates -/

/-- **Cut clearance of initial belt birth templates, with an explicit layer
threshold.** For every lower layer index `k₀ ≥ descendantCutClearanceThreshold D₀ C_B`,
every belt tile of a layer `k ≥ k₀` has birth region at endpoint distance at least
`C₀ 2 ^ k`, and every template whose points lie in that birth region, with piece
size `s₀ ≤ 2 t_k` and scanner scale `n ≤ ⌈C_B t_k⌉`, satisfies
`dist_∞(T, Z) > 4 D₀ s₀` and `dist_∞(T, Z) > 2 n ^ β`.
Source: area-law Section 11, lines 742–744 and 748–750, with the belt scanner
scales of lines 732–733 and `geometry:layer-distance` (lines 179–189). -/
theorem initialBelt_birthTemplate_cutClearance_of_le {D₀ CB : ℝ} (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hK₀ : descendantCutClearanceThreshold D₀ CB ≤ k₀) :
    ∀ (x : InitialRegionIndex o k₀ Z C a b hC h₀) s, x = Sum.inr (Sum.inr s) →
      (∀ y ∈ initialBirthRegion o k₀ Z C a b hC h₀ x, ∀ w ∈ Z,
        (C : ℝ) * 2 ^ s.1.val ≤ dist y (integerPoint w)) ∧
      ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
        (∀ t ∈ T.points, integerPoint t ∈ initialBirthRegion o k₀ Z C a b hC h₀ x) →
        (s₀ : ℝ) ≤ 2 * (2 : ℝ) ^ fineScaleIndex s.1.val →
        n ≤ ⌈CB * (2 : ℝ) ^ fineScaleIndex s.1.val⌉₊ →
        T.IsSeparated D₀ Z ∧ ∀ t ∈ T.points, ∀ w ∈ Z,
          2 * (n : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t w : ℝ) := by
  intro x s hxs
  obtain ⟨⟨k, hk⟩, ⟨z, hz⟩, R⟩ := s
  subst hxs
  have hfar : ∀ y ∈ initialBirthRegion o k₀ Z C a b hC h₀ (.inr (.inr ⟨⟨k, hk⟩, ⟨z, hz⟩, R⟩)),
      ∀ w ∈ Z, (C : ℝ) * 2 ^ k ≤ dist y (integerPoint w) := by
    intro y hy w hw
    have hcell : y ∈ closure (dyadicCell o (fineScaleIndex k) z) := by
      rw [← cellFanRunRegions_cover]
      exact Set.mem_iUnion.mpr ⟨R, hy⟩
    exact dyadicLayer_dist_lower o k Z C y
      (closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
        (fineScaleIndex k) Z C z (fineScaleIndex_le k) (Finset.mem_filter.mp hz).1) hcell) w hw
  refine ⟨hfar, fun T hT hs hn ↦ ?_⟩
  obtain ⟨-, hk₁, hk₂⟩ := descendant_cutClearance_scales_of_le (hK₀.trans hk)
  have hu₀ : (0 : ℝ) ≤ (2 : ℝ) ^ fineScaleIndex k := by positivity
  refine T.cutClearance_of_endpoint_dist_ge hC hk₁ hk₂ hu₀ le_rfl
    (fun t ht w hw ↦ ?_) (by linarith) hn
  have : ((C : ℝ) - 1) * 2 ^ k ≤ (C : ℝ) * 2 ^ k := by
    have : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith
  exact this.trans (hfar _ (hT t ht) w hw)

/-- **Cut clearance of initial belt birth templates.** For every `D₀` and `C_B`
there is a threshold such that, for every lower layer index `k₀` beyond it, the
following holds for every belt tile of a layer `k ≥ k₀`. Its birth region has
endpoint distance at least `C₀ 2 ^ k`. Every template whose points lie in that
birth region, with piece size `s₀ ≤ 2 t_k` and scanner scale `n ≤ ⌈C_B t_k⌉`
(in particular the belt choice `s₀ = u = t_k`, `n = ⌈C_B u⌉`), satisfies
`dist_∞(T, Z) > 4 D₀ s₀` and `dist_∞(T, Z) > 2 n ^ β`.
Source: area-law Section 11, lines 742–744 and 748–750, with the belt scanner
scales of lines 732–733, `geometry:layer-distance` (lines 179–189), and the
choice of `k₀` after `C₀` and `C_B` (lines 756–774). The threshold is
`descendantCutClearanceThreshold D₀ C_B`
(`initialBelt_birthTemplate_cutClearance_of_le`). -/
theorem initialBelt_birthTemplate_cutClearance (D₀ CB : ℝ) :
    ∃ K : ℕ, ∀ (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
      (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
      (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
      ∀ (x : InitialRegionIndex o k₀ Z C a b hC h₀) s, x = Sum.inr (Sum.inr s) →
        (∀ y ∈ initialBirthRegion o k₀ Z C a b hC h₀ x, ∀ w ∈ Z,
          (C : ℝ) * 2 ^ s.1.val ≤ dist y (integerPoint w)) ∧
        ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
          (∀ t ∈ T.points, integerPoint t ∈ initialBirthRegion o k₀ Z C a b hC h₀ x) →
          (s₀ : ℝ) ≤ 2 * (2 : ℝ) ^ fineScaleIndex s.1.val →
          n ≤ ⌈CB * (2 : ℝ) ^ fineScaleIndex s.1.val⌉₊ →
          T.IsSeparated D₀ Z ∧ ∀ t ∈ T.points, ∀ w ∈ Z,
            2 * (n : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t w : ℝ) :=
  ⟨_, fun o k₀ Z C a b hC h₀ hK₀ ↦
    initialBelt_birthTemplate_cutClearance_of_le o k₀ Z C a b hC h₀ hK₀⟩

/-- **Cut clearance of descendant birth templates, with explicit thresholds.**
For every stopping scale `S_* ≥ repairMarginThreshold (1/128)`, every layer
width `C₀`, every template constant `D₀`, every belt scale constant `C_B` and
every lower layer index `k₀` at least `fineScaleIndexThreshold S_*` and
`descendantCutClearanceThreshold D₀ C_B`, the conclusion of
`descendant_birthTemplate_cutClearance` holds for every replacement.
Source: area-law Section 11, lines 742–750, with the replacement scanner scales
of lines 735–737 and Lemma 11.4 (`geometry:repair-induction`, lines 471–485). -/
theorem descendant_birthTemplate_cutClearance_of_le {Sstar : ℝ}
    (hS : repairMarginThreshold (1 / 128) ≤ Sstar) (C : ℕ) (D₀ CB : ℝ) (o : ℝ × ℝ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hK : max (fineScaleIndexThreshold Sstar) (descendantCutClearanceThreshold D₀ CB) ≤ k₀) :
    ∀ (j : ℕ) (x : (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).regionIndex)
      (m : (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex),
      repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m →
      ∃ k, k₀ ≤ k ∧
        repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m) ≤
          (2 : ℝ) ^ fineScaleIndex k ∧
        (∀ y ∈ (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).birth x,
          ∀ z ∈ boundaryEndpoints Λ A,
            ((C : ℝ) - 1) * 2 ^ k ≤ dist y (integerPoint z)) ∧
        ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
          (∀ t ∈ T.points,
            integerPoint t ∈ (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).birth x) →
          (s₀ : ℝ) ≤ 2 * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m) →
          n ≤ ⌈CB * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m)⌉₊ →
          T.IsSeparated D₀ (boundaryEndpoints Λ A) ∧
            ∀ t ∈ T.points, ∀ z ∈ boundaryEndpoints Λ A,
              2 * (n : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t z : ℝ) := by
  intro j x m hx
  have hU := isUniformRepairInduction_of_le hS o Λ A C k₀ hC h₀ (le_of_max_le_left hK)
  obtain ⟨k, hk, hu, hdist⟩ :=
    repairStage_birth_endpoint_dist_ge o Λ A C k₀ hC h₀ Sstar hU j x m hx
  obtain ⟨hk₀, hk₁, hk₂⟩ := descendant_cutClearance_scales_of_le ((le_of_max_le_right hK).trans hk)
  have hd : 2 * repairHalfSide ((2 : ℝ) ^ fineScaleIndex k) ≤ (2 : ℝ) ^ k :=
    (mul_le_mul_of_nonneg_left (repairHalfSide_le_rpow (by positivity)) (by norm_num)).trans hk₀
  have hfar : ∀ y ∈ (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).birth x,
      ∀ z ∈ boundaryEndpoints Λ A, ((C : ℝ) - 1) * 2 ^ k ≤ dist y (integerPoint z) := by
    intro y hy z hz
    linarith [hdist y hy z hz]
  refine ⟨k, hk, hu, hfar, fun T hT hs hn ↦ ?_⟩
  exact T.cutClearance_of_endpoint_dist_ge hC hk₁ hk₂ (repairHalfSide_pos _).le hu
    (fun t ht z hz ↦ hfar _ (hT t ht) z hz) hs hn

/-- **Cut clearance of descendant birth templates.** There is a stopping-scale
threshold such that, for every stopping scale `S_*` beyond it, every layer
width `C₀`, every template constant `D₀` and every belt scale constant `C_B`,
there is a threshold such that, for every lower layer index `k₀` beyond it, the
following holds for every replacement of every generation `j + 1`, with parent
mark `m` and removal half-side `u = d(S_m)`. Its initial ancestor belongs to a
layer `k ≥ k₀` with `u ≤ t_k`; its birth region has endpoint distance at least
`(C₀ - 1) 2 ^ k`, including when it extends into the dummy region; and every
template whose points lie in that birth region, with piece size `s₀ ≤ 2 u` and
scanner scale `n ≤ ⌈C_B u⌉` (in particular the replacement choice `s₀ = 2u`,
`n = ⌈C_B u⌉`), satisfies `dist_∞(T, Z) > 4 D₀ s₀` and `dist_∞(T, Z) > 2 n ^ β`.
Source: area-law Section 11, lines 742–750, with the replacement scanner scales
of lines 735–737, Lemma 11.4 (`geometry:repair-induction`, lines 471–485), and
the choice of `S_*` and then `k₀` after `C₀` and `C_B` (lines 756–774). The
thresholds are `repairMarginThreshold (1/128)` and the larger of
`fineScaleIndexThreshold S_*` and `descendantCutClearanceThreshold D₀ C_B`
(`descendant_birthTemplate_cutClearance_of_le`). -/
theorem descendant_birthTemplate_cutClearance :
    ∃ T₀ : ℝ, ∀ Sstar : ℝ, T₀ ≤ Sstar → ∀ (C : ℕ) (D₀ CB : ℝ), ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
        ∀ (j : ℕ) (x : (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).regionIndex)
          (m : (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex),
          repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m →
          ∃ k, k₀ ≤ k ∧
            repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m) ≤
              (2 : ℝ) ^ fineScaleIndex k ∧
            (∀ y ∈ (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).birth x,
              ∀ z ∈ boundaryEndpoints Λ A,
                ((C : ℝ) - 1) * 2 ^ k ≤ dist y (integerPoint z)) ∧
            ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
              (∀ t ∈ T.points,
                integerPoint t ∈ (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).birth x) →
              (s₀ : ℝ) ≤ 2 * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m) →
              n ≤ ⌈CB * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m)⌉₊ →
              T.IsSeparated D₀ (boundaryEndpoints Λ A) ∧
                ∀ t ∈ T.points, ∀ z ∈ boundaryEndpoints Λ A,
                  2 * (n : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t z : ℝ) :=
  ⟨_, fun _ hS C D₀ CB ↦ ⟨_, descendant_birthTemplate_cutClearance_of_le hS C D₀ CB⟩⟩

end TNLean.PEPS.AreaLaw.Geometry
