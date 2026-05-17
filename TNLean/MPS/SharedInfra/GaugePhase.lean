/- 
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.PeripheralToSpectralGap
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.SpectralGapNT
import TNLean.Topology.TendstoHelpers

import Mathlib.Data.Real.Sqrt

/-!
# Shared gauge-phase lemmas for MPS tensors

This module collects the generic gauge-phase identities used by both the
single-block proportional FT and the canonical-form equal-norm argument.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- If `B i = ζ • (X * A i * X⁻¹)` then `mpv B σ = ζ^N * mpv A σ`. -/
theorem mpv_eq_pow_mul_of_gaugePhase
    (A B : MPSTensor d D)
    (X : GL (Fin D) ℂ) (ζ : ℂ)
    (hX :
      ∀ i : Fin d,
        B i =
          ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ := by
  intro N σ
  classical
  set w : List (Fin d) := List.ofFn σ
  have hwlen : w.length = N := by
    simp [w]
  let C : MPSTensor d D := fun i =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hB : B = fun i => ζ • C i := by
    funext i
    simpa [C] using hX i
  have hGauge :
      evalWord C w =
        (X : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [C] using (evalWord_gauge (A := A) (B := C) X (by intro i; rfl) w)
  have htrace : Matrix.trace (evalWord C w) = Matrix.trace (evalWord A w) := by
    simpa [hGauge, Matrix.mul_assoc] using (trace_conj_eq (X := X) (M := evalWord A w))
  calc
    mpv B σ = Matrix.trace (evalWord B w) := by
      simp [mpv, coeff, w]
    _ = Matrix.trace (evalWord (fun i => ζ • C i) w) := by
      simp [hB]
    _ = Matrix.trace ((ζ ^ w.length) • evalWord C w) := by
          simpa using congrArg Matrix.trace (evalWord_smul (ζ := ζ) (A := C) w)
    _ = (ζ ^ w.length) * Matrix.trace (evalWord C w) := by
          simp [Matrix.trace_smul, smul_eq_mul]
    _ = (ζ ^ w.length) * Matrix.trace (evalWord A w) := by
          simp [htrace]
    _ = ζ ^ N * mpv A σ := by
          simp [mpv, coeff, w, hwlen]

/-- If `mpv B σ = ζ ^ N * mpv A σ` for every system size `N` and configuration `σ`, then the
self-overlap of `B` scales by `(ζ * conj ζ) ^ N` times the self-overlap of `A`. -/
theorem mpvOverlap_self_scale_of_mpv_eq_pow_mul
    {D D' : ℕ} {A : MPSTensor d D} {B : MPSTensor d D'} {ζ : ℂ}
    (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ,
      mpvOverlap (d := d) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N := by
  intro N
  classical
  simp only [mpvOverlap]
  simp_rw [hmpv N, star_mul, star_pow]
  simp_rw [show star ζ = starRingEnd ℂ ζ from rfl]
  simp_rw [show ∀ x : Cfg d N,
      ζ ^ N * mpv A x * (star (mpv A x) * (starRingEnd ℂ ζ) ^ N) =
        ζ ^ N * (starRingEnd ℂ ζ) ^ N * (mpv A x * star (mpv A x)) from
      fun x => by ring]
  rw [← Finset.mul_sum, mul_pow]

/-- If two self-overlaps both have norm limit `1`, and one scales from the other by powers of
`ζ * conj ζ`, then `ζ` has unit norm. -/
theorem norm_eq_one_of_selfOverlap_scale
    {D D' : ℕ} {A : MPSTensor d D} {B : MPSTensor d D'} {ζ : ℂ}
    (hAA : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) Filter.atTop (nhds 1))
    (hBB : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) Filter.atTop (nhds 1))
    (hSelf : ∀ N : ℕ,
      mpvOverlap (d := d) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N) :
    ‖ζ‖ = 1 := by
  have hAA_ne : ∀ᶠ N in Filter.atTop, ‖mpvOverlap (d := d) A A N‖ ≠ 0 :=
    hAA.eventually_ne one_ne_zero
  have hRatio : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖ /
      ‖mpvOverlap (d := d) A A N‖) Filter.atTop (nhds 1) := by
    rw [show (1 : ℝ) = 1 / 1 from (one_div_one).symm]
    exact hBB.div hAA one_ne_zero
  have hRatioEq : ∀ᶠ N in Filter.atTop,
      ‖mpvOverlap (d := d) B B N‖ / ‖mpvOverlap (d := d) A A N‖ = (‖ζ‖ ^ 2) ^ N := by
    filter_upwards [hAA_ne] with N hN
    rw [hSelf N, norm_mul, norm_pow, show ‖ζ * starRingEnd ℂ ζ‖ = ‖ζ‖ ^ 2 from by
      rw [norm_mul, RCLike.norm_conj, sq]]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact mul_div_cancel_of_imp (fun h => absurd h hN)
  have hPow : Filter.Tendsto (fun N => (‖ζ‖ ^ 2) ^ N) Filter.atTop (nhds 1) :=
    hRatio.congr' hRatioEq
  have h1 : ‖ζ‖ ^ 2 = 1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact (hPow.ne_nhds one_ne_zero)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h)
    · have hlt2 : ∀ᶠ n in Filter.atTop, (‖ζ‖ ^ 2) ^ n < 2 :=
        hPow.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
      rcases ((Filter.tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt h) 2).and hlt2).exists
        with ⟨n, hn1, hn2⟩
      exact not_lt_of_ge hn1 hn2
  nlinarith [norm_nonneg ζ]

/-- The gauge phase `ζ` in a gauge-phase equivalence between two TP-normalized irreducible
primitive blocks has unit norm. -/
theorem norm_gaugePhase_eq_one_of_irr_TP_primitive
    {D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A)
    (hB_irr : IsIrreducibleTensor B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hA_prim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hB_prim : _root_.IsPrimitive (transferMap (d := d) (D := D) B))
    (X : GL (Fin D) ℂ) (ζ : ℂ)
    (hX : ∀ i : Fin d,
      B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ‖ζ‖ = 1 := by
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ :=
    mpv_eq_pow_mul_of_gaugePhase A B X ζ hX
  have hScale : ∀ N,
      mpvOverlap (d := d) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N :=
    mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A) (B := B) (ζ := ζ) hmpv
  have hA_pf : HasPrimitiveFixedPoint A :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hA_irr hA_norm hA_prim
  have hB_pf : HasPrimitiveFixedPoint B :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible B hB_irr hB_norm hB_prim
  have hAA : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) Filter.atTop (nhds 1) := by
    convert hA_pf.overlap_tendsto_one.norm using 1
    simp
  have hBB : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) Filter.atTop (nhds 1) := by
    convert hB_pf.overlap_tendsto_one.norm using 1
    simp
  exact norm_eq_one_of_selfOverlap_scale hAA hBB hScale


/-! ### Symmetry, transitivity, and cast-composition of `GaugePhaseEquiv`

The following four lemmas record purely algebraic facts about the
`GaugePhaseEquiv` predicate (defined in `MPS.Defs`).  They were originally
local helpers in `MPS/FundamentalTheorem/PaperBNT/StrongMatch.lean` for the
paper-faithful bijective-matching argument, but are module-agnostic and so
live here, next to the existing gauge-phase shared infrastructure. -/

/-- Symmetry of `GaugePhaseEquiv` at a fixed bond dimension.

`GaugePhaseEquiv A B` says there exist a gauge `X ∈ GL` and a nonzero
scalar `ζ` such that `B i = ζ • (X * A i * X⁻¹)` for every physical
index `i`.  Conjugating by `X⁻¹` and scaling by `ζ⁻¹` gives the
reversed identity `A i = ζ⁻¹ • (X⁻¹ * B i * X)`, i.e.
`GaugePhaseEquiv B A`. -/
theorem gaugePhaseEquiv_symm_same_dim {d D : ℕ} {A B : MPSTensor d D}
    (h : GaugePhaseEquiv A B) : GaugePhaseEquiv B A := by
  classical
  obtain ⟨X, ζ, hζ, hrel⟩ := h
  refine ⟨X⁻¹, ζ⁻¹, inv_ne_zero hζ, ?_⟩
  intro i
  -- From `B i = ζ • (X * A i * X⁻¹)` derive `A i = ζ⁻¹ • (X⁻¹ * B i * X)`.
  have hBi := hrel i
  -- Abbreviations for the matrix coercions.
  set XM : Matrix (Fin D) (Fin D) ℂ := (X : Matrix (Fin D) (Fin D) ℂ)
  set XinvM : Matrix (Fin D) (Fin D) ℂ :=
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hXX : XinvM * XM = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have hU : (X⁻¹ * X : GL (Fin D) ℂ) = 1 := by simp
    have hUval :
        ((X⁻¹ * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
          = ((1 : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
      congrArg Units.val hU
    simp only [Units.val_mul, Units.val_one] at hUval
    exact hUval
  have hXX' : XM * XinvM = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have hU : (X * X⁻¹ : GL (Fin D) ℂ) = 1 := by simp
    have hUval :
        ((X * X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
          = ((1 : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
      congrArg Units.val hU
    simp only [Units.val_mul, Units.val_one] at hUval
    exact hUval
  -- Inverse-of-inverse: `(X⁻¹)⁻¹ = X` for units.
  have hInvInv : ((X⁻¹)⁻¹ : GL (Fin D) ℂ) = X := inv_inv X
  -- The desired identity: `A i = ζ⁻¹ • (X⁻¹ * B i * X)`.
  -- Multiply `hBi : B i = ζ • (X * A i * X⁻¹)` on the left by `X⁻¹` and on
  -- the right by `X`:
  --   X⁻¹ * B i * X = ζ • (X⁻¹ * X * A i * X⁻¹ * X) = ζ • (1 * A i * 1) = ζ • A i.
  have hSandwich :
      XinvM * B i * XM = ζ • A i := by
    calc
      XinvM * B i * XM
          = XinvM * (ζ • (XM * A i * XinvM)) * XM := by rw [hBi]
      _ = ζ • (XinvM * (XM * A i * XinvM) * XM) := by
            simp
      _ = ζ • ((XinvM * XM) * A i * (XinvM * XM)) := by
            simp [Matrix.mul_assoc]
      _ = ζ • A i := by rw [hXX]; simp
  -- Now divide by `ζ`.
  have hAi : A i = ζ⁻¹ • (XinvM * B i * XM) := by
    have := congrArg (fun M => (ζ⁻¹ : ℂ) • M) hSandwich
    simp only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at this
    exact this.symm
  -- Repackage with the inverse of `X⁻¹` being `X`.
  -- The goal expects `((X⁻¹)⁻¹ : GL).val = X.val`.
  change A i = ζ⁻¹ • (XinvM * B i *
    (((X⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
  simpa [hInvInv, XM, XinvM] using hAi

/-- Symmetry of `GaugePhaseEquiv` across a bond-dim cast: if the cast
maps the *right-hand* tensor into the *left-hand* space, then we may
flip both the cast direction and the equivalence direction.

The two forms are mathematically the same statement (after eliminating
the cast by `subst`), but the cast routing differs at the term level,
so we record this as an explicit auxiliary lemma. -/
theorem gaugePhaseEquiv_swap_cast {d D₁ D₂ : ℕ}
    (h : D₁ = D₂) {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hGP : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h.symm) B) A) :
    GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) A) B := by
  subst h
  -- After `subst`, both casts reduce to identity.
  simpa using gaugePhaseEquiv_symm_same_dim (by simpa using hGP)

/-- Transitivity of `GaugePhaseEquiv` at a fixed bond dimension.

If `B i = ζ₁ • (X₁ * A i * X₁⁻¹)` and `C i = ζ₂ • (X₂ * B i * X₂⁻¹)`,
then `C i = (ζ₂ ζ₁) • ((X₂ X₁) * A i * (X₂ X₁)⁻¹)`, giving
`GaugePhaseEquiv A C` with gauge `X₂ * X₁` and phase scalar `ζ₂ * ζ₁`. -/
theorem gaugePhaseEquiv_trans_same_dim {d D : ℕ} {A B C : MPSTensor d D}
    (h₁ : GaugePhaseEquiv A B) (h₂ : GaugePhaseEquiv B C) : GaugePhaseEquiv A C := by
  classical
  obtain ⟨X₁, ζ₁, hζ₁, hr₁⟩ := h₁
  obtain ⟨X₂, ζ₂, hζ₂, hr₂⟩ := h₂
  refine ⟨X₂ * X₁, ζ₂ * ζ₁, mul_ne_zero hζ₂ hζ₁, ?_⟩
  intro i
  -- Abbreviations for the matrix coercions of the four GL units in play.
  set X₁M : Matrix (Fin D) (Fin D) ℂ :=
    ((X₁ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set X₂M : Matrix (Fin D) (Fin D) ℂ :=
    ((X₂ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set X₁invM : Matrix (Fin D) (Fin D) ℂ :=
    ((X₁⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set X₂invM : Matrix (Fin D) (Fin D) ℂ :=
    ((X₂⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  -- Coercion of the product `X₂ * X₁` to a matrix is the matrix product.
  have hMul_val :
      (((X₂ * X₁ : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) = X₂M * X₁M := by
    simp [X₁M, X₂M]
  -- Coercion of the inverse of the product is the reversed product of inverses.
  have hMulInv_val :
      (((X₂ * X₁)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = X₁invM * X₂invM := by
    have hRev : ((X₂ * X₁)⁻¹ : GL (Fin D) ℂ) = X₁⁻¹ * X₂⁻¹ := mul_inv_rev X₂ X₁
    have := congrArg (fun U : GL (Fin D) ℂ =>
        (U : Matrix (Fin D) (Fin D) ℂ)) hRev
    simp [X₁invM, X₂invM]
  -- Compute `C i` by chaining the two equivalences.
  calc C i
      = ζ₂ • (X₂M * B i * X₂invM) := hr₂ i
    _ = ζ₂ • (X₂M * (ζ₁ • (X₁M * A i * X₁invM)) * X₂invM) := by rw [hr₁ i]
    _ = ζ₂ • (ζ₁ • (X₂M * (X₁M * A i * X₁invM) * X₂invM)) := by
          simp [smul_smul]
    _ = (ζ₂ * ζ₁) • (X₂M * X₁M * A i * X₁invM * X₂invM) := by
          simp [smul_smul, Matrix.mul_assoc]
    _ = (ζ₂ * ζ₁) • ((X₂M * X₁M) * A i * (X₁invM * X₂invM)) := by
          simp [Matrix.mul_assoc]
    _ = (ζ₂ * ζ₁) •
          ((((X₂ * X₁ : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) * A i *
            (((X₂ * X₁)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
          rw [hMul_val, hMulInv_val]

/-- Composition through a common centre `A`: if the cast `D = D₁` carries
`A : MPSTensor d D` into a gauge-phase equivalence with `B : MPSTensor d D₁`,
and similarly the cast `D = D₂` carries `A` into a gauge-phase equivalence
with `C : MPSTensor d D₂`, then `B` and `C` are gauge-phase equivalent
(after the dimension cast `D₁ = D₂`).

This cast-aware transitivity is used to compose two gauge-phase
equivalences through a shared centre tensor, eliminating the centre via
`gaugePhaseEquiv_symm_same_dim` and `gaugePhaseEquiv_trans_same_dim`. -/
theorem gaugePhaseEquiv_cast_compose_via_centre
    {d D D₁ D₂ : ℕ}
    (h₁ : D = D₁) (h₂ : D = D₂)
    {A : MPSTensor d D} {B : MPSTensor d D₁} {C : MPSTensor d D₂}
    (GE₁ : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h₁) A) B)
    (GE₂ : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h₂) A) C) :
    GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) (h₁.symm.trans h₂)) B) C := by
  subst h₁
  -- After `subst h₁`, `D₁` is replaced everywhere by `D`, the cast on
  -- `GE₁` reduces to identity, and `h₂.symm.trans h₂ = h₂`.
  subst h₂
  -- After `subst h₂`, all three tensors live in `MPSTensor d D`.
  simp only [cast_eq] at GE₁ GE₂ ⊢
  exact gaugePhaseEquiv_trans_same_dim (gaugePhaseEquiv_symm_same_dim GE₁) GE₂

end MPSTensor
