/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs
import TNLean.PEPS.AreaLaw.SafeRectangleDilation
import TNLean.PEPS.AreaLaw.Geometry.TemplateSafeRectangles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rounded scales for safe rectangle shells

For fixed positive row-scale multiplier and collar exponent in `(0, 1)`,
the rounded collar and logarithmic truncation radius are sublinear in the
parent rectangle size. One threshold works for every positive safety
parameter and every physical instance. Selected dyadic shell cells inherit
native rectangle safety. The dyadic cap exponent is not the scanner band count.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, proof of Proposition 9.5, `08-scanner.tex`, lines 707–729,
and `scanner:scales` / `scanner:test-geometry`, lines 32–49, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original proof from the manuscript; no upstream Lean proof text reused.
-/

open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

private theorem roundedClearance_ratio_tendsto_zero {ell : ℝ} (hell : 0 < ell)
    (Cr : ℝ) :
    Tendsto (fun n : ℕ ↦ (4 * (n : ℝ) ^ (1 - ell) +
      20 * (Cr * Real.log n ^ 2 + 1)) / n) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 - ell) / n) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hell).comp hnat
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    simpa only [Function.comp_apply, Real.rpow_one,
      show 1 - ell - 1 = -ell by ring] using Real.rpow_sub hn0 (1 - ell) 1
  have hl : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / n) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero, Function.comp_apply] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hnat
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have h := ((hp.const_mul 4).add (hl.const_mul (20 * Cr))).add (hi.const_mul 20)
  simp only [mul_zero, add_zero] at h
  convert h using 1 <;> ext n <;> ring

/-- Rounded collar and truncation scales satisfy the safe-box and scanner
clearance budgets eventually. The threshold precedes the safety parameter.
Source: Proposition 9.5, `08-scanner.tex`, lines 707–729. -/
theorem exists_rounded_clearance_threshold {C₂ Cr ell : ℝ}
    (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) (hell : 0 < ell) (hell1 : ell < 1) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ s : ℕ, S ≤ s →
      let n := ⌈C₂ * s⌉₊
      let L := ⌊(n : ℝ) ^ (1 - ell)⌋₊
      let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
      1 ≤ L ∧ L ≤ s ∧ ∀ D₀ : ℕ, 1 ≤ D₀ →
        (D₀ + 1) * L ≤ D₀ * s ∧ 2 * L + 10 * r₀ ≤ D₀ * s := by
  have hη : 0 < 1 / (C₂ + 1) := by positivity
  obtain ⟨N, hN⟩ := ((roundedClearance_ratio_tendsto_zero hell Cr).eventually_lt_const
    hη).exists_forall_of_atTop
  have hlarge : ∀ᶠ s : ℕ in atTop, (max N 1 : ℝ) ≤ C₂ * s :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun s : ℕ ↦ (s : ℝ)) atTop atTop).
      const_mul_atTop hC₂).eventually_ge_atTop _
  obtain ⟨S, hS⟩ := hlarge.exists_forall_of_atTop
  refine ⟨max S 1, le_max_right _ _, ?_⟩
  intro s hs
  dsimp only
  let n : ℕ := ⌈C₂ * s⌉₊
  let L : ℕ := ⌊(n : ℝ) ^ (1 - ell)⌋₊
  let r₀ : ℕ := ⌈Cr * Real.log n ^ 2⌉₊
  have hs1 : 1 ≤ s := (le_max_right S 1).trans hs
  have hnlo : (max N 1 : ℝ) ≤ n :=
    (hS s ((le_max_left S 1).trans hs)).trans (Nat.le_ceil _)
  have hnmax : max N 1 ≤ n := by exact_mod_cast hnlo
  have hnN : N ≤ n := (le_max_left N 1).trans hnmax
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hnmax
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnupper : (n : ℝ) ≤ (C₂ + 1) * s := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ C₂ * s by positivity)).le
    have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    dsimp [n]
    nlinarith
  have hsmall := (div_lt_iff₀ hn0).mp (hN n hnN)
  have htotal : 4 * (n : ℝ) ^ (1 - ell) + 20 * (Cr * Real.log n ^ 2 + 1) < s := by
    have h := (div_le_iff₀' (show 0 < C₂ + 1 by positivity)).mpr hnupper
    calc
      _ < (1 / (C₂ + 1)) * n := hsmall
      _ = (n : ℝ) / (C₂ + 1) := by ring
      _ ≤ s := h
  have hLupper : (L : ℝ) ≤ (n : ℝ) ^ (1 - ell) := Nat.floor_le (by positivity)
  have hrupper : (r₀ : ℝ) ≤ Cr * Real.log n ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hbudget : 4 * L + 20 * r₀ < s := by
    have h : (4 : ℝ) * L + 20 * r₀ < s := by linarith
    exact_mod_cast h
  have hLone : 1 ≤ L := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - ell) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by linarith)
    exact Nat.le_floor (by exact_mod_cast h1)
  refine ⟨hLone, by omega, ?_⟩
  intro D₀ hD₀
  have htwo : 2 * L ≤ s := by omega
  have hmul := Nat.mul_le_mul_left D₀ htwo
  have hside : L ≤ D₀ * L := Nat.le_mul_of_pos_left L hD₀
  have hsafety : s ≤ D₀ * s := Nat.le_mul_of_pos_left s hD₀
  constructor <;> nlinarith

/-- The rounded clearance theorem uses the scanner's actual collar scale;
it imposes no condition on the scanner band count. Source: Proposition 9.5,
`08-scanner.tex`, lines 707–729. -/
theorem ScannerExponents.exists_rounded_clearance_threshold (X : ScannerExponents)
    {C₂ Cr : ℝ} (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ s : ℕ, S ≤ s →
      let n := ⌈C₂ * s⌉₊
      let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
      1 ≤ X.L n ∧ X.L n ≤ s ∧ ∀ D₀ : ℕ, 1 ≤ D₀ →
        (D₀ + 1) * X.L n ≤ D₀ * s ∧ 2 * X.L n + 10 * r₀ ≤ D₀ * s :=
  exists_rounded_clearance_threshold hC₂ hCr X.ell_pos X.ell_lt_one

end TNLean.PEPS.AreaLaw.Scan

namespace TNLean.PEPS.AreaLaw

open Geometry

/-- Actual selected shell cells of a safe rectangle remain safe under the
rounded-clearance budget. The cap exponent `Kcap` is independent of the scanner
band count. Source: Proposition 9.5, `08-scanner.tex`, lines 723–729. -/
theorem IsSafe.cappedDyadicPartition_shell {Λ : Finset (ℤ × ℤ)}
    {A : Finset (Site Λ)} {D₀ j L Kcap k : ℕ} {Q : IntRect}
    (hsafe : TNLean.PEPS.AreaLaw.IsSafe Λ A D₀ Q) (hj : j ≤ L)
    (hcap : 2 ^ Kcap ≤ L) (hbudget : (D₀ + 1) * L ≤ D₀ * Q.size)
    {z : ℤ × ℤ}
    (hcell : (k, z) ∈ cappedDyadicPartition ((Q.dilate j).toFinset \ Q.toFinset) Kcap) :
    TNLean.PEPS.AreaLaw.IsSafe Λ A D₀ (latticeDyadicRect k z) := by
  obtain ⟨hk, hsub, _⟩ := (mem_cappedDyadicPartition _ _ _ _).mp hcell
  have hsize : (latticeDyadicRect k z).size ≤ L := by
    rw [size_latticeDyadicRect]
    exact (Nat.pow_le_pow_right (by decide) hk).trans hcap
  apply hsafe.of_subset_dilate
  · simpa only [toFinset_latticeDyadicRect] using hsub.trans Finset.sdiff_subset
  · calc
      D₀ * (latticeDyadicRect k z).size + j ≤ D₀ * L + L :=
        Nat.add_le_add (Nat.mul_le_mul_left D₀ hsize) hj
      _ = (D₀ + 1) * L := by ring
      _ ≤ D₀ * Q.size := hbudget

end TNLean.PEPS.AreaLaw

namespace TNLean.PEPS.AreaLaw.Scan

open Geometry

/-- One rounded-scale threshold gives scanner clearance and safe actual shell
cells uniformly in the domain, cut, safety parameter and parent rectangle.
Source: Proposition 9.5, `08-scanner.tex`, lines 707–729. -/
theorem exists_safe_shell_cells_of_rounded_scales (X : ScannerExponents)
    {C₂ Cr : ℝ} (hC₂ : 0 < C₂) (hCr : 0 ≤ Cr) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ))
      (D₀ : ℕ), 1 ≤ D₀ → ∀ Q : IntRect, S ≤ Q.size → IsSafe Λ A D₀ Q →
      let n := ⌈C₂ * Q.size⌉₊
      let L := X.L n
      let r₀ := ⌈Cr * Real.log n ^ 2⌉₊
      1 ≤ L ∧ L ≤ Q.size ∧
      (∀ e ∈ edgeBoundary Λ A, ∀ z ∈ e, ∀ p ∈ Q.toFinset,
        2 * L + 10 * r₀ < supDist p z.1) ∧
      ∀ j Kcap : ℕ, j ≤ L → 2 ^ Kcap ≤ L → ∀ k z,
        (k, z) ∈ cappedDyadicPartition ((Q.dilate j).toFinset \ Q.toFinset) Kcap →
        IsSafe Λ A D₀ (latticeDyadicRect k z) := by
  obtain ⟨S, hS, h⟩ := X.exists_rounded_clearance_threshold hC₂ hCr
  refine ⟨S, hS, ?_⟩
  intro Λ A D₀ hD₀ Q hQ hsafe
  obtain ⟨hLone, hLsize, hbudgets⟩ := h Q.size hQ
  obtain ⟨hbudget, hclear⟩ := hbudgets D₀ hD₀
  refine ⟨hLone, hLsize, ?_, ?_⟩
  · intro e he z hz p hp
    exact hclear.trans_lt (hsafe e he z hz p hp)
  · intro j Kcap hj hcap k z hcell
    exact hsafe.cappedDyadicPartition_shell hj hcap hbudget hcell

end TNLean.PEPS.AreaLaw.Scan
