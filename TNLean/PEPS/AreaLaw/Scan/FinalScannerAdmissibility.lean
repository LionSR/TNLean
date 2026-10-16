/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation
import TNLean.PEPS.AreaLaw.Geometry.Exponents

/-!
# Automatic admissibility of the final rounded scanner scales

The original literal rounded radius, window, separation and band count
satisfy all numerical scanner prerequisites at one sufficiently large
physical size. The threshold depends on the fixed radius coefficient,
not on the finite domain, cut, Hamiltonian, template or entropy data.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--58 and 839--867, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript using existing TNLean results;
no upstream Lean proof text is reused.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- Every fixed nonnegative radius coefficient admits one threshold at which
all final rounded scanner scale inequalities hold, including the doubled
radius needed for source truncation. The band count is natural-number
division throughout. Source: `08-scanner.tex`, lines 32--58 and 839--867. -/
theorem exists_finalScanner_admissibility {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
      let m := ⌊(n : ℝ) ^ (Exponents.scannerMu : ℝ)⌋₊
      let D := ⌈(n : ℝ) ^ (Exponents.scannerKappa : ℝ)⌉₊
      let K := L / (8 * m)
      2 * roundedLogRadius Cr n ≤ D ∧ 1 ≤ D ∧ 4 * D ≤ m ∧
        1 ≤ K ∧ 8 * K * m ≤ L := by
  have hkappa : 0 < (Exponents.scannerKappa : ℝ) := by
    norm_num [Exponents.scannerKappa]
  have hkm : (Exponents.scannerKappa : ℝ) < (Exponents.scannerMu : ℝ) := by
    norm_num [Exponents.scannerKappa, Exponents.scannerMu]
  have hmu : 0 < (Exponents.scannerMu : ℝ) := hkappa.trans hkm
  have hmuL : (Exponents.scannerMu : ℝ) < 1 - (Exponents.scannerEll : ℝ) := by
    norm_num [Exponents.scannerMu, Exponents.scannerEll]
  have hscales := eventually_status_scale_separation
    (ell := (Exponents.scannerEll : ℝ)) hCr hkappa hkm
  have hradius := eventually_const_mul_roundedLogRadius_le_rpow hCr hkappa 2
  have hbands := eventually_one_le_source_bandCount hmu hmuL
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hscales.and (hradius.and hbands))
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn
  obtain ⟨hscale, hradius, hband⟩ := hN n ((le_max_left N 2).trans hn)
  dsimp only at hscale hband ⊢
  refine ⟨?_, hscale.2.2.1, hscale.2.2.2.1, hband, hscale.2.2.2.2⟩
  exact_mod_cast hradius.trans
    (Nat.le_ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ)))

end TNLean.PEPS.AreaLaw.Scan
