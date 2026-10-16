/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedSampling
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth
import TNLean.PEPS.AreaLaw.Geometry.Exponents

/-!
# The literal physical scanner of an ambient template

Use the accepted actual-history scanner with the actual induced domain
and ambient target depth. Each original interaction is anchored at a
chosen member of its nonempty support. All scales are the paper's literal
final floors, ceilings and natural-number band division.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--58, 83--154 and 839--845, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently written from the manuscript; no upstream Lean proof reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The actual finite-history scanner at the final rounded scales, with
no geometric or entropy certificate stored as a field. Source:
`08-scanner.tex`, lines 32--58, 83--154 and 839--845. -/
def finalTemplateScanner {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset (Site Λ)) (R n : ℕ) (Cr C₁ : ℝ) :
    CollarScan (Site Λ) (AdmissibleSupport Λ R) where
  graph := domainGraph Λ
  A := A
  depth := fun x ↦ ambientDepth T hT x.val
  anchor := fun i ↦ i.property.1.choose
  n := n
  m := ⌊(n : ℝ) ^ (Exponents.scannerMu : ℝ)⌋₊
  K := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ /
    (8 * ⌊(n : ℝ) ^ (Exponents.scannerMu : ℝ)⌋₊)
  D := ⌈(n : ℝ) ^ (Exponents.scannerKappa : ℝ)⌉₊
  r₀ := ⌈Cr * Real.log (n : ℝ) ^ 2⌉₊
  C₁ := C₁

/-- The scanner's actual truncation set is exactly the original template
collar inside the chosen cut. This identity is independent of all scale,
clearance and entropy estimates. Source: `08-scanner.tex`, lines 21--29
and 50--53. -/
theorem finalTemplateScanner_truncationSet {Λ T : Finset (ℤ × ℤ)}
    (hT : T.Nonempty) (A : Finset (Site Λ)) (R n : ℕ) (Cr C₁ : ℝ) (L : ℕ) :
    (finalTemplateScanner hT A R n Cr C₁).truncationSet L =
      A.filter fun x ↦ x.val ∈ ambientDilation T L := by
  classical
  ext x
  simp only [finalTemplateScanner, CollarScan.truncationSet, Finset.mem_filter,
    ambientDepth_le_iff_mem_dilation]

end TNLean.PEPS.AreaLaw.Scan
