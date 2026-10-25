/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CopyRegionEntropy
import TNLean.MPS.AreaLaw.EntropyScaling.QutritEntropy

/-!
# Repeated qutrit states with bounded interval entropy

The state on `N² * (N + N) = 2N³` sites consists of `N²` consecutive copies
of the qutrit state with parameter `p = 1/N`. Every interval has entropy at
most four bits, expressed here as `4 * log 2` with natural logarithms.

Source: Schuch, Wolf, Verstraete, and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 421–430.
-/

namespace TNLean.MPS.AreaLaw.EntropyScaling

/-- The source's state on `2N³` sites, indexed as `N²` consecutive blocks of
`N + N` sites. Source: arXiv:0705.0292v2, lines 421–425. -/
noncomputable def qutritCopies (N : ℕ) :
    EuclideanSpace ℂ (Fin (N ^ 2 * (N + N)) → Fin 3) :=
  copyProduct (fun _ : Fin (N ^ 2) ↦ qutritFamily N)

/-- The number of physical sites in the repeated family.
Source: arXiv:0705.0292v2, line 423. -/
theorem qutritCopies_length (N : ℕ) : N ^ 2 * (N + N) = 2 * N ^ 3 := by
  ring

/-- Normalization of the repeated family.
Source: arXiv:0705.0292v2, lines 421–425. -/
theorem norm_qutritCopies {N : ℕ} (hN : 0 < N) : ‖qutritCopies N‖ = 1 := by
  simp [qutritCopies, norm_copyProduct, norm_qutritFamily hN]

/-- Every contiguous region has entropy at most four bits.
Source: arXiv:0705.0292v2, lines 426–430. -/
theorem regionEntropy_interval_qutritCopies_le {N : ℕ} (hN : 0 < N) (a b : ℕ) :
    Entropy.regionEntropy (interval (N ^ 2 * (N + N)) a b) (qutritCopies N) ≤
      4 * Real.log 2 := by
  simpa only [qutritCopies, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
    regionEntropy_interval_copyProduct_le (norm_qutritFamily hN)
      (regionEntropy_qutritFamily_le hN) (N ^ 2) a b

end TNLean.MPS.AreaLaw.EntropyScaling
