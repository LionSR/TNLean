/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixComparison
import TNLean.PEPS.AreaLaw.Scan.Budgets
import TNLean.PEPS.AreaLaw.TwoFamilies
import QICLean.Entropy.FiniteProductContinuity

/-!
# Entropy transfer on positive-depth prefixes

An entropy bound for the original vector on every whole-row positive-depth
prefix transfers to the same supplied truncated vector. The compact-region
cardinality bound and the actual quantitative truncation estimate give one
threshold before the domain, vectors, depth function and prefixes.

The original entropy bound is an explicit hypothesis, as in the scanner
proposition. No Hamiltonian, truncated vector or comparison family is chosen
here. The depth identification and geometric size estimate are supplied by
their separate geometric applications.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `08-scanner.tex`, `scanner:entropy-input`, lines 353--357,
and its continuity argument, lines 399--404; `01-preliminaries.tex`,
Lemma 2.1, lines 33--46; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- A single large-scale threshold transfers the original entropy bound to
every positive-depth prefix in the same truncated vector. The actual global
trace distance retains the normalized gap coefficient, and the dimension
bound concerns only the compact region. The threshold is independent of
the entropy coefficient and exponent as well as the supplied finite system.
Source: `08-scanner.tex`, lines 353--357 and 399--404, at the manuscript
revision stated in the module documentation. -/
theorem eventually_regionalEntropy_positiveDepthPrefix_le
    (q : ℕ) (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (Λ : Finset (ℤ × ℤ)) (Ω Ωt : StateSpace Λ q),
      ‖Ω‖ = 1 → ‖Ωt‖ = 1 →
      ∀ (A : Finset (Site Λ)) (depth : Site Λ → ℤ) (L : ℕ),
      ((depthPrefix A depth (L : ℤ)).card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
      Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
          (Matrix.vecMulVec Ω (star Ω)) ≤
        Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
      ∀ Ce e : ℝ,
      (∀ j : ℕ, j ≤ L →
        regionalEntropy Λ q Ω (positiveDepthPrefix A depth (j : ℤ)) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n)) →
      ∀ j : ℕ, j ≤ L →
        regionalEntropy Λ q Ωt (positiveDepthPrefix A depth (j : ℤ)) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ) := by
  classical
  done

end TNLean.PEPS.AreaLaw.Scan
