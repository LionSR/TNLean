/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapParameters
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# The fixed bootstrap scanner exponents

The scanner scales use exactly the manuscript's fixed bootstrap parameters.
The auxiliary entropy-exponent field is set to mu, so this construction does
not identify that field with the changing entropy exponent in the bootstrap.
Only the rounded collar, window, separation, band count and parameter interval
are used. No final-stage scanner tuple or marginal-moment margin is used.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 693--703, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.BootstrapParameters

/-- The original fixed bootstrap scales as scanner exponents. The field `e`
is mu and serves only to satisfy the numerical exponent structure; it is not
the current entropy exponent. Source: `08-scanner.tex`, lines 693--703. -/
def scannerExponents (e₀ : ℝ) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) : ScannerExponents :=
  { ell := ell e₀
    kappa := kappa e₀
    mu := mu e₀
    nu := nu e₀
    e := mu e₀
    ell_pos := by
      obtain ⟨_, _, hℓ, _, _⟩ := parameter_bounds he₀ he₀₁
      exact hℓ
    ell_lt_one := by
      obtain ⟨_, _, _, hℓ₁, _⟩ := parameter_bounds he₀ he₀₁
      exact hℓ₁
    kappa_pos := by
      obtain ⟨_, _, _, _, hκ⟩ := parameter_bounds he₀ he₀₁
      exact hκ
    kappa_lt_mu := kappa_lt_mu he₀ he₀₁
    mu_lt_one_sub_ell := sub_lt_sub_left (ell_lt_g0 he₀ he₀₁) 1
    nu_pos := by
      obtain ⟨hg₀, _, _, _, _⟩ := parameter_bounds he₀ he₀₁
      exact div_pos hg₀ (by norm_num)
    e_pos := by
      obtain ⟨_, hg₀half, _, _, _⟩ := parameter_bounds he₀ he₀₁
      change 0 < 1 - g0 e₀
      linarith
    e_lt_one := by
      obtain ⟨hg₀, _, _, _, _⟩ := parameter_bounds he₀ he₀₁
      exact sub_lt_self 1 hg₀
    kappa_le_e := (kappa_lt_mu he₀ he₀₁).le }

end TNLean.PEPS.AreaLaw.Scan.BootstrapParameters
