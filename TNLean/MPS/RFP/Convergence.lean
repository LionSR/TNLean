/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Transfer
import TNLean.MPS.BNT.Construction
import TNLean.Spectral.SpectralGap

/-!
# RG flow convergence for canonical-form MPS tensors

This file states the convergence result for the renormalization-group (RG) flow
applied to MPS tensors in canonical form, following arXiv:1606.00608, Appendix B
(Cirac–Pérez-García–Schuch–Verstraete).

For a CF tensor, the transfer matrix decomposes as
`E' = ⊕_{j,j'} μ_{j,q} μ̄_{j',q'} E_{j,j'}`.
Off-diagonal blocks `E_{j,j'}` (j ≠ j') have spectral radius < 1 and decay.
Diagonal blocks `E_{j,j}` have a unique magnitude-1 eigenvalue. So `E'^N`
converges to an idempotent (the RFP).

## Main result

* `rg_flow_converges_of_cf`: the sequence of blocked transfer maps converges
  to an idempotent for any canonical-form tensor.

TODO: add `IsCanonicalForm` hypothesis and formalize the convergence.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Appendix B** (arXiv:1606.00608): For a tensor in canonical form, the
iterated blocking `E^{2^n}` converges to an idempotent transfer map.

TODO: state with `IsCanonicalForm` hypothesis. The convergence is in
operator norm on the `D² × D²` transfer matrix space. -/
theorem rg_flow_converges_of_cf (A : MPSTensor d D)
    /- (hCF : IsCanonicalForm μ A) -/ :
    ∃ (_E_infty : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ),
      True := by -- refine to: E_infty is idempotent and limit of E^(2^n)
  sorry

end MPSTensor
