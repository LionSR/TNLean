/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Transfer
import TNLean.MPS.BNT.Construction
import TNLean.Spectral.SpectralGap
import TNLean.MPS.RFP.Defs

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

TODO: formalize the convergence in operator norm.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Appendix B** (arXiv:1606.00608): For a tensor in canonical form, the
iterated blocking `E^{2^n}` converges to an idempotent transfer map.

The convergence is entry-wise on the `D² × D²` transfer matrix space:
`∀ ρ, (E^{2^n}) ρ → E_∞ ρ` where `E_∞ ∘ E_∞ = E_∞`.

TODO: prove. -/
theorem rg_flow_converges_of_cf {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalForm μ A) (k : Fin r) :
    ∃ (E_infty : Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ]
                 Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      E_infty ∘ₗ E_infty = E_infty ∧
      ∀ ρ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        Filter.Tendsto
          (fun n : ℕ => ((transferMap (A k) ^ (2 ^ n : ℕ) : _) ρ))
          Filter.atTop
          (nhds (E_infty ρ)) := by
  sorry

end MPSTensor
