/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm
import QICLean.Analysis.ClusterExpansion.Temperature

/-!
# The matrix product form at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1320), extends the high-temperature
matrix product form to every temperature. For `β > β₀` he sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` the smallest even integer such that
`β/n ≤ β₀`. Taking `n` even makes `ρ(β, l_proj)` positive, and the `n` indices at each site, one
from each factor, group into a single index, so the power is again in the form of eq. `mpf`.

This file keeps the product-form part of that step for any Hermitian operator in product form.

* An even power of a Hermitian matrix is positive semidefinite: `A^{2k} = (A^k)ᴴ A^k`.
* A power of an operator in product form of range `l` is in product form of range `l`
  (`TNLean.Lattice.HasProductForm.pow`, which groups the indices of the factors).
* For `β ≥ 0` and `β₀ > 0` an even `n ≥ 2` with `β/n ≤ β₀` exists.

The actual truncated high-temperature operator is Hermitian, and its even powers have
the required positivity and product form in `TruncatedAllTemperatures.lean`. The error
estimates at every temperature are proved in `TemperatureError.lean`, and the actual local
index counts are proved in `LocalIndexCount.lean`. The least positive even factor count
at positive temperature lies in the interval `[β/β₀, β/β₀ + 2)`.

**Local fix (positivity at every temperature):** the source states that `ρ(β, l_proj)` is
positive definite. An even power of a Hermitian operator is positive semidefinite, and positive
definite only when the base `ρ(β/n, l_proj)` is invertible, which the source does not establish.
The results here state positive semidefiniteness, which is what the even power is used for.
Documented in `docs/paper-gaps/hastings05_mplt_positivity.tex`.

The product-form statements apply to every finite site set and every locality relation;
in particular, they apply to the source's arbitrary finite metric lattice. No planar
embedding is assumed.

## Main results

* `TNLean.Lattice.HasProductForm.pow_of_even`: for Hermitian `ρ` in product
  form of range `l` and even `m`, `ρ^m` is positive semidefinite and in product form of range `l`.

The positivity of even powers (`ClusterExpansion.posSemidef_pow_of_even`) and the even number
of factors (`ClusterExpansion.exists_even_div_le`) are QICLean's
(`QICLean/Analysis/ClusterExpansion/Temperature`).

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1320.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

open ClusterExpansion
open SimpleGraph (overlapGraph)

namespace TNLean.Lattice.ClusterExpansion

/-- **Eq. `mplt` keeps the matrix product form.** Let `ρ` be a Hermitian operator in product form
of range `l`, as the truncated high-temperature density matrix `ρ(β/n, l_proj)` is. For even `m`
the power `ρ^m` is positive semidefinite and again in product form of range `l`, the `m`
indices at each site being grouped into one. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1303–1317. -/
theorem _root_.TNLean.Lattice.HasProductForm.pow_of_even
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} {near : ι → ι → Prop}
    {ρ : Matrix ((j : ι) → Fin (d j)) ((j : ι) → Fin (d j)) ℂ} (hρ : HasProductForm d near ρ)
    (hH : ρ.IsHermitian) {m : ℕ} (hm : Even m) :
    HasProductForm d near (ρ ^ m) ∧ (ρ ^ m).PosSemidef :=
  ⟨hρ.pow m, _root_.ClusterExpansion.posSemidef_pow_of_even hH hm⟩

end TNLean.Lattice.ClusterExpansion
