/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm

/-!
# The matrix product form at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1320), extends the high-temperature
matrix product form to every temperature. For `β > β₀` he sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` the smallest even integer such that
`β/n ≤ β₀`. Taking `n` even makes `ρ(β, l_proj)` positive, and the `n` indices at each site, one
from each factor, group into a single index, so the power is again in the form of eq. `mpf`.

This file proves the structural part of that step for any Hermitian operator in product form.

* An even power of a Hermitian matrix is positive semidefinite: `A^{2k} = (A^k)ᴴ A^k`. The source
  calls `ρ(β, l_proj)` positive definite; an even power is positive definite only when the base is
  invertible, and positive semidefinite in general, which is what is proved here.
* A power of an operator in product form of range `l` is in product form of range `l`
  (`TNLean.Lattice.HasProductForm.pow`, which groups the indices of the factors).
* For `β ≥ 0` and `β₀ > 0` an even `n ≥ 2` with `β/n ≤ β₀` exists.

The truncated high-temperature form `ρ(β/n, l_proj)` is Hermitian because it is a real-weighted
sum of exponentials of Hermitian operators, but its definition belongs to the cluster
expansion and is not used here: the results take any Hermitian operator in product form. The
error bound at every temperature (lines 1322–1349) and the count of index values (lines
1313–1320) are not proved here; the index count is the one recorded as not established in
`TNLean/Lattice/ProductForm.lean`.

## Main results

* `TNLean.Lattice.ClusterExpansion.posSemidef_pow_of_even`: `A^m ≥ 0` for Hermitian `A` and even
  `m`.
* `TNLean.Lattice.ClusterExpansion.HasProductForm.pow_of_even`: for Hermitian `ρ` in product
  form of range `l` and even `m`, `ρ^m` is positive semidefinite and in product form of range `l`.
* `TNLean.Lattice.ClusterExpansion.exists_even_div_le`: an even number of factors suffices.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1320.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An even power `A^{2k} = (A^k)ᴴ A^k` of a Hermitian matrix is positive semidefinite. -/
theorem posSemidef_pow_two_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ (2 * k)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (A ^ k)
  rwa [(hA.pow k).eq, ← pow_add, ← two_mul] at h

/-- **Positivity at every temperature.** An even power of a Hermitian matrix is positive
semidefinite. This is why Hastings takes the number of factors in eq. `mplt` even.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1309–1311. -/
theorem posSemidef_pow_of_even {A : Matrix n n ℂ} (hA : A.IsHermitian) {m : ℕ} (hm : Even m) :
    (A ^ m).PosSemidef := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul]
  exact posSemidef_pow_two_mul hA k

/-- **Eq. `mplt` keeps the matrix product form.** Let `ρ` be a Hermitian operator in product form
of range `l`, as the truncated high-temperature density matrix `ρ(β/n, l_proj)` is. For even `m`
the power `ρ^m` is positive semidefinite and again in product form of range `l`, the `m`
indices at each site being grouped into one. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1303–1313. -/
theorem HasProductForm.pow_of_even {Λ : Finset (ℤ × ℤ)} {q l : ℕ}
    {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ} (hρ : HasProductForm Λ q l ρ)
    (hH : ρ.IsHermitian) {m : ℕ} (hm : Even m) :
    HasProductForm Λ q l (ρ ^ m) ∧ (ρ ^ m).PosSemidef :=
  ⟨hρ.pow m, posSemidef_pow_of_even hH hm⟩

/-- **The number of factors in eq. `mplt`.** For `β ≥ 0` and `β₀ > 0` there is an even `n ≥ 2`
with `β/n ≤ β₀`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1305–1308. -/
theorem exists_even_div_le {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : 0 < β₀) :
    ∃ m : ℕ, Even m ∧ 2 ≤ m ∧ β / m ≤ β₀ := by
  refine ⟨2 * (⌈β / β₀⌉₊ + 1), even_two_mul _, by omega, ?_⟩
  have hceil : β / β₀ ≤ ⌈β / β₀⌉₊ := Nat.le_ceil _
  have hm : (0 : ℝ) < ((2 * (⌈β / β₀⌉₊ + 1) : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hm]
  rw [div_le_iff₀ hβ₀] at hceil
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) ⌈β / β₀⌉₊]

end TNLean.Lattice.ClusterExpansion
