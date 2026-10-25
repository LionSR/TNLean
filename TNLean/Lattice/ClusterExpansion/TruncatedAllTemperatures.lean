/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.TruncatedPositivity
import TNLean.Lattice.ClusterExpansion.TruncatedProductForm

/-!
# The truncated operator at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1317), sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` even, and states that this power is
positive and in the matrix product form of eq. `mpf`, the `n` indices at each site being grouped
into one. This file proves both for the actual truncated operator of the cluster expansion: it is
in product form of range `l` (`hasProductForm_truncatedExp`) and Hermitian when the terms are
(`isHermitian_truncatedExp`), so `HasProductForm.pow_of_even` applies.

**Local fix (positivity at every temperature):** the source states positive definiteness; the
result is positive semidefiniteness. Documented in `docs/paper-gaps/hastings05_mplt_positivity.tex`.

**Scope restriction (geometry):** the product form is on a nonempty finite planar domain with walk
distance, and the source's count of index values (lines 1318–1320) is not established. Documented
in `docs/paper-gaps/hastings05_planar_domain_scope.tex`.

## Main results

* `TNLean.Lattice.ClusterExpansion.hasProductForm_truncatedExp_pow_of_even`: for even `m`,
  `ρ(β, l)^m` is in product form of range `l` and positive semidefinite.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1317.
-/

open scoped MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

open QuantumCircuit

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Eq. `mplt` for the truncated operator** (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1303–1317). Let the domain be nonempty, let each term `h k` be Hermitian and act on the sites
`acts k`, and let `m` be even. Then `ρ(β, l)^m` is in matrix product form of range `l` and
positive semidefinite. With `β/n` in place of `β` and `m = n`, this is the matrix product form and
the positivity of `ρ(β, l_proj) = ρ(β/n, l_proj)^n`; the source states positive definiteness, see
the module docstring. -/
theorem hasProductForm_truncatedExp_pow_of_even [Nonempty (Site Λ)] (acts : κ → Finset (Site Λ))
    (h : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set (Site Λ)))
    (hherm : ∀ k, (h k).IsHermitian) (l : ℕ) (β : ℝ) {m : ℕ} (hm : Even m) :
    HasProductForm Λ q l ((truncatedExp (overlapGraph acts) (IsLargeWalk l acts) h β) ^ m) ∧
      ((truncatedExp (overlapGraph acts) (IsLargeWalk l acts) h β) ^ m).PosSemidef :=
  (hasProductForm_truncatedExp acts h hh l β).pow_of_even
    (isHermitian_truncatedExp _ _ hherm β) hm

end TNLean.Lattice.ClusterExpansion
