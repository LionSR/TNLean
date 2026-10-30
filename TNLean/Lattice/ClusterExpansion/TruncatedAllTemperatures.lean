/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.TruncatedPositivity
import TNLean.Lattice.ClusterExpansion.TruncatedProductForm
import TNLean.Lattice.ClusterExpansion.PercolationSource

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

The product form holds on every nonempty finite site set with reflexive locality, and
therefore on every finite metric lattice. The local index ranges of its powers are proved
in `TNLean.Lattice.ClusterExpansion.LocalIndexCount`, with the lattice-volume interpretation
recorded in `docs/paper-gaps/hastings05_planar_domain_scope.tex`.

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

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Eq. `mplt` for the truncated operator** (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1303–1317). Let the finite site set be nonempty, let the locality relation be reflexive,
let each term `h k` be Hermitian and act on the sites `acts k`, and let `m` be even. Then
`ρ(β, l)^m` is in matrix product form with the same locality relation and
positive semidefinite. With `β/n` in place of `β` and `m = n`, this is the matrix product form and
the positivity of `ρ(β, l_proj) = ρ(β/n, l_proj)^n`; the source states positive definiteness, see
the module docstring. -/
theorem hasProductForm_truncatedExp_pow_of_even [Nonempty σ] (acts : κ → Finset σ)
    (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ))
    (hherm : ∀ k, (h k).IsHermitian) (near : σ → σ → Prop) (hnear : ∀ i, near i i)
    (β : ℝ) {m : ℕ} (hm : Even m) :
    HasProductForm q near ((truncatedExp (overlapGraph acts) (IsLargeSupport near acts) h β) ^ m) ∧
      ((truncatedExp (overlapGraph acts) (IsLargeSupport near acts) h β) ^ m).PosSemidef :=
  (hasProductForm_truncatedExp acts h hh near hnear β).pow_of_even
    (isHermitian_truncatedExp _ _ hherm β) hm

/-- The source's diameter truncation on an arbitrary finite pseudometric site set has
matrix product form of range `l`. Hastings, arXiv:cond-mat/0508554v3, lines 1256–1279. -/
theorem hasProductForm_truncatedExp_of_dist_le [PseudoMetricSpace σ] [Nonempty σ]
    (acts : κ → Finset σ) (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ))
    {l : ℝ} (hl : 0 ≤ l) (β : ℝ) :
    HasProductForm q (fun i j ↦ dist i j ≤ l)
      (truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β) := by
  have hlarge : IsLargeSupport (fun i j ↦ dist i j ≤ l) acts = IsLargeDiam acts l := by
    funext C
    simp only [IsLargeSupport, IsLargeDiam, not_le]
  rw [← hlarge]
  exact hasProductForm_truncatedExp acts h hh (fun i j ↦ dist i j ≤ l)
    (fun i ↦ by simpa using hl) β

/-- At every temperature, the even power of the source's diameter-truncated operator on
an arbitrary finite metric lattice is positive semidefinite and retains its matrix product
form. Hastings, arXiv:cond-mat/0508554v3, eq. `mplt`, lines 1303–1317. -/
theorem hasProductForm_truncatedExp_pow_of_even_of_dist_le
    [PseudoMetricSpace σ] [Nonempty σ] (acts : κ → Finset σ)
    (h : κ → Matrix (σ → Fin q) (σ → Fin q) ℂ)
    (hh : ∀ k, h k ∈ supportedOperators q (acts k : Set σ))
    (hherm : ∀ k, (h k).IsHermitian) {l : ℝ} (hl : 0 ≤ l) (β : ℝ)
    {m : ℕ} (hm : Even m) :
    HasProductForm q (fun i j ↦ dist i j ≤ l)
        ((truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β) ^ m) ∧
      ((truncatedExp (overlapGraph acts) (IsLargeDiam acts l) h β) ^ m).PosSemidef :=
  (hasProductForm_truncatedExp_of_dist_le acts h hh hl β).pow_of_even
    (isHermitian_truncatedExp _ _ hherm β) hm

end TNLean.Lattice.ClusterExpansion
