/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.AllTemperatures
import TNLean.Lattice.ClusterExpansion.Truncation

/-!
# Positivity of the truncated operator at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1314), sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` even, and states that the even power is
positive definite. The positivity of even powers in `AllTemperatures.lean` applies to Hermitian
operators. This file shows that the truncated operator `ρ(β, l)` of the cluster expansion is
Hermitian when the terms `H_k` are, so the even power of the actual truncated operator is positive
semidefinite.

`ρ(β, l)` is the finite inclusion–exclusion sum `∑_U (-1)^{|U|} ρ(β, U)` (`truncatedExp_eq_sum`),
and each `ρ(β, C) = ∑_{D ⊆ C} (-1)^{|D|} e^{-β (H - H_B - H_D)}` is a sum of exponentials of
Hermitian operators with real coefficients.

**Local fix (positivity at every temperature):** the source states that `ρ(β, l_proj)` is
positive definite. The result here is positive semidefiniteness, as in `AllTemperatures.lean`.
Documented in `docs/paper-gaps/hastings05_mplt_positivity.tex`.

## Main results

* `TNLean.Lattice.ClusterExpansion.isHermitian_clusterPart`: `ρ(β, C)` is Hermitian.
* `TNLean.Lattice.ClusterExpansion.isHermitian_truncatedExp`: `ρ(β, l)` is Hermitian.
* `TNLean.Lattice.ClusterExpansion.posSemidef_truncatedExp_pow`: `ρ(β/n, l)^n` is positive
  semidefinite for even `n`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1314.
-/

open Finset Matrix
open scoped MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
/-- A power of `-1` is self-adjoint, so it preserves Hermitian matrices as a scalar. -/
private theorem isHermitian_neg_one_pow_smul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (k : ℕ) :
    ((-1 : ℂ) ^ k • A).IsHermitian :=
  hA.smul ((IsSelfAdjoint.one ℂ).neg.pow k)

/-- **The cluster part is Hermitian.** If `H` and the terms `h_k` with `k ∈ B ∪ C` are Hermitian,
then `ρ(β, C) = ∑_{D ⊆ C} (-1)^{|D|} e^{-β (H - H_B - H_D)}` is Hermitian. The cluster part is
Hastings' `ρ(β, C)`, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1174–1177. -/
theorem isHermitian_clusterPart {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {h : κ → Matrix ι ι ℂ}
    {B C : Finset κ} (hh : ∀ k ∈ B ∪ C, (h k).IsHermitian) (β : ℝ) :
    (clusterPart H h B C β).IsHermitian := by
  refine Matrix.isHermitian_sum _ fun D hD ↦ isHermitian_neg_one_pow_smul ?_ _
  have hsum : ∀ T ⊆ B ∪ C, (∑ k ∈ T, h k).IsHermitian := fun T hT ↦
    Matrix.isHermitian_sum T fun k hk ↦ hh k (hT hk)
  have hD' : D ⊆ B ∪ C := (mem_powerset.1 hD).trans subset_union_right
  exact (((hH.sub (hsum B subset_union_left)).sub (hsum D hD')).smul
    (IsSelfAdjoint.all β)).neg.exp

variable [Fintype κ] (G : SimpleGraph κ) [DecidableRel G.Adj]
  (large : Finset κ → Prop)

/-- **The truncated operator is Hermitian.** If every term `h_k` is Hermitian, then
`ρ(β, l)` is Hermitian: it is the inclusion–exclusion sum `∑_U (-1)^{|U|} ρ(β, U)` of Hermitian
cluster parts. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1101–1104 and
1197–1225. -/
theorem isHermitian_truncatedExp {h : κ → Matrix ι ι ℂ} (hh : ∀ k, (h k).IsHermitian)
    (β : ℝ) : (truncatedExp G large h β).IsHermitian := by
  classical
  have hH : (∑ k, h k).IsHermitian := Matrix.isHermitian_sum _ fun k _ ↦ hh k
  rw [truncatedExp_eq_sum G large (H := ∑ k, h k) rfl β]
  exact Matrix.isHermitian_sum _ fun U _ ↦
    isHermitian_neg_one_pow_smul (isHermitian_clusterPart hH (fun k _ ↦ hh k) β) _

/-- **The even power of the truncated operator is positive** (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1303–1314, eq. `mplt`). If every term `h_k` is
Hermitian and `m` is even, then `ρ(β, l)^m` is positive semidefinite; with `β/n` in place of
`β` and `m = n`, this is the positivity of `ρ(β/n, l_proj)^n`. The source states positive
definiteness; see the module docstring. -/
theorem posSemidef_truncatedExp_pow {h : κ → Matrix ι ι ℂ} (hh : ∀ k, (h k).IsHermitian)
    (β : ℝ) {m : ℕ} (hm : Even m) : ((truncatedExp G large h β) ^ m).PosSemidef :=
  posSemidef_pow_of_even (isHermitian_truncatedExp G large hh β) hm

end TNLean.Lattice.ClusterExpansion
