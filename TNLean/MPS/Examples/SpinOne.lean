/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.Algebra.FinVecEta
import TNLean.MPS.Examples.SpinOperator

/-!
# Spin-1 chains: the spin operators and the exchange of two sites

The spin-1 operators \(S^x,S^y,S^z\), the building blocks of spin-1 Hamiltonians
such as the AKLT Hamiltonian. The exchange interaction and the squared total spin
of a spin-1 chain are the general `MPSTensor.spinExchange` and
`MPSTensor.totalSpinSq` for this operator family.

The physical basis is \(|0\rangle=|m{=}0\rangle\), \(|1\rangle=|m{=}{+}1\rangle\),
\(|2\rangle=|m{=}{-}1\rangle\), with the standard phases
\(S^+|0\rangle=\sqrt2\,|1\rangle\) and \(S^+|2\rangle=\sqrt2\,|0\rangle\). This
labelling is the one in which the three matrices of the AKLT tensor
`MPSTensor.akltTensor` are proportional to
\(\sigma^z,\sqrt2\sigma^+,-\sqrt2\sigma^-\) on the indices \(0,1,2\). In this basis
the exchange of two sites is
\(S^z\otimes S^z+\tfrac12(S^+\otimes S^-+S^-\otimes S^+)\), a matrix with integer
entries.

## Main definitions
* `MPSTensor.spinOneOperator` : the spin-1 operators \(S^x,S^y,S^z\)

## Main results
* `MPSTensor.spinOneOperator_sum_mul_self` : \(\mathbf S^2=2=s(s+1)\) on one site
* `MPSTensor.spinExchange_spinOneOperator_zero_one_apply` : the exchange of two
  spin-1 sites as an explicit integer matrix
* `MPSTensor.totalSpinSq_spinOneOperator_two` : on two spin-1 sites,
  \(\mathbf S_{\mathrm{tot}}^2=4+2\,\mathbf S_0\cdot\mathbf S_1\)
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

/-- The spin-1 operators \(S^x,S^y,S^z\) in the basis
\(|0\rangle=|m{=}0\rangle\), \(|1\rangle=|m{=}{+}1\rangle\),
\(|2\rangle=|m{=}{-}1\rangle\), with \(S^x=\tfrac12(S^++S^-)\),
\(S^y=\tfrac1{2i}(S^+-S^-)\) and \(S^z=\operatorname{diag}(0,1,-1)\), where
\(S^+|0\rangle=\sqrt2\,|1\rangle\), \(S^+|2\rangle=\sqrt2\,|0\rangle\) and
\(S^-=(S^+)^\dagger\). The nonzero entries of \(S^x\) and \(S^y\) are
\(\pm1/\sqrt2\) and \(\pm i/\sqrt2\). -/
def spinOneOperator : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![Complex.invSqrtTwo • !![0, 1, 1; 1, 0, 0; 1, 0, 0],
    Complex.invSqrtTwo • !![0, Complex.I, -Complex.I; -Complex.I, 0, 0; Complex.I, 0, 0],
    !![0, 0, 0; 0, 1, 0; 0, 0, -1]]

/-- The squares of the three spin-1 operators sum to \(s(s+1)=2\). -/
lemma spinOneOperator_sum_mul_self :
    ∑ α, spinOneOperator α * spinOneOperator α = (2 : ℂ) • 1 := by
  ext p b
  fin_cases p <;> fin_cases b <;>
    simp [spinOneOperator, Fin.sum_univ_three] <;> ring_nf <;>
    simp [Complex.I_sq, Complex.invSqrtTwo_sq] <;> norm_num

/-- Updating both sites of a two-site configuration gives the new pair. -/
lemma update_update_fin_two {α : Type*} (σ : Fin 2 → α) (a b : α) :
    Function.update (Function.update σ 0 a) 1 b = ![a, b] := by
  ext k
  fin_cases k <;> simp

/-- The exchange of two spin-1 sites,
\(S^z\otimes S^z+\tfrac12(S^+\otimes S^-+S^-\otimes S^+)\), as an explicit integer
matrix: row \((p,q)\) lists \((\mathbf S_0\cdot\mathbf S_1\,v)(p,q)\). -/
lemma spinExchange_spinOneOperator_zero_one_apply (v : NSiteSpace 3 2) (σ : Cfg 3 2) :
    spinExchange spinOneOperator 0 1 v σ =
      !![v ![1, 2] + v ![2, 1], v ![1, 0], v ![2, 0];
        v ![0, 1], v ![1, 1], v ![0, 0] - v ![1, 2];
        v ![0, 2], v ![0, 0] - v ![2, 1], v ![2, 2]] (σ 0) (σ 1) := by
  rw [spinExchange_apply]
  simp only [update_update_fin_two]
  generalize σ 0 = p, σ 1 = q
  fin_cases p <;> fin_cases q <;>
    simp [spinOneOperator, Fin.sum_univ_three] <;> ring_nf <;>
    simp [Complex.I_sq, Complex.invSqrtTwo_sq] <;> ring

/-- On two spin-1 sites the squared total spin is
\(\mathbf S_{\mathrm{tot}}^2=\mathbf S_0^2+\mathbf S_1^2+2\,\mathbf S_0\cdot\mathbf S_1
=4+2\,\mathbf S_0\cdot\mathbf S_1\). -/
theorem totalSpinSq_spinOneOperator_two :
    (totalSpinSq spinOneOperator : NSiteSpace 3 2 →ₗ[ℂ] NSiteSpace 3 2) =
      (4 : ℂ) • LinearMap.id + (2 : ℂ) • spinExchange spinOneOperator 0 1 := by
  rw [totalSpinSq_eq spinOneOperator spinOneOperator_sum_mul_self]
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  rw [spinExchange_comm spinOneOperator (show (1 : Fin 2) ≠ 0 by decide)]
  module

end MPSTensor

end
