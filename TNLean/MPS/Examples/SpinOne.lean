/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.Algebra.FinVecEta
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Spin-1 chains: the spin operators and the exchange interaction

The spin-1 operators \(S^x,S^y,S^z\) and the exchange interaction
\(\mathbf S_j\cdot\mathbf S_k=\sum_\alpha S^\alpha_jS^\alpha_k\) of two spins of a
chain of \(N\) spin-1 sites, acting on coefficient vectors. These are the
building blocks of spin-1 Hamiltonians such as the AKLT Hamiltonian.

The physical basis is \(|0\rangle=|m{=}0\rangle\), \(|1\rangle=|m{=}{+}1\rangle\),
\(|2\rangle=|m{=}{-}1\rangle\), with the standard phases
\(S^+|0\rangle=\sqrt2\,|1\rangle\) and \(S^+|2\rangle=\sqrt2\,|0\rangle\). This
labelling is the one in which the AKLT tensor `MPSTensor.akltTensor` carries
\(\sigma^z,\sigma^+,-\sigma^-\) on the indices \(0,1,2\). In this basis the exchange
of two sites is \(S^z\otimes S^z+\tfrac12(S^+\otimes S^-+S^-\otimes S^+)\), a
matrix with integer entries.

## Main definitions
* `MPSTensor.spinOneOperator` : the spin-1 operators \(S^x,S^y,S^z\)
* `MPSTensor.spinOneExchange` : the exchange \(\mathbf S_j\cdot\mathbf S_k\) on a chain

## Main results
* `MPSTensor.spinOneOperator_sum_mul_self` : \(\mathbf S^2=2=s(s+1)\) on one site
* `MPSTensor.spinOneExchange_apply` : the coordinate formula of the exchange
* `MPSTensor.spinOneExchange_zero_one_apply` : the exchange of two spin-1 sites
  as an explicit integer matrix
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

/-- The squares of the three spin-1 operators sum to \(s(s+1)=2\):
\(\sum_\alpha (S^\alpha S^\alpha)_{pb}=2\delta_{pb}\). -/
lemma spinOneOperator_sum_mul_self (p b : Fin 3) :
    ∑ α, ∑ a, spinOneOperator α p a * spinOneOperator α a b =
      if p = b then 2 else 0 := by
  fin_cases p <;> fin_cases b <;>
    simp [spinOneOperator, Fin.sum_univ_three] <;> ring_nf <;>
    simp [Complex.I_sq, Complex.invSqrtTwo_sq] <;> norm_num

/-- The exchange interaction \(\mathbf S_j\cdot\mathbf S_k=\sum_\alpha S^\alpha_jS^\alpha_k\)
of two spins of a chain of \(N\) spin-1 sites, acting on coefficient vectors:
\((\mathbf S_j\cdot\mathbf S_k\,\psi)(\sigma)
=\sum_{\alpha,a,b}S^\alpha_{\sigma_j a}S^\alpha_{\sigma_k b}\,
\psi(\sigma\text{ with }\sigma_j=a,\ \sigma_k=b)\). -/
def spinOneExchange {N : ℕ} (j k : Fin N) : NSiteSpace 3 N →ₗ[ℂ] NSiteSpace 3 N where
  toFun ψ σ := ∑ α, ∑ a, ∑ b,
    spinOneOperator α (σ j) a * spinOneOperator α (σ k) b *
      ψ (Function.update (Function.update σ j a) k b)
  map_add' ψ φ := by
    ext σ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

/-- The coordinate formula of the exchange, with the sum over the three spin
components carried out inside the coefficient. -/
lemma spinOneExchange_apply {N : ℕ} (j k : Fin N) (ψ : NSiteSpace 3 N) (σ : Cfg 3 N) :
    spinOneExchange j k ψ σ =
      ∑ a, ∑ b, (∑ α, spinOneOperator α (σ j) a * spinOneOperator α (σ k) b) *
        ψ (Function.update (Function.update σ j a) k b) := by
  change (∑ α, ∑ a, ∑ b, spinOneOperator α (σ j) a * spinOneOperator α (σ k) b *
      ψ (Function.update (Function.update σ j a) k b)) = _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]

/-- Updating both sites of a two-site configuration gives the new pair. -/
lemma update_update_fin_two {α : Type*} (σ : Fin 2 → α) (a b : α) :
    Function.update (Function.update σ 0 a) 1 b = ![a, b] := by
  ext k
  fin_cases k <;> simp

/-- The exchange of two spin-1 sites,
\(S^z\otimes S^z+\tfrac12(S^+\otimes S^-+S^-\otimes S^+)\), as an explicit integer
matrix: row \((p,q)\) lists \((\mathbf S_0\cdot\mathbf S_1\,v)(p,q)\). -/
lemma spinOneExchange_zero_one_apply (v : NSiteSpace 3 2) (σ : Cfg 3 2) :
    spinOneExchange 0 1 v σ =
      !![v ![1, 2] + v ![2, 1], v ![1, 0], v ![2, 0];
        v ![0, 1], v ![1, 1], v ![0, 0] - v ![1, 2];
        v ![0, 2], v ![0, 0] - v ![2, 1], v ![2, 2]] (σ 0) (σ 1) := by
  rw [spinOneExchange_apply]
  simp only [update_update_fin_two]
  generalize σ 0 = p, σ 1 = q
  fin_cases p <;> fin_cases q <;>
    simp [spinOneOperator, Fin.sum_univ_three] <;> ring_nf <;>
    simp [Complex.I_sq, Complex.invSqrtTwo_sq] <;> ring

end MPSTensor

end
