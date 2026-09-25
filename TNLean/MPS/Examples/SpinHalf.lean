/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Spin-\(\tfrac12\) chains: the spin operators and the exchange interaction

The spin-\(\tfrac12\) operators \(S^\alpha=\sigma^\alpha/2\) in the basis
\(|0\rangle,|1\rangle\), and the exchange interaction
\(\mathbf S_j\cdot\mathbf S_k=\sum_\alpha S^\alpha_jS^\alpha_k\) of two spins of a
chain of \(N\) spin-\(\tfrac12\) sites, acting on coefficient vectors. For two
distinct sites the exchange is \(\tfrac12P_{jk}-\tfrac14\), with \(P_{jk}\) the
transposition of the two sites. These are the building blocks of Heisenberg-type
Hamiltonians such as the Majumdar-Ghosh Hamiltonian.

## Main definitions
* `MPSTensor.spinHalfOperator` : the spin-\(\tfrac12\) operators \(S^x,S^y,S^z\)
* `MPSTensor.spinExchange` : the exchange \(\mathbf S_j\cdot\mathbf S_k\) on a chain

## Main results
* `MPSTensor.spinHalfOperator_sum` : the completeness relation of the spin operators
* `MPSTensor.spinExchange_apply` : \(\mathbf S_j\cdot\mathbf S_k=\tfrac12P_{jk}-\tfrac14\)
  for \(j\ne k\)
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

/-- The spin-\(\tfrac12\) operators \(S^x,S^y,S^z\), each half a Pauli matrix,
in the basis \(|0\rangle,|1\rangle\). -/
def spinHalfOperator : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(1 / 2 : ℂ) • !![0, 1; 1, 0], (1 / 2 : ℂ) • !![0, -Complex.I; Complex.I, 0],
    (1 / 2 : ℂ) • !![1, 0; 0, -1]]

/-- The completeness relation of the spin operators:
\(\sum_\alpha S^\alpha_{pa}S^\alpha_{qb}
=\tfrac12\delta_{pb}\delta_{qa}-\tfrac14\delta_{pa}\delta_{qb}\). -/
lemma spinHalfOperator_sum (p q a b : Fin 2) :
    ∑ α, spinHalfOperator α p a * spinHalfOperator α q b =
      (if a = q ∧ b = p then 1 / 2 else 0) - (if a = p ∧ b = q then 1 / 4 else 0) := by
  fin_cases p <;> fin_cases q <;> fin_cases a <;> fin_cases b <;>
    simp [spinHalfOperator, Fin.sum_univ_three] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- The exchange interaction \(\mathbf S_j\cdot\mathbf S_k=\sum_\alpha S^\alpha_jS^\alpha_k\)
of two spins of a chain of \(N\) spin-\(\tfrac12\) sites, acting on coefficient
vectors: \((\mathbf S_j\cdot\mathbf S_k\,\psi)(\sigma)
=\sum_{\alpha,a,b}S^\alpha_{\sigma_j a}S^\alpha_{\sigma_k b}\,
\psi(\sigma\text{ with }\sigma_j=a,\ \sigma_k=b)\). -/
def spinExchange {N : ℕ} (j k : Fin N) : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N where
  toFun ψ σ := ∑ α, ∑ a, ∑ b,
    spinHalfOperator α (σ j) a * spinHalfOperator α (σ k) b *
      ψ (Function.update (Function.update σ j a) k b)
  map_add' ψ φ := by
    ext σ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

/-- For two distinct sites, the exchange interaction is half the transposition of
the two sites minus a quarter: \(\mathbf S_j\cdot\mathbf S_k=\tfrac12P_{jk}-\tfrac14\). -/
theorem spinExchange_apply {N : ℕ} {j k : Fin N} (hjk : j ≠ k) (ψ : NSiteSpace 2 N)
    (σ : Cfg 2 N) :
    spinExchange j k ψ σ = (1 / 2) * ψ (σ ∘ Equiv.swap j k) - (1 / 4) * ψ σ := by
  have hswap : σ ∘ Equiv.swap j k =
      Function.update (Function.update σ j (σ k)) k (σ j) := by
    rw [Equiv.comp_swap_eq_update, Function.update_comm hjk.symm]
  have hself : Function.update (Function.update σ j (σ j)) k (σ k) = σ := by simp
  change (∑ α, ∑ a, ∑ b, spinHalfOperator α (σ j) a * spinHalfOperator α (σ k) b *
      ψ (Function.update (Function.update σ j a) k b)) = _
  have hcomm : (∑ α, ∑ a, ∑ b, spinHalfOperator α (σ j) a * spinHalfOperator α (σ k) b *
      ψ (Function.update (Function.update σ j a) k b)) =
      ∑ a, ∑ b, (∑ α, spinHalfOperator α (σ j) a * spinHalfOperator α (σ k) b) *
        ψ (Function.update (Function.update σ j a) k b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
  rw [hcomm]
  simp only [spinHalfOperator_sum, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rw [hswap, hself]

end MPSTensor

end
