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
* `MPSTensor.spinSite` : the spin operator \(S^\alpha_j\) acting on site \(j\) of a chain
* `MPSTensor.totalSpinSq` : the squared total spin
  \(\mathbf S^2=\sum_\alpha\bigl(\sum_jS^\alpha_j\bigr)^2\) of a chain

## Main results
* `MPSTensor.spinHalfOperator_sum` : the completeness relation of the spin operators
* `MPSTensor.spinExchange_apply` : \(\mathbf S_j\cdot\mathbf S_k=\tfrac12P_{jk}-\tfrac14\)
  for \(j\ne k\)
* `MPSTensor.sum_spinSite_comp_of_ne`, `MPSTensor.sum_spinSite_comp_self` :
  \(\sum_\alpha S^\alpha_jS^\alpha_k\) is the exchange for \(j\ne k\) and
  \(\tfrac34\) for \(j=k\)
* `MPSTensor.totalSpinSq_eq` : \(\mathbf S^2=\tfrac34N+\sum_{j\ne k}\mathbf S_j\cdot\mathbf S_k\)
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

/-! ### Single-site spin operators and the total spin -/

/-- The squares of the three spin-\(\tfrac12\) operators sum to \(\tfrac34\):
\(\sum_\alpha (S^\alpha S^\alpha)_{pb}=\tfrac34\delta_{pb}\). -/
lemma spinHalfOperator_sum_mul_self (p b : Fin 2) :
    ∑ α, ∑ a, spinHalfOperator α p a * spinHalfOperator α a b =
      if p = b then 3 / 4 else 0 := by
  fin_cases p <;> fin_cases b <;>
    simp [spinHalfOperator, Fin.sum_univ_three] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- The spin operator \(S^\alpha_j\) acting on site \(j\) of a chain of \(N\)
spin-\(\tfrac12\) sites: \((S^\alpha_j\psi)(\sigma)
=\sum_aS^\alpha_{\sigma_ja}\,\psi(\sigma\text{ with }\sigma_j=a)\). -/
def spinSite {N : ℕ} (α : Fin 3) (j : Fin N) : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N where
  toFun ψ σ := ∑ a, spinHalfOperator α (σ j) a * ψ (Function.update σ j a)
  map_add' ψ φ := by
    ext σ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => by ring

/-- The coordinate formula for the single-site spin operator. -/
lemma spinSite_apply {N : ℕ} (α : Fin 3) (j : Fin N) (ψ : NSiteSpace 2 N) (σ : Cfg 2 N) :
    spinSite α j ψ σ = ∑ a, spinHalfOperator α (σ j) a * ψ (Function.update σ j a) := rfl

/-- For two distinct sites, \(\sum_\alpha S^\alpha_jS^\alpha_k\) is the exchange
interaction \(\mathbf S_j\cdot\mathbf S_k\). -/
theorem sum_spinSite_comp_of_ne {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    ∑ α, spinSite α j ∘ₗ spinSite α k = spinExchange j k := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, spinSite_apply,
    Function.update_of_ne hjk.symm, Finset.mul_sum, ← mul_assoc]
  rfl

/-- On a single site, \(\sum_\alpha S^\alpha_jS^\alpha_j=\tfrac34\). -/
theorem sum_spinSite_comp_self {N : ℕ} (j : Fin N) :
    ∑ α, spinSite α j ∘ₗ spinSite α j = (3 / 4 : ℂ) • LinearMap.id := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, spinSite_apply,
    Function.update_self, Function.update_idem, Finset.mul_sum, ← mul_assoc,
    LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  have h : ∀ α : Fin 3, (∑ a, ∑ b, spinHalfOperator α (σ j) a * spinHalfOperator α a b *
      ψ (Function.update σ j b)) = ∑ b, (∑ a, spinHalfOperator α (σ j) a *
        spinHalfOperator α a b) * ψ (Function.update σ j b) := fun α => by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  simp only [h]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, spinHalfOperator_sum_mul_self, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Function.update_eq_self]

/-- The total spin component \(S^\alpha=\sum_jS^\alpha_j\) of a chain of \(N\)
spin-\(\tfrac12\) sites. -/
def totalSpin {N : ℕ} (α : Fin 3) : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N :=
  ∑ j, spinSite α j

/-- The squared total spin \(\mathbf S^2=\sum_\alpha(S^\alpha)^2\) of a chain of
\(N\) spin-\(\tfrac12\) sites, with \(S^\alpha=\sum_jS^\alpha_j\). Its eigenvalue on
the states of total spin \(s\) is \(s(s+1)\). -/
def totalSpinSq {N : ℕ} : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N :=
  ∑ α, totalSpin α ∘ₗ totalSpin α

/-- The squared total spin is \(\tfrac34\) per site plus the exchange of every
ordered pair of distinct sites:
\(\mathbf S^2=\sum_{j,k}\mathbf S_j\cdot\mathbf S_k\), where
\(\mathbf S_j\cdot\mathbf S_j=\tfrac34\). -/
theorem totalSpinSq_eq {N : ℕ} :
    (totalSpinSq : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N) =
      ∑ j, ∑ k, if j = k then (3 / 4 : ℂ) • LinearMap.id else spinExchange j k := by
  simp only [totalSpinSq, totalSpin, ← Module.End.mul_eq_comp, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · subst h; exact sum_spinSite_comp_self j
  · exact sum_spinSite_comp_of_ne h

end MPSTensor

end
