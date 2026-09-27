/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Spin chains: site operators, the exchange interaction and the total spin

For a family \(S=(S^x,S^y,S^z)\) of \(d\times d\) matrices, the operator
\(S^\alpha_j\) acting on site \(j\) of a chain of \(N\) sites, the exchange
interaction \(\mathbf S_j\cdot\mathbf S_k=\sum_\alpha S^\alpha_jS^\alpha_k\), and the
squared total spin \(\mathbf S^2=\sum_\alpha\bigl(\sum_jS^\alpha_j\bigr)^2\), all acting
on coefficient vectors. The spin-\(\tfrac12\) and spin-\(1\) chains instantiate
these with their spin operators.

## Main definitions
* `MPSTensor.siteOperator` : a one-site operator acting on site \(j\) of a chain
* `MPSTensor.spinExchange` : the exchange \(\mathbf S_j\cdot\mathbf S_k\)
* `MPSTensor.totalSpin`, `MPSTensor.totalSpinSq` : the total spin components and
  the squared total spin

## Main results
* `MPSTensor.spinExchange_apply` : the coordinate formula of the exchange
* `MPSTensor.spinExchange_comm` : \(\mathbf S_j\cdot\mathbf S_k=\mathbf S_k\cdot\mathbf S_j\)
* `MPSTensor.sum_siteOperator_comp_of_ne`, `MPSTensor.sum_siteOperator_comp_self` :
  \(\sum_\alpha S^\alpha_jS^\alpha_k\) is the exchange for \(j\ne k\) and the
  Casimir value \(c\) for \(j=k\) when \(\sum_\alpha(S^\alpha)^2=c\)
* `MPSTensor.totalSpinSq_eq` : \(\mathbf S^2=cN+\sum_{j\ne k}\mathbf S_j\cdot\mathbf S_k\)
* `MPSTensor.cyclicRestrictₗ_spinExchange` : restricting a periodic chain to the
  window \(i,i+1\) turns \(\mathbf S_i\cdot\mathbf S_{i+1}\) into the exchange of a
  two-site chain
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

variable {d N : ℕ}

/-- The operator \(X_j\) acting as the one-site matrix \(X\) on site \(j\) of a chain
of \(N\) sites: \((X_j\psi)(\sigma)=\sum_aX_{\sigma_ja}\,\psi(\sigma\text{ with }\sigma_j=a)\). -/
def siteOperator (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin N) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N where
  toFun ψ σ := ∑ a, X (σ j) a * ψ (Function.update σ j a)
  map_add' ψ φ := by
    ext σ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => by ring

/-- The coordinate formula for a site operator. -/
lemma siteOperator_apply (X : Matrix (Fin d) (Fin d) ℂ) (j : Fin N) (ψ : NSiteSpace d N)
    (σ : Cfg d N) :
    siteOperator X j ψ σ = ∑ a, X (σ j) a * ψ (Function.update σ j a) := rfl

/-- The exchange interaction \(\mathbf S_j\cdot\mathbf S_k=\sum_\alpha S^\alpha_jS^\alpha_k\)
of two sites of a chain of \(N\) sites for the operator family \(S\), acting on
coefficient vectors: \((\mathbf S_j\cdot\mathbf S_k\,\psi)(\sigma)
=\sum_{\alpha,a,b}S^\alpha_{\sigma_j a}S^\alpha_{\sigma_k b}\,
\psi(\sigma\text{ with }\sigma_j=a,\ \sigma_k=b)\). The formula is the exchange only for
distinct sites \(j\ne k\) (`sum_siteOperator_comp_of_ne`); for \(j=k\) the second
update overwrites the first, and the operator \(\sum_\alpha S^\alpha_jS^\alpha_j\) is
given instead by `sum_siteOperator_comp_self`. -/
def spinExchange (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (j k : Fin N) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N where
  toFun ψ σ := ∑ α, ∑ a, ∑ b,
    S α (σ j) a * S α (σ k) b * ψ (Function.update (Function.update σ j a) k b)
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
lemma spinExchange_apply (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (j k : Fin N)
    (ψ : NSiteSpace d N) (σ : Cfg d N) :
    spinExchange S j k ψ σ =
      ∑ a, ∑ b, (∑ α, S α (σ j) a * S α (σ k) b) *
        ψ (Function.update (Function.update σ j a) k b) := by
  change (∑ α, ∑ a, ∑ b, S α (σ j) a * S α (σ k) b *
      ψ (Function.update (Function.update σ j a) k b)) = _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]

/-- The exchange of two distinct sites is symmetric in the two sites. -/
theorem spinExchange_comm (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) {j k : Fin N}
    (hjk : j ≠ k) : spinExchange S j k = spinExchange S k j := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  rw [spinExchange_apply, spinExchange_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Function.update_comm hjk.symm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- For two distinct sites, \(\sum_\alpha S^\alpha_jS^\alpha_k\) is the exchange
interaction \(\mathbf S_j\cdot\mathbf S_k\). -/
theorem sum_siteOperator_comp_of_ne (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) {j k : Fin N}
    (hjk : j ≠ k) :
    ∑ α, siteOperator (S α) j ∘ₗ siteOperator (S α) k = spinExchange S j k := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, siteOperator_apply,
    Function.update_of_ne hjk.symm, Finset.mul_sum, ← mul_assoc]
  rfl

/-- On a single site, \(\sum_\alpha S^\alpha_jS^\alpha_j=c\) when the one-site
matrices satisfy \(\sum_\alpha(S^\alpha)^2=c\). -/
theorem sum_siteOperator_comp_self (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) {c : ℂ}
    (hS : ∑ α, S α * S α = c • 1) (j : Fin N) :
    ∑ α, siteOperator (S α) j ∘ₗ siteOperator (S α) j = c • LinearMap.id := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, siteOperator_apply,
    Function.update_self, Function.update_idem, Finset.mul_sum, ← mul_assoc,
    LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  have h : ∀ α : Fin 3, (∑ a, ∑ b, S α (σ j) a * S α a b * ψ (Function.update σ j b)) =
      ∑ b, (S α * S α) (σ j) b * ψ (Function.update σ j b) := fun α => by
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_mul]
  simp only [h]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Matrix.sum_apply, hS, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Function.update_eq_self]

/-- The total spin component \(S^\alpha=\sum_jS^\alpha_j\) of a chain of \(N\) sites. -/
def totalSpin (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (α : Fin 3) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  ∑ j, siteOperator (S α) j

/-- The squared total spin \(\mathbf S^2=\sum_\alpha(S^\alpha)^2\) of a chain of
\(N\) sites, with \(S^\alpha=\sum_jS^\alpha_j\). For the spin-\(s\) operators its
eigenvalue on the states of total spin \(t\) is \(t(t+1)\). -/
def totalSpinSq (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) : NSiteSpace d N →ₗ[ℂ] NSiteSpace d N :=
  ∑ α, totalSpin S α ∘ₗ totalSpin S α

/-- The squared total spin is the Casimir value \(c\) per site plus the exchange of
every ordered pair of distinct sites, when \(\sum_\alpha(S^\alpha)^2=c\):
\(\mathbf S^2=\sum_{j,k}\mathbf S_j\cdot\mathbf S_k\), where
\(\mathbf S_j\cdot\mathbf S_j=c\). -/
theorem totalSpinSq_eq (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) {c : ℂ}
    (hS : ∑ α, S α * S α = c • 1) :
    (totalSpinSq S : NSiteSpace d N →ₗ[ℂ] NSiteSpace d N) =
      ∑ j, ∑ k, if j = k then c • LinearMap.id else spinExchange S j k := by
  simp only [totalSpinSq, totalSpin, ← Module.End.mul_eq_comp, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · subst h; exact sum_siteOperator_comp_self S hS j
  · exact sum_siteOperator_comp_of_ne S h

/-- Restricting to the cyclic window of sites \(i,i+1\) intertwines the exchange of
these two sites with the exchange of a two-site chain. -/
lemma cyclicRestrictₗ_spinExchange (S : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (hN : 0 < N)
    (hN2 : 2 ≤ N) (i : Fin N) (τ : Cfg d N) (ψ : NSiteSpace d N) :
    cyclicRestrictₗ hN 2 i τ (spinExchange S i (cyclicForwardSite i 1) ψ) =
      spinExchange S 0 1 (cyclicRestrictₗ hN 2 i τ ψ) := by
  ext ω
  have h0 : cyclicCfg hN 2 i ω τ i = ω 0 := by
    simpa [cyclicForwardSite_zero] using cyclicCfg_cyclicForwardSite_apply hN hN2 i ω τ 0
  have h1 : cyclicCfg hN 2 i ω τ (cyclicForwardSite i 1) = ω 1 :=
    cyclicCfg_cyclicForwardSite_apply hN hN2 i ω τ 1
  have hu : ∀ a b : Fin d, Function.update (Function.update (cyclicCfg hN 2 i ω τ) i a)
      (cyclicForwardSite i 1) b =
        cyclicCfg hN 2 i (Function.update (Function.update ω 0 a) 1 b) τ := fun a b => by
    have e0 := update_cyclicCfg hN hN2 i ω τ 0 a
    have e1 := update_cyclicCfg hN hN2 i (Function.update ω 0 a) τ 1 b
    simp only [Fin.val_zero, cyclicForwardSite_zero, Fin.val_one] at e0 e1
    rw [e0, e1]
  simp only [cyclicRestrictₗ_apply, spinExchange_apply, h0, h1, hu]

end MPSTensor

end
