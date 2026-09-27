/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MajumdarGhoshGroundSpace
import TNLean.MPS.ParentHamiltonian.CoefficientPairing
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Majumdar-Ghosh: the ground space of the review's Hamiltonian

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127),
Appendix A, `Papers/2011.12127/TN-Review-main.tex` lines 2397–2401: the
Majumdar-Ghosh state "appears as the ground state of the spin-\(\tfrac12\)
Hamiltonian \(H=\sum \mathbf S_i\cdot\mathbf S_{i+1}+\tfrac12\sum\mathbf
S_i\cdot\mathbf S_{i+2}\)", and this ground state is a superposition of the singlet
coverings \((1,2),(3,4),\dots\) and \((2,3),(4,5),\dots,(N,1)\).
Review: arXiv:2011.12127, Appendix A, "The Majumdar-Ghosh model".

**Formalized here.** On three spin-\(\tfrac12\) sites the operator
\(\tfrac43(h+\tfrac38)\), one third of the sum of the three transpositions, is the
orthogonal projector onto the orthogonal complement of the three-site ground space
of the Majumdar-Ghosh tensor, that is, its three-site parent interaction. On a
periodic chain of \(N\ge3\) sites this gives
\(H+\tfrac{3N}8=\tfrac34H^{(3)}_{\mathrm{parent}}\). Hence every eigenvalue of
\(H\) is real and at least \(-\tfrac{3N}8\), and the eigenspace for
\(-\tfrac{3N}8\) is the kernel of the parent Hamiltonian. On an even ring of
\(N\ge4\) sites this eigenspace is the span of the two singlet coverings, which
makes them ground states of \(H\) with ground energy \(-\tfrac{3N}8\). On an odd
ring of \(N\ge5\) sites the value \(-\tfrac{3N}8\) is not an eigenvalue.

The same projector is the projector \(P^{3/2}\) onto total spin \(\tfrac32\)
of three spins, so the identity reads
\(H+\tfrac{3N}8=\tfrac34\sum_iP^{3/2}_{i,i+1,i+2}\); the identification with total
spin is proved in `TNLean.MPS.Examples.MajumdarGhoshTotalSpin`.

## Main results
* `MPSTensor.majumdarGhoshTerm_shift_eq_parentInteraction` :
  \(\tfrac43(h+\tfrac38)\) is the three-site parent interaction
* `MPSTensor.majumdarGhoshHamiltonian_add_eq_parentHamiltonian` :
  \(H+\tfrac{3N}8=\tfrac34 H^{(3)}_{\mathrm{parent}}\)
* `MPSTensor.majumdarGhoshHamiltonian_eigenvalue_ge`,
  `MPSTensor.majumdarGhoshHamiltonian_add_isPositive` : \(H\ge-\tfrac{3N}8\)
* `MPSTensor.majumdarGhoshHamiltonian_eigenspace_eq_ker` : the eigenspace for
  \(-\tfrac{3N}8\) is the kernel of the parent Hamiltonian
* `MPSTensor.majumdarGhoshHamiltonian_eigenspace_eq_span`,
  `MPSTensor.majumdarGhoshHamiltonian_hasEigenvalue` : the ground space on even rings
* `MPSTensor.majumdarGhoshHamiltonian_not_hasEigenvalue_of_odd` : odd rings

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators InnerProductSpace ComplexConjugate ComplexOrder
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### The three-site term as a projector -/

/-- The shifted and rescaled three-site term \(\tfrac43(h+\tfrac38)\). -/
local notation "𝐐" => ((4 / 3 : ℂ) •
  (majumdarGhoshTerm + (3 / 8 : ℂ) • (LinearMap.id : NSiteSpace 2 3 →ₗ[ℂ] NSiteSpace 2 3)))

/-- The shifted and rescaled three-site term \(\tfrac43(h+\tfrac38)\) acts as one
third of the sum of the three transpositions of the sites. -/
lemma majumdarGhoshTerm_shift_apply (v : NSiteSpace 2 3) (σ : Cfg 2 3) :
    𝐐 v σ = (1 / 3) * (v (σ ∘ Equiv.swap 0 1) + v (σ ∘ Equiv.swap 1 2) +
      v (σ ∘ Equiv.swap 0 2)) := by
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, majumdarGhoshTerm_apply]
  ring

/-- The operator \(\tfrac43(h+\tfrac38)\) is symmetric for the \(\ell^2\) pairing
of coefficient vectors. -/
private lemma majumdarGhoshTerm_shift_symm (f g : NSiteSpace 2 3) :
    ∑ σ, conj (f σ) * 𝐐 g σ = ∑ σ, conj (𝐐 f σ) * g σ := by
  have hL : ∀ σ : Cfg 2 3, conj (f σ) * 𝐐 g σ =
      1 / 3 * (conj (f σ) * g (σ ∘ Equiv.swap 0 1)) +
        1 / 3 * (conj (f σ) * g (σ ∘ Equiv.swap 1 2)) +
          1 / 3 * (conj (f σ) * g (σ ∘ Equiv.swap 0 2)) := fun σ => by
    rw [majumdarGhoshTerm_shift_apply]; ring
  have hR : ∀ σ : Cfg 2 3, conj (𝐐 f σ) * g σ =
      1 / 3 * (conj (f (σ ∘ Equiv.swap 0 1)) * g σ) +
        1 / 3 * (conj (f (σ ∘ Equiv.swap 1 2)) * g σ) +
          1 / 3 * (conj (f (σ ∘ Equiv.swap 0 2)) * g σ) := fun σ => by
    rw [majumdarGhoshTerm_shift_apply]
    simp only [map_mul, map_add, map_div₀, map_one, map_ofNat]
    ring
  simp only [hL, hR, Finset.sum_add_distrib, ← Finset.mul_sum, sum_conj_mul_comp_swap]

/-- The operator \(\tfrac43(h+\tfrac38)\) is idempotent. For three
spin-\(\tfrac12\) sites the sum \(T\) of the three transpositions satisfies
\(T^2=3T\), because the antisymmetric part of three qubits vanishes. -/
private lemma majumdarGhoshTerm_shift_idem (v : NSiteSpace 2 3) :
    𝐐 (𝐐 v) = 𝐐 v := by
  ext σ
  rw [Matrix.eq_vecCons_fin_three σ]
  generalize σ 0 = a, σ 1 = b, σ 2 = c
  simp only [majumdarGhoshTerm_shift_apply, Matrix.vec3_comp_swap_zero_one,
    Matrix.vec3_comp_swap_one_two, Matrix.vec3_comp_swap_zero_two]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only [Fin.zero_eta, Fin.mk_one] <;> ring

/-- The kernel of \(\tfrac43(h+\tfrac38)\) is the three-site local ground space. -/
private lemma mem_groundSpace_three_iff (u : NSiteSpace 2 3) :
    u ∈ groundSpace majumdarGhoshTensor 3 ↔ 𝐐 u = 0 := by
  rw [majumdarGhosh_groundSpace_three_eq_eigenspace, Module.End.mem_eigenspace_iff]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, smul_eq_zero,
    show (4 / 3 : ℂ) ≠ 0 by norm_num, false_or]
  constructor
  · intro h; rw [h, ← add_smul]; norm_num
  · intro h; rw [add_eq_zero_iff_eq_neg.mp h, ← neg_smul]; norm_num

/-- Bridge: the three-site term, shifted by \(\tfrac38\) and rescaled by
\(\tfrac43\), is the three-site parent interaction of `majumdarGhoshTensor`, the
orthogonal projector onto \(\mathcal G_3^\perp\). -/
theorem majumdarGhoshTerm_shift_eq_parentInteraction :
    (4 / 3 : ℂ) • (majumdarGhoshTerm + (3 / 8 : ℂ) • LinearMap.id) =
      parentInteraction majumdarGhoshTensor 3 := by
  set Q := 𝐐 with hQ
  set e := WithLp.linearEquiv 2 ℂ (NSiteSpace 2 3)
  set G := groundSpaceES majumdarGhoshTensor 3
  have hker : ∀ u, u ∈ G ↔ Q (e u) = 0 := fun u => by
    rw [mem_groundSpaceES_iff, mem_groundSpace_three_iff]
  have hperp : ∀ v, e.symm (Q v) ∈ Gᗮ := by
    intro v
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := majumdarGhoshTerm_shift_symm (e u) v
    rw [← hQ, (hker u).1 hu] at h
    rw [← e.symm_apply_apply u, inner_withLpLinearEquiv_symm, h]
    simp
  have hin : ∀ v, e.symm v - e.symm (Q v) ∈ G := by
    intro v
    have h := majumdarGhoshTerm_shift_idem v
    rw [← hQ] at h
    rw [hker, ← map_sub, e.apply_symm_apply, map_sub, h, sub_self]
  refine LinearMap.ext fun v => ?_
  change Q v = e (Gᗮ.starProjection (e.symm v))
  rw [Submodule.eq_starProjection_of_mem_orthogonal (hperp v)
    (Submodule.le_orthogonal_orthogonal G (hin v)), e.apply_symm_apply]

/-! ### The periodic Hamiltonian -/

/-- Bridge: on a periodic chain of \(N\ge3\) sites, the range-three parent
Hamiltonian of `majumdarGhoshTensor` is one third of the sum, over the windows of
three consecutive sites, of the three transpositions within the window. -/
theorem majumdarGhosh_parentHamiltonian_three_apply {N : ℕ} (hN3 : 3 ≤ N)
    (ψ : NSiteSpace 2 N) (σ : Cfg 2 N) :
    parentHamiltonian majumdarGhoshTensor 3 N ψ σ =
      (1 / 3) * ∑ i : Fin N, (ψ (σ ∘ Equiv.swap i (cyclicForwardSite i 1)) +
        ψ (σ ∘ Equiv.swap (cyclicForwardSite i 1) (cyclicForwardSite i 2)) +
          ψ (σ ∘ Equiv.swap i (cyclicForwardSite i 2))) := by
  have hN : 0 < N := by omega
  have hw : ∀ (i : Fin N) (a b : Fin 3),
      replaceWindow 3 hN3 i σ (extractWindow 3 i σ ∘ Equiv.swap a b) =
        σ ∘ Equiv.swap (cyclicForwardSite i a.val) (cyclicForwardSite i b.val) :=
    fun i a b => cyclicCfg_extractWindow_comp_swap hN hN3 i σ a b
  simp only [parentHamiltonian, LinearMap.sum_apply, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [localTerm, dite_eq_left hN3]
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [← majumdarGhoshTerm_shift_eq_parentInteraction, majumdarGhoshTerm_shift_apply]
  simp only [LinearMap.pi_apply, LinearMap.proj_apply, hw]
  simp [cyclicForwardSite_zero]

/-- Project result: on a periodic chain of \(N\ge3\) sites,
\(H+\tfrac{3N}8=\tfrac34H^{(3)}_{\mathrm{parent}}\), where \(H^{(3)}_{\mathrm{parent}}\)
is the range-three parent Hamiltonian of `majumdarGhoshTensor` and \(H\) is the review's Hamiltonian
(arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2398–2399). -/
theorem majumdarGhoshHamiltonian_add_eq_parentHamiltonian {N : ℕ} (hN3 : 3 ≤ N) :
    majumdarGhoshHamiltonian N + (3 * N / 8 : ℂ) • LinearMap.id =
      (3 / 4 : ℂ) • parentHamiltonian majumdarGhoshTensor 3 N := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, majumdarGhoshHamiltonian_apply hN3,
    majumdarGhosh_parentHamiltonian_three_apply hN3]
  ring

/-- Project result: on a periodic chain of \(N\ge3\) sites, the operator
\(H+\tfrac{3N}8\), transported to the \(\ell^2\) space of coefficient vectors, is
positive, that is, \(H\ge-\tfrac{3N}8\) as operators. -/
theorem majumdarGhoshHamiltonian_add_isPositive {N : ℕ} (hN3 : 3 ≤ N) :
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace 2 N)).symm.toLinearMap ∘ₗ
      (majumdarGhoshHamiltonian N + (3 * N / 8 : ℂ) • LinearMap.id) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 N)).toLinearMap).IsPositive := by
  have h : (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 N)).symm.toLinearMap ∘ₗ
      (majumdarGhoshHamiltonian N + (3 * N / 8 : ℂ) • LinearMap.id) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 N)).toLinearMap =
      (3 / 4 : ℂ) • parentHamiltonianES majumdarGhoshTensor 3 N := by
    rw [majumdarGhoshHamiltonian_add_eq_parentHamiltonian hN3]
    ext v
    simp [parentHamiltonianES]
  rw [h]
  exact (parentHamiltonianES_isPositive majumdarGhoshTensor 3 N).smul_of_nonneg
    (by norm_num [Complex.le_def])

/-- The eigenvalue equation of the review's Hamiltonian, rewritten through the
parent Hamiltonian. -/
private lemma majumdarGhoshHamiltonian_apply_eq_smul_iff {N : ℕ} (hN3 : 3 ≤ N) (μ : ℂ)
    (v : NSiteSpace 2 N) :
    majumdarGhoshHamiltonian N v = μ • v ↔
      parentHamiltonian majumdarGhoshTensor 3 N v = ((4 / 3) * (μ + 3 * N / 8)) • v := by
  have h := LinearMap.congr_fun (majumdarGhoshHamiltonian_add_eq_parentHamiltonian hN3) v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  constructor
  · intro hv
    rw [hv, ← add_smul] at h
    rw [mul_smul, h, smul_smul]
    norm_num
  · intro hv
    rw [hv, smul_smul, show (3 / 4 : ℂ) * (4 / 3 * (μ + 3 * N / 8)) = μ + 3 * N / 8 by ring,
      add_smul] at h
    exact add_right_cancel h

/-- Project result: on a periodic chain of \(N\ge3\) sites, every eigenvalue \(\mu\)
of the review's Hamiltonian \(H\) is real with \(\mu\ge-\tfrac{3N}8\). -/
theorem majumdarGhoshHamiltonian_eigenvalue_ge {N : ℕ} (hN3 : 3 ≤ N) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (majumdarGhoshHamiltonian N) μ) :
    μ.im = 0 ∧ -(3 * N / 8 : ℝ) ≤ μ.re := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hshift : Module.End.HasEigenvalue
      (majumdarGhoshHamiltonian N + (3 * N / 8 : ℂ) • LinearMap.id) (μ + 3 * N / 8) :=
    Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 (by
      simp [Module.End.mem_eigenspace_iff.1 hv.1, add_smul]), hv.2⟩
  have h := Complex.le_def.1 (nonneg_of_hasEigenvalue_of_isPositive_conj
    (majumdarGhoshHamiltonian_add_isPositive hN3) hshift)
  simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.add_im] at h
  norm_num at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Bridge: on a periodic chain of \(N\ge3\) sites, the eigenspace of the review's
Hamiltonian for \(-\tfrac{3N}8\) is the kernel of the range-three parent
Hamiltonian of `majumdarGhoshTensor`. -/
theorem majumdarGhoshHamiltonian_eigenspace_eq_ker {N : ℕ} (hN3 : 3 ≤ N) :
    Module.End.eigenspace (majumdarGhoshHamiltonian N) (-(3 * N / 8) : ℂ) =
      LinearMap.ker (parentHamiltonian majumdarGhoshTensor 3 N) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, majumdarGhoshHamiltonian_apply_eq_smul_iff hN3,
    LinearMap.mem_ker]
  norm_num

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2397–2401.
On an even ring of \(N\ge4\) sites, the eigenspace of the review's Hamiltonian
\(H\) for the eigenvalue \(-\tfrac{3N}8\) is spanned by the two singlet coverings
\((1,2)(3,4)\cdots(N-1,N)\) and \((2,3)(4,5)\cdots(N,1)\). Together with
`majumdarGhoshHamiltonian_eigenvalue_ge`, this is the review's claim that the
ground states of \(H\) are the superpositions of these two coverings. -/
theorem majumdarGhoshHamiltonian_eigenspace_eq_span {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    Module.End.eigenspace (majumdarGhoshHamiltonian N) (-(3 * N / 8) : ℂ) =
      Submodule.span ℂ {pairCoveringEven majumdarGhoshSinglet,
        pairCoveringOdd majumdarGhoshSinglet} := by
  rw [majumdarGhoshHamiltonian_eigenspace_eq_ker (by omega),
    majumdarGhosh_ker_parentHamiltonian_eq_span hN hN4]

/-- Project result: on an even ring of \(N\ge4\) sites, \(-\tfrac{3N}8\) is an
eigenvalue of the review's Hamiltonian, hence its ground energy by
`majumdarGhoshHamiltonian_eigenvalue_ge`. -/
theorem majumdarGhoshHamiltonian_hasEigenvalue {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    Module.End.HasEigenvalue (majumdarGhoshHamiltonian N) (-(3 * N / 8) : ℂ) := by
  rw [Module.End.hasEigenvalue_iff, majumdarGhoshHamiltonian_eigenspace_eq_span hN hN4]
  intro h
  have hmem : (pairCoveringEven majumdarGhoshSinglet : NSiteSpace 2 N) ∈
      (⊥ : Submodule ℂ (NSiteSpace 2 N)) :=
    h ▸ Submodule.subset_span (Set.mem_insert _ _)
  exact (majumdarGhosh_pairCovering_linearIndependent hN hN4).ne_zero 0
    (by simpa using hmem)

/-- Project result: on an odd ring of \(N\ge5\) sites, \(-\tfrac{3N}8\) is not an
eigenvalue of the review's Hamiltonian, so there the bound of
`majumdarGhoshHamiltonian_eigenvalue_ge` is strict. -/
theorem majumdarGhoshHamiltonian_not_hasEigenvalue_of_odd {N : ℕ} (hN : Odd N) (hN5 : 5 ≤ N) :
    ¬ Module.End.HasEigenvalue (majumdarGhoshHamiltonian N) (-(3 * N / 8) : ℂ) := by
  rw [Module.End.hasEigenvalue_iff, majumdarGhoshHamiltonian_eigenspace_eq_ker (by omega),
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) (by omega),
    majumdarGhosh_chainGroundSpace_eq_bot_of_odd hN hN5, not_not]

end MPSTensor

end
