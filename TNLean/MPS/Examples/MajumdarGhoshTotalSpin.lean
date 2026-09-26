/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MajumdarGhoshLowerBound

/-!
# Majumdar-Ghosh: the three-site term and total spin

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127),
Appendix A, `Papers/2011.12127/TN-Review-main.tex` lines 2397–2401: the
Majumdar-Ghosh state is the ground state of the spin-\(\tfrac12\) Hamiltonian
\(H=\sum \mathbf S_i\cdot\mathbf S_{i+1}+\tfrac12\sum\mathbf S_i\cdot\mathbf S_{i+2}\).
The review writes \(H\) through spin operators and does not itself decompose the
three-site term by total spin; that decomposition is the standard addition of
three spins \(\tfrac12\), which gives total spin \(\tfrac12\) (twice) and
\(\tfrac32\) (once).
Review: arXiv:2011.12127, Appendix A, "The Majumdar-Ghosh model".

**Formalized here.** On three spin-\(\tfrac12\) sites the squared total spin is
\(\mathbf S^2=\tfrac94+4h\) for the three-site term \(h\) of the Majumdar-Ghosh
Hamiltonian, and
\(\mathbf S^2=\tfrac34+3\,\bigl(\tfrac43(h+\tfrac38)\bigr)\). Hence the three-site
local ground space of the Majumdar-Ghosh tensor is the eigenspace of
\(\mathbf S^2\) for \(\tfrac34\), the total-spin-\(\tfrac12\) subspace, and the
three-site parent interaction \(\tfrac43(h+\tfrac38)=\tfrac13(P_{01}+P_{12}+P_{02})\)
is the orthogonal projector \(P^{3/2}\) onto the eigenspace of \(\mathbf S^2\) for
\(\tfrac{15}4\), the total-spin-\(\tfrac32\) subspace.

## Main results
* `MPSTensor.totalSpinSq_three_eq_majumdarGhoshTerm` : \(\mathbf S^2=\tfrac94+4h\)
* `MPSTensor.totalSpinSq_three_eq_parentInteraction` :
  \(\mathbf S^2=\tfrac34+3P^{3/2}\)
* `MPSTensor.majumdarGhosh_groundSpace_three_eq_totalSpinSq_eigenspace` : the
  three-site ground space is the total-spin-\(\tfrac12\) subspace
* `MPSTensor.majumdarGhosh_parentInteraction_eq_spinThreeHalves_starProjection` :
  the three-site parent interaction is the projector onto total spin \(\tfrac32\)

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators InnerProductSpace

noncomputable section

namespace MPSTensor

/-- On three spin-\(\tfrac12\) sites, the squared total spin is \(\tfrac34\) plus
the sum of the three transpositions of the sites. -/
lemma totalSpinSq_three_apply (v : NSiteSpace 2 3) (σ : Cfg 2 3) :
    totalSpinSq v σ = (3 / 4) * v σ + (v (σ ∘ Equiv.swap 0 1) + v (σ ∘ Equiv.swap 1 2) +
      v (σ ∘ Equiv.swap 0 2)) := by
  rw [totalSpinSq_eq]
  simp only [Fin.sum_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq, LinearMap.add_apply,
    Pi.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  rw [spinExchange_apply (by decide), spinExchange_apply (by decide),
    spinExchange_apply (by decide), spinExchange_apply (by decide),
    spinExchange_apply (by decide), spinExchange_apply (by decide),
    Equiv.swap_comm (1 : Fin 3) 0, Equiv.swap_comm (2 : Fin 3) 0,
    Equiv.swap_comm (2 : Fin 3) 1]
  ring

/-- Project result: on three spin-\(\tfrac12\) sites,
\(\mathbf S^2=\tfrac94+4h\) for the three-site Majumdar-Ghosh term
\(h=\tfrac12(\mathbf S_1\cdot\mathbf S_2+\mathbf S_2\cdot\mathbf S_3
+\mathbf S_1\cdot\mathbf S_3)\). -/
theorem totalSpinSq_three_eq_majumdarGhoshTerm :
    (totalSpinSq : NSiteSpace 2 3 →ₗ[ℂ] NSiteSpace 2 3) =
      (9 / 4 : ℂ) • LinearMap.id + (4 : ℂ) • majumdarGhoshTerm := by
  refine LinearMap.ext fun v => funext fun σ => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, totalSpinSq_three_apply, majumdarGhoshTerm_apply]
  ring

/-- Project result: on three spin-\(\tfrac12\) sites,
\(\mathbf S^2=\tfrac34+3P\), where \(P\) is the three-site parent interaction of
`majumdarGhoshTensor`. Since \(P\) is an orthogonal projector, \(\mathbf S^2\) has
the eigenvalue \(\tfrac34\) on \(\ker P\) and \(\tfrac{15}4\) on the range of
\(P\). -/
theorem totalSpinSq_three_eq_parentInteraction :
    (totalSpinSq : NSiteSpace 2 3 →ₗ[ℂ] NSiteSpace 2 3) =
      (3 / 4 : ℂ) • LinearMap.id + (3 : ℂ) • parentInteraction majumdarGhoshTensor 3 := by
  rw [← majumdarGhoshTerm_shift_eq_parentInteraction, totalSpinSq_three_eq_majumdarGhoshTerm]
  refine LinearMap.ext fun v => funext fun σ => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Project result: the addition of three spins \(\tfrac12\), applied to the
Hamiltonian of arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2397–2401. The three-site local ground space
of `majumdarGhoshTensor` is the eigenspace of the squared total spin for
\(\tfrac34=\tfrac12(\tfrac12+1)\), the total-spin-\(\tfrac12\) subspace. -/
theorem majumdarGhosh_groundSpace_three_eq_totalSpinSq_eigenspace :
    groundSpace majumdarGhoshTensor 3 =
      Module.End.eigenspace (totalSpinSq : NSiteSpace 2 3 →ₗ[ℂ] NSiteSpace 2 3) (3 / 4) := by
  rw [majumdarGhosh_groundSpace_three_eq_eigenspace]
  ext v
  simp only [Module.End.mem_eigenspace_iff, totalSpinSq_three_eq_majumdarGhoshTerm,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · intro h
    rw [h]
    module
  · intro h
    have h' : (4 : ℂ) • majumdarGhoshTerm v = (4 : ℂ) • ((-3 / 8 : ℂ) • v) := by
      linear_combination (norm := module) h
    exact smul_right_injective _ (by norm_num) h'

/-- The eigenspace of the squared total spin of three spin-\(\tfrac12\) sites for
\(\tfrac{15}4=\tfrac32(\tfrac32+1)\), the total-spin-\(\tfrac32\) subspace, in the
\(\ell^2\) space of coefficient vectors. -/
def spinThreeHalvesES : Submodule ℂ (EuclideanSpace ℂ (Cfg 2 3)) :=
  (Module.End.eigenspace (totalSpinSq : NSiteSpace 2 3 →ₗ[ℂ] NSiteSpace 2 3) (15 / 4)).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 3)).symm.toLinearMap

/-- The total-spin-\(\tfrac32\) subspace is the orthogonal complement of the
three-site local ground space of `majumdarGhoshTensor`. -/
theorem spinThreeHalvesES_eq_orthogonal_groundSpaceES :
    spinThreeHalvesES = (groundSpaceES majumdarGhoshTensor 3)ᗮ := by
  set e := WithLp.linearEquiv 2 ℂ (NSiteSpace 2 3)
  ext v
  rw [spinThreeHalvesES, Submodule.mem_map_equiv, LinearEquiv.symm_symm,
    ← Submodule.starProjection_eq_self_iff, Module.End.mem_eigenspace_iff,
    totalSpinSq_three_eq_parentInteraction]
  change _ ↔ e.symm (parentInteraction majumdarGhoshTensor 3 (e v)) = v
  rw [e.symm_apply_eq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · intro h
    have h' : (3 : ℂ) • parentInteraction majumdarGhoshTensor 3 (e v) = (3 : ℂ) • e v := by
      linear_combination (norm := module) h
    exact smul_right_injective _ (by norm_num) h'
  · intro h
    rw [h]
    module

/-- Project result: the addition of three spins \(\tfrac12\), applied to the
Hamiltonian of arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`
lines 2397–2401. The three-site parent interaction
of `majumdarGhoshTensor`, which is
\(\tfrac43(h+\tfrac38)=\tfrac13(P_{01}+P_{12}+P_{02})\) by
`majumdarGhoshTerm_shift_eq_parentInteraction`, is the orthogonal projector
\(P^{3/2}\) onto the total-spin-\(\tfrac32\) subspace. -/
theorem majumdarGhosh_parentInteraction_eq_spinThreeHalves_starProjection :
    parentInteraction majumdarGhoshTensor 3 =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 3)).toLinearMap ∘ₗ
        spinThreeHalvesES.starProjection.toLinearMap ∘ₗ
          (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 3)).symm.toLinearMap := by
  rw [parentInteraction, spinThreeHalvesES_eq_orthogonal_groundSpaceES]

end MPSTensor

end
