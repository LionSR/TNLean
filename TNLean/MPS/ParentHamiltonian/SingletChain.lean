/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CyclicWindowPermutation
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Periodic chains with the singlet parent interaction

The two-qubit singlet projection is one half of the identity minus the site
transposition. Translating this interaction around a ring gives the
ferromagnetic Heisenberg Hamiltonian. The coordinate identity below applies
to any tensor whose two-site parent interaction is this projection.

**Transitional (#10948).** `localTermES_apply_of_singlet_parentInteraction` and
`parentHamiltonianES_apply_of_singlet_parentInteraction`, the same identities for the
Euclidean-space operators, are kept until their users are converted; the last section states
them for the terms and the Hamiltonian of the parent interaction on the ring.
-/

open scoped BigOperators

namespace MPSTensor

/-- A singlet parent interaction acts at each cyclic bond by subtracting the
coefficient with the two spins exchanged. -/
theorem localTermES_apply_of_singlet_parentInteraction {D N : ℕ}
    (A : MPSTensor 2 D)
    (hA : ∀ (v : EuclideanSpace ℂ (Cfg 2 2)) (σ : Cfg 2 2),
      parentInteractionES A 2 v σ = (v σ - v (σ ∘ Fin.rev)) / 2)
    (hN : 2 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    localTermES A 2 i v σ =
      (v σ - v (σ ∘ Equiv.swap i (cyclicForwardSite i 1))) / 2 := by
  rw [localTermES_apply A 2 i hN, hA]
  have hrev : (Fin.rev : Fin 2 → Fin 2) = Equiv.swap 0 1 := by
    funext j
    fin_cases j <;> decide
  change (v (cyclicCfg (Fin.pos i) 2 i (extractWindow 2 i σ) σ) -
    v (cyclicCfg (Fin.pos i) 2 i (extractWindow 2 i σ ∘ Fin.rev) σ)) / 2 = _
  rw [hrev, cyclicCfg_extractWindow (Fin.pos i) hN,
    cyclicCfg_extractWindow_comp_swap_of_le (Fin.pos i) hN]
  simp

/-- The periodic Hamiltonian with a singlet parent interaction is the sum
of nearest-neighbour singlet projections. -/
theorem parentHamiltonianES_apply_of_singlet_parentInteraction {D N : ℕ}
    (A : MPSTensor 2 D)
    (hA : ∀ (v : EuclideanSpace ℂ (Cfg 2 2)) (σ : Cfg 2 2),
      parentInteractionES A 2 v σ = (v σ - v (σ ∘ Fin.rev)) / 2)
    (hN : 2 ≤ N) (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    parentHamiltonianES A 2 N v σ =
      (∑ i : Fin N, (v σ - v (σ ∘ Equiv.swap i (cyclicForwardSite i 1)))) / 2 := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    localTermES_apply_of_singlet_parentInteraction A hA hN, Finset.sum_div]

/-! ### The parent interaction on the ring -/

/-- A singlet parent interaction acts at each cyclic bond by subtracting the
coefficient with the two spins exchanged: the term of the parent interaction on the ring at
`i`. -/
theorem toEuclideanLin_parentRingInteraction_term_apply_of_singlet_parentInteraction {D N : ℕ}
    (A : MPSTensor 2 D)
    (hA : ∀ (v : EuclideanSpace ℂ (Cfg 2 2)) (σ : Cfg 2 2),
      Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A 2)) v σ =
        (v σ - v (σ ∘ Fin.rev)) / 2)
    (hN : 2 ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    Matrix.toEuclideanLin ((parentRingInteraction A hN).term i) v σ =
      (v σ - v (σ ∘ Equiv.swap i (cyclicForwardSite i 1))) / 2 := by
  rw [toEuclideanLin_parentRingInteraction_term_apply A hN i, hA]
  have hrev : (Fin.rev : Fin 2 → Fin 2) = Equiv.swap 0 1 := by
    funext j
    fin_cases j <;> decide
  change (v (cyclicCfg (Fin.pos i) 2 i (extractWindow 2 i σ) σ) -
    v (cyclicCfg (Fin.pos i) 2 i (extractWindow 2 i σ ∘ Fin.rev) σ)) / 2 = _
  rw [hrev, cyclicCfg_extractWindow (Fin.pos i) hN,
    cyclicCfg_extractWindow_comp_swap_of_le (Fin.pos i) hN]
  simp

/-- The Hamiltonian of the parent interaction on the ring with a singlet parent interaction is
the sum of nearest-neighbour singlet projections. -/
theorem toEuclideanLin_hamiltonian_parentRingInteraction_apply_of_singlet_parentInteraction
    {D N : ℕ} (A : MPSTensor 2 D)
    (hA : ∀ (v : EuclideanSpace ℂ (Cfg 2 2)) (σ : Cfg 2 2),
      Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A 2)) v σ =
        (v σ - v (σ ∘ Fin.rev)) / 2)
    (hN : 2 ≤ N) (v : EuclideanSpace ℂ (Cfg 2 N)) (σ : Cfg 2 N) :
    Matrix.toEuclideanLin (parentRingInteraction A hN).hamiltonian v σ =
      (∑ i : Fin N, (v σ - v (σ ∘ Equiv.swap i (cyclicForwardSite i 1)))) / 2 := by
  rw [ManyBody.Interaction.hamiltonian, map_sum]
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    toEuclideanLin_parentRingInteraction_term_apply_of_singlet_parentInteraction A hA hN,
    Finset.sum_div]

end MPSTensor
