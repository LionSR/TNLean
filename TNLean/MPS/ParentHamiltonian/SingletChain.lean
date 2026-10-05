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

end MPSTensor
