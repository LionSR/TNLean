/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.CyclicWindowOpenHamiltonian

/-!
# Periodic chains with the singlet parent interaction

The two-qubit singlet projection is one half of the identity minus the site
transposition. Translating this interaction around a ring gives the
ferromagnetic Heisenberg Hamiltonian. The coordinate identity below applies
to any tensor whose two-site parent interaction is this projection.
-/

open scoped BigOperators

namespace MPSTensor

/-- The successor permutation of the sites of a periodic chain. -/
noncomputable def cyclicSuccessorEquiv (N : ℕ) [NeZero N] : Equiv.Perm (Fin N) :=
  (ZMod.finEquiv N).toEquiv |>.trans (Equiv.addRight (1 : ZMod N))
    |>.trans (ZMod.finEquiv N).symm.toEquiv

/-- The successor permutation agrees with motion by one cyclic site. -/
theorem cyclicSuccessorEquiv_apply {N : ℕ} [NeZero N] (i : Fin N) :
    cyclicSuccessorEquiv N i = cyclicForwardSite i 1 := by
  change (ZMod.finEquiv N).symm (ZMod.finEquiv N i + 1) = _
  simpa only [Nat.cast_one, RingEquiv.symm_apply_apply] using
    finEquiv_symm_add_eq_cyclicForwardSite (ZMod.finEquiv N i) 1

/-- The successor on a ring of at least two sites has no fixed point. -/
theorem cyclicSuccessorEquiv_ne {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i : Fin N) :
    cyclicSuccessorEquiv N i ≠ i := by
  let : Fact (1 < N) := ⟨by omega⟩
  intro hi
  change (ZMod.finEquiv N).symm (ZMod.finEquiv N i + 1) = i at hi
  have h := congrArg (ZMod.finEquiv N) hi
  simp only [RingEquiv.apply_symm_apply, add_eq_left] at h
  exact one_ne_zero h

/-- The cyclic successor is addition by one in the group of sites. -/
theorem finEquiv_cyclicSuccessorEquiv {N : ℕ} [NeZero N] (i : Fin N) :
    ZMod.finEquiv N (cyclicSuccessorEquiv N i) = ZMod.finEquiv N i + 1 := by
  change ZMod.finEquiv N ((ZMod.finEquiv N).symm (ZMod.finEquiv N i + 1)) = _
  exact (ZMod.finEquiv N).apply_symm_apply _

/-- The cyclic predecessor is subtraction by one in the group of sites. -/
theorem finEquiv_cyclicSuccessorEquiv_symm {N : ℕ} [NeZero N] (i : Fin N) :
    ZMod.finEquiv N ((cyclicSuccessorEquiv N).symm i) = ZMod.finEquiv N i - 1 := by
  apply (eq_sub_iff_add_eq).2
  simpa only [Equiv.apply_symm_apply] using
    (finEquiv_cyclicSuccessorEquiv ((cyclicSuccessorEquiv N).symm i)).symm

/-- Exchanging two entries of an extracted window exchanges the corresponding
sites when the window is inserted back into the chain. -/
theorem cyclicCfg_extractWindow_comp_swap_of_le {d N L : ℕ}
    (hN : 0 < N) (hLN : L ≤ N) (i : Fin N) (σ : Cfg d N) (a b : Fin L) :
    cyclicCfg hN L i (extractWindow L i σ ∘ Equiv.swap a b) σ =
      σ ∘ Equiv.swap (cyclicForwardSite i a.val) (cyclicForwardSite i b.val) := by
  rw [Equiv.comp_swap_eq_update, Equiv.comp_swap_eq_update, ← update_cyclicCfg hN hLN,
    ← update_cyclicCfg hN hLN, cyclicCfg_extractWindow hN hLN]
  rfl

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
