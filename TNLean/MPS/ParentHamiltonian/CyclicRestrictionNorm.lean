/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.CyclicWindowIndex
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# The norm partition for actual cyclic restrictions

A full exterior configuration records the window coordinates redundantly.
Summing all squared restriction norms therefore counts each full coefficient
exactly \(d^L\) times. Dividing by that multiplicity gives the actual normalized
restriction identity used by the finite parent and uncle Hamiltonians.
-/

noncomputable section

open scoped BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- Split a configuration into a cyclic window of length L and its ordered
complement, starting at the supplied physical site. -/
def cyclicWindowCfgEquiv {N L : ℕ} (hN : L ≤ N) (i : Fin N) :
    Cfg d L × Cfg d (N - L) ≃ Cfg d N :=
  (Equiv.sumArrowEquivProdArrow (Fin L) (Fin (N - L)) (Fin d)).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d) (cyclicWindowIndexEquiv L N hN i))

/-- The window coordinates occupy their prescribed cyclic sites. -/
@[simp] theorem cyclicWindowCfgEquiv_apply_window {N L : ℕ} (hN : L ≤ N)
    (i : Fin N) (σ : Cfg d L) (τ : Cfg d (N - L)) (r : Fin L) :
    cyclicWindowCfgEquiv hN i (σ, τ) (cyclicForwardSite i r.val) = σ r := by
  change Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d) (cyclicWindowIndexEquiv L N hN i)
    ((Equiv.sumArrowEquivProdArrow (Fin L) (Fin (N - L)) (Fin d)).symm (σ, τ))
    (cyclicWindowIndexEquiv L N hN i (Sum.inl r)) = σ r
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

/-- Replacing the window keeps its ordered complement and discards the old window. -/
theorem cyclicCfg_cyclicWindowCfgEquiv {N L : ℕ} {η : Cfg d L} (hN : L ≤ N)
    (i : Fin N) (σ : Cfg d L) (τ : Cfg d (N - L)) :
    cyclicCfg (Fin.pos i) L i σ (cyclicWindowCfgEquiv hN i (η, τ)) =
      cyclicWindowCfgEquiv hN i (σ, τ) := by
  funext k
  simp only [cyclicCfg]
  by_cases hk : (k.val + N - i.val) % N < L
  · rw [dite_eq_left hk]
    let r : Fin L := ⟨(k.val + N - i.val) % N, hk⟩
    have hki : k = cyclicForwardSite i r.val := by
      simpa [cyclicForwardSite, r] using
        eq_cyclic_site_of_offset_eq (Fin.pos i) (i := i) (k := k) (r := r.val) rfl
    have hleft : σ ⟨(k.val + N - i.val) % N, hk⟩ = σ r := rfl
    rw [hleft]
    rw [hki]
    exact cyclicWindowCfgEquiv_apply_window hN i σ τ r |>.symm
  · rw [dite_eq_right hk]
    let x := (cyclicWindowIndexEquiv L N hN i).symm k
    have hkx : cyclicWindowIndexEquiv L N hN i x = k := by simp [x]
    rcases x with r | r
    · exfalso
      apply hk
      rw [← hkx]
      change ((cyclicForwardSite i r.val).val + N - i.val) % N < L
      rw [show ((cyclicForwardSite i r.val).val + N - i.val) % N = r.val by
        simpa [cyclicForwardSite] using
          offset_mod_eq i.isLt (Nat.lt_of_lt_of_le r.isLt hN)]
      exact r.isLt
    · change Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d)
          (cyclicWindowIndexEquiv L N hN i)
          ((Equiv.sumArrowEquivProdArrow (Fin L) (Fin (N - L)) (Fin d)).symm
            (η, τ)) k =
        Equiv.piCongrLeft (fun _ : Fin N ↦ Fin d)
          (cyclicWindowIndexEquiv L N hN i)
          ((Equiv.sumArrowEquivProdArrow (Fin L) (Fin (N - L)) (Fin d)).symm
            (σ, τ)) k
      rw [← hkx, Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      rfl


/-- The actual cyclic restrictions count every full-chain coefficient \(d^L\)
times. This identity includes zero physical dimension and empty windows;
the supplied cyclic site already forces the full chain to be nonempty. -/
theorem sum_norm_sq_cyclicRestrictES {N L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    (∑ τ : Cfg d N, ‖cyclicRestrictES (Fin.pos i) L i τ v‖ ^ 2) =
      (d : ℝ) ^ L * ‖v‖ ^ 2 := by
  classical
  let e := cyclicWindowCfgEquiv (d := d) hLN i
  have hv : (∑ τ : Cfg d (N - L), ∑ σ : Cfg d L, ‖v (e (σ, τ))‖ ^ 2) =
      ‖v‖ ^ 2 := by
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type, PiLp.norm_sq_eq_of_L2] using
      e.sum_comp (fun ξ ↦ ‖v ξ‖ ^ 2)
  calc
    _ = ∑ z : Cfg d L × Cfg d (N - L),
        ‖cyclicRestrictES (Fin.pos i) L i (e z) v‖ ^ 2 := by
      exact (e.sum_comp (fun τ ↦ ‖cyclicRestrictES (Fin.pos i) L i τ v‖ ^ 2)).symm
    _ = ∑ η : Cfg d L, ∑ τ : Cfg d (N - L),
        ∑ σ : Cfg d L, ‖v (e (σ, τ))‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro η _
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro σ _
      change ‖v (cyclicCfg (Fin.pos i) L i σ (e (η, τ)))‖ ^ 2 = _
      rw [cyclicCfg_cyclicWindowCfgEquiv]
    _ = (Fintype.card (Cfg d L) : ℝ) * ‖v‖ ^ 2 := by
      rw [hv]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- Averaging over the redundant exterior-window labels preserves the
actual full-chain norm. This is the normalization in the periodic parent
and uncle Hamiltonians, rather than an additional state estimate. -/
theorem inv_pow_mul_sum_norm_sq_cyclicRestrictES {N L : ℕ}
    (hd : d ≠ 0) (hLN : L ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    (((d ^ L : ℕ) : ℝ)⁻¹) *
        (∑ τ : Cfg d N, ‖cyclicRestrictES (Fin.pos i) L i τ v‖ ^ 2) = ‖v‖ ^ 2 := by
  rw [sum_norm_sq_cyclicRestrictES hLN i v, Nat.cast_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero L (Nat.cast_ne_zero.mpr hd)), one_mul]

end MPSTensor
