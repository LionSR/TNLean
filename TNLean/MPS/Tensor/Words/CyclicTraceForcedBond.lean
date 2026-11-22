/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Tensor.Words.CyclicTrace

/-!
# Periodic amplitudes along a forced bond configuration

The amplitude of the periodic vector of a tensor at a configuration `σ` is the sum over closed
bond configurations `g` of the products `∏_n A^{σ_n}_{g_n g_{n+1}}` around the chain. When every
bond configuration except one meets a vanishing factor, the amplitude is the single product along
the surviving configuration. This is the vector counterpart of
`MPOTensor.mpo_apply_eq_prod_of_forced_bond`.

## Main results

* `MPSTensor.mpv_eq_sum_cyclic`: the amplitude as a sum over closed bond configurations.
* `MPSTensor.mpv_eq_prod_of_forced_bond`: the amplitude as the product along the unique bond
  configuration that is not forced to vanish.
* `MPSTensor.mpv_of_forced_left_bond`, `MPSTensor.mpv_of_forced_right_bond`: for a tensor whose
  incoming (or outgoing) bond is a function of the physical letter, the amplitude is the product
  of the entries along the forced bonds.

## Periodic vectors of bond-one tensors

A bond-one periodic vector is the product of its one-site scalar entries.
A nonzero letter therefore gives a nonzero vector at every positive
length, including lengths preceding any injectivity threshold.

Source: the trace-MPS definition in SPWC10, arXiv:0909.5347, and the
finite-prefix boundary of Theorem 5, local main.tex lines 850--880.
-/

section

open scoped BigOperators

namespace MPSTensor

variable {d D N : ℕ} [NeZero N]

/-- The amplitude of the periodic vector at `σ` is the sum over closed bond configurations of the
products of the tensor entries around the chain. -/
theorem mpv_eq_sum_cyclic (A : MPSTensor d D) (σ : Fin N → Fin d) :
    mpv A σ = ∑ g : Fin N → Fin D, ∏ n : Fin N, A (σ n) (g n) (g (n + 1)) :=
  trace_evalWord_eq_sum_cyclic A σ

/-- **A periodic amplitude along a forced bond configuration.** If every closed bond
configuration other than `g₀` meets a vanishing tensor entry, then the amplitude of the periodic
vector at `σ` is the product of the tensor entries along `g₀`. -/
theorem mpv_eq_prod_of_forced_bond (A : MPSTensor d D) (σ : Fin N → Fin d)
    (g₀ : Fin N → Fin D) (h : ∀ g, g ≠ g₀ → ∃ n, A (σ n) (g n) (g (n + 1)) = 0) :
    mpv A σ = ∏ n : Fin N, A (σ n) (g₀ n) (g₀ (n + 1)) := by
  rw [mpv_eq_sum_cyclic, Fintype.sum_eq_single g₀]
  intro g hg
  obtain ⟨n, hn⟩ := h g hg
  exact Finset.prod_eq_zero (Finset.mem_univ n) hn

/-- **The periodic amplitude of a tensor with a forced incoming bond.** Suppose that the entry
`A^i_{lr}` vanishes unless the incoming bond is `l = β i`, and then equals `φ i r`. Then the
amplitude of the periodic vector at `σ` is the product over the sites `n` of the entry of site
`n` evaluated at the bond forced by site `n + 1`. -/
theorem mpv_of_forced_left_bond {A : MPSTensor d D} {β : Fin d → Fin D} {φ : Fin d → Fin D → ℂ}
    (hA : ∀ i l r, A i l r = if l = β i then φ i r else 0) (σ : Fin N → Fin d) :
    mpv A σ = ∏ n : Fin N, φ (σ n) (β (σ (n + 1))) := by
  rw [mpv_eq_prod_of_forced_bond A σ (fun n ↦ β (σ n)) fun g hg ↦ ?_]
  · exact Finset.prod_congr rfl fun n _ ↦ by rw [hA, ite_eq_left rfl]
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    exact ⟨n, by rw [hA, ite_eq_right hn]⟩

/-- **The periodic amplitude of a tensor with a forced outgoing bond.** Suppose that the entry
`A^i_{lr}` vanishes unless the outgoing bond is `r = β i`, and then equals `φ i l`. Then the
amplitude at `σ` is the product over the edges `(n, n + 1)` of the entry of site `n + 1` at the
bond forced by site `n`. -/
theorem mpv_of_forced_right_bond {A : MPSTensor d D} {β : Fin d → Fin D}
    {φ : Fin d → Fin D → ℂ} (hA : ∀ i l r, A i l r = if r = β i then φ i l else 0)
    (σ : Fin N → Fin d) :
    mpv A σ = ∏ n : Fin N, φ (σ (n + 1)) (β (σ n)) := by
  rw [mpv_eq_prod_of_forced_bond A σ (fun n ↦ β (σ (n - 1))) fun g hg ↦ ?_]
  · refine (Fintype.prod_equiv (Equiv.addRight 1) _ _ fun n ↦ ?_).symm
    rw [Equiv.coe_addRight, hA, ite_eq_left (by simp), add_sub_cancel_right]
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    refine ⟨n - 1, ?_⟩
    rw [hA, ite_eq_right fun h ↦ hn ?_]
    simpa using h

end MPSTensor

end

section

open scoped BigOperators

namespace MPSTensor

variable {d N : ℕ}

/-- At bond dimension one, the periodic amplitude is the product of the
actual one-site scalar entries. Source: the trace-MPS definition used in
SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880. -/
theorem mpv_apply_of_bondOne [NeZero N] (A : MPSTensor d 1) (σ : Fin N → Fin d) :
    mpv A σ = ∏ k, A (σ k) 0 0 := by
  rw [mpv_eq_prod_of_forced_bond A σ 0
    (fun g hg ↦ absurd (Subsingleton.elim g 0) hg)]
  rfl

/-- A nonzero bond-one letter supplies an actual nonzero periodic
amplitude at every positive length. No finite-length nonvanishing
hypothesis is supplied. Source: SPWC10, Theorem 5, lines 850--880,
product-state specialization of its uniform-bond branch. -/
theorem exists_mpv_ne_zero_of_bondOne (A : MPSTensor d 1)
    (hletter : ∃ i, A i ≠ 0) (hN : 0 < N) : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0 := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, hi⟩ := hletter
  have hentry : A i 0 0 ≠ 0 := by
    intro hzero
    apply hi
    ext p q
    simpa only [show p = 0 from Subsingleton.elim _ _,
      show q = 0 from Subsingleton.elim _ _, Matrix.zero_apply] using hzero
  refine ⟨fun _ ↦ i, ?_⟩
  rw [mpv_apply_of_bondOne]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ ↦ hentry)

end MPSTensor

end
