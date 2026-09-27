/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Defs

/-!
# Site operators commuting with nearest-neighbour product kernels

On a periodic chain of `N` sites with `d` states per site, a matrix whose entry at the
configurations `(s, t)` is the product `∏_n f(s_n, s_{n+1}, t_n, t_{n+1})` around the ring is a
*nearest-neighbour product kernel*. The periodic operator of a matrix product operator whose
bond index is forced by the physical indices, such as the topological symmetry `Y` of an anyon
chain, has this form. A *site operator* at site `i` changes only the state at site `i`, with an
amplitude `h(t_{i−1}, t_{i+1}, s_i, t_i)` depending on the two neighbours, as the three-site terms
of an anyon-chain Hamiltonian do.

The site operator commutes with the kernel as soon as one three-site identity holds, the local
commutation relation `∑_y h(a',c',b',y) f(a',y,a,b) f(y,c',b,c) = ∑_y f(a',b',a,y) f(b',c',y,c)
h(a,c,y,b)`; the product of the remaining factors around the ring is untouched by a change at
site `i`.

## Main definitions

* `MPOTensor.neighbourKernel`: the nearest-neighbour product kernel.
* `MPOTensor.siteOperator`: the operator acting at one site with neighbour-dependent amplitudes.

## Main results

* `MPOTensor.siteOperator_mul_neighbourKernel`: the local commutation relation implies that the
  site operator commutes with the kernel, on every periodic chain of at least two sites.
-/

open scoped BigOperators

namespace MPOTensor

variable {R : Type*} [CommSemiring R] {d N : ℕ} [NeZero N]

/-- The nearest-neighbour product kernel of `f` on a periodic chain of `N` sites: its entry at
`(s, t)` is `∏_n f(s_n, s_{n+1}, t_n, t_{n+1})`. -/
def neighbourKernel (f : Fin d → Fin d → Fin d → Fin d → R) (N : ℕ) [NeZero N] :
    Matrix (Fin N → Fin d) (Fin N → Fin d) R :=
  Matrix.of fun s t ↦ ∏ n, f (s n) (s (n + 1)) (t n) (t (n + 1))

/-- The operator acting at site `i` with amplitude `h(t_{i−1}, t_{i+1}, s_i, t_i)` from the input
`t` to the output `s`, where `s` and `t` agree away from site `i`. -/
def siteOperator (h : Fin d → Fin d → Fin d → Fin d → R) (i : Fin N) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) R :=
  Matrix.of fun s t ↦
    if ∀ k, k ≠ i → s k = t k then h (t (i - 1)) (t (i + 1)) (s i) (t i) else 0

omit [NeZero N] in
/-- A sum over the configurations that agree with `s` away from site `i` is a sum over the state
at site `i`. -/
theorem sum_ite_agree (s : Fin N → Fin d) (i : Fin N) (g : (Fin N → Fin d) → R) :
    ∑ z, (if ∀ k, k ≠ i → s k = z k then g z else 0) = ∑ y, g (Function.update s i y) := by
  have key : ∀ z : Fin N → Fin d,
      (∀ k, k ≠ i → s k = z k) ↔ z = Function.update s i (z i) := by
    intro z
    constructor
    · intro h
      funext k
      by_cases hk : k = i
      · subst hk
        simp
      · rw [Function.update_of_ne hk, h k hk]
    · intro h k hk
      rw [h, Function.update_of_ne hk]
  symm
  calc ∑ y, g (Function.update s i y)
      = ∑ y, ∑ z, if z = Function.update s i y then g z else 0 := by
        simp
    _ = ∑ z, ∑ y, if z = Function.update s i y then g z else 0 := Finset.sum_comm
    _ = ∑ z, (if ∀ k, k ≠ i → s k = z k then g z else 0) := by
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [Finset.sum_eq_single (z i)]
        · simp only [key z]
        · intro y _ hy
          rw [ite_eq_right_iff]
          intro hz
          exact absurd (by rw [hz]; simp) hy
        · simp

variable {f : Fin d → Fin d → Fin d → Fin d → R} {h : Fin d → Fin d → Fin d → Fin d → R}

private theorem sub_one_ne (hN : 2 ≤ N) (i : Fin N) : i - 1 ≠ i := by
  intro h
  have h1 : (1 : Fin N) = 0 := sub_eq_self.mp h
  have h' := congrArg Fin.val h1
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h'
  exact one_ne_zero h'

private theorem add_one_ne (hN : 2 ≤ N) (i : Fin N) : i + 1 ≠ i := by
  intro h
  exact sub_one_ne hN (i + 1) (by rw [add_sub_cancel_right, h])

/-- The product of the kernel factors away from the two bonds at site `i`. -/
private def restFactor (f : Fin d → Fin d → Fin d → Fin d → R) (i : Fin N)
    (s t : Fin N → Fin d) : R :=
  ∏ n ∈ (Finset.univ.erase i).erase (i - 1), f (s n) (s (n + 1)) (t n) (t (n + 1))

private theorem neighbourKernel_apply_eq (hN : 2 ≤ N) (i : Fin N) (s t : Fin N → Fin d) :
    neighbourKernel f N s t = restFactor f i s t *
      (f (s (i - 1)) (s i) (t (i - 1)) (t i) * f (s i) (s (i + 1)) (t i) (t (i + 1))) := by
  have hmem : i - 1 ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨sub_one_ne hN i, by simp⟩
  rw [neighbourKernel, Matrix.of_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ hmem, restFactor, sub_add_cancel]
  ring

private theorem restFactor_update (i : Fin N) (s t : Fin N → Fin d) (y y' : Fin d) :
    restFactor f i (Function.update s i y) (Function.update t i y') = restFactor f i s t := by
  refine Finset.prod_congr rfl fun n hn ↦ ?_
  obtain ⟨hn1, hn⟩ := Finset.mem_erase.mp hn
  have hn0 : n ≠ i := (Finset.mem_erase.mp hn).1
  have hn2 : n + 1 ≠ i := fun h ↦ hn1 (by rw [← h, add_sub_cancel_right])
  simp only [Function.update_of_ne hn0, Function.update_of_ne hn2]

/-- **A site operator commutes with a nearest-neighbour product kernel** as soon as the local
commutation relation holds on three consecutive sites. -/
theorem siteOperator_mul_neighbourKernel (hN : 2 ≤ N)
    (hloc : ∀ a' b' c' a b c : Fin d,
      ∑ y, h a' c' b' y * f a' y a b * f y c' b c =
        ∑ y, f a' b' a y * f b' c' y c * h a c y b)
    (i : Fin N) :
    siteOperator h i * neighbourKernel f N = neighbourKernel f N * siteOperator h i := by
  ext s t
  have hl := sub_one_ne hN i
  have hr := add_one_ne hN i
  simp only [Matrix.mul_apply, siteOperator, Matrix.of_apply, ite_mul, zero_mul, mul_ite,
    mul_zero]
  simp_rw [show ∀ z : Fin N → Fin d, (∀ k, k ≠ i → z k = t k) ↔ (∀ k, k ≠ i → t k = z k) from
    fun z ↦ forall₂_congr fun _ _ ↦ eq_comm]
  rw [sum_ite_agree s i, sum_ite_agree t i]
  have hK₁ : ∀ y, neighbourKernel f N (Function.update s i y) t = restFactor f i s t *
      (f (s (i - 1)) y (t (i - 1)) (t i) * f y (s (i + 1)) (t i) (t (i + 1))) := by
    intro y
    rw [neighbourKernel_apply_eq hN i, ← restFactor_update (f := f) i s t y (t i),
      Function.update_eq_self]
    simp only [Function.update_self, Function.update_of_ne hl, Function.update_of_ne hr]
  have hK₂ : ∀ y, neighbourKernel f N s (Function.update t i y) = restFactor f i s t *
      (f (s (i - 1)) (s i) (t (i - 1)) y * f (s i) (s (i + 1)) y (t (i + 1))) := by
    intro y
    rw [neighbourKernel_apply_eq hN i, ← restFactor_update (f := f) i s t (s i) y,
      Function.update_eq_self]
    simp only [Function.update_self, Function.update_of_ne hl, Function.update_of_ne hr]
  simp only [Function.update_self, Function.update_of_ne hl, Function.update_of_ne hr, hK₁, hK₂]
  have := hloc (s (i - 1)) (s i) (s (i + 1)) (t (i - 1)) (t i) (t (i + 1))
  calc ∑ y, h (s (i - 1)) (s (i + 1)) (s i) y * (restFactor f i s t *
        (f (s (i - 1)) y (t (i - 1)) (t i) * f y (s (i + 1)) (t i) (t (i + 1))))
      = restFactor f i s t * ∑ y, h (s (i - 1)) (s (i + 1)) (s i) y *
          f (s (i - 1)) y (t (i - 1)) (t i) * f y (s (i + 1)) (t i) (t (i + 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ by ring
    _ = restFactor f i s t * ∑ y, f (s (i - 1)) (s i) (t (i - 1)) y *
          f (s i) (s (i + 1)) y (t (i + 1)) * h (t (i - 1)) (t (i + 1)) y (t i) := by
        rw [this]
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ by ring

end MPOTensor
