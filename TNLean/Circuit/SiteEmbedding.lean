/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedOperators
import QICLean.Entropy.RegionUnion
import QICLean.ManyBody.Sites.PlaceAlong

/-!
# Configurations agreeing off a set of placed sites

An injective map `e : κ → ι` places a finite set of sites `κ` among a finite set of sites `ι`.
An operator `X` on the placed sites acts on all the sites as `X ⊗ 1`; this is QICLean's
placement along an injection, `ManyBody.placeAlong`, whose entry between two configurations
vanishes unless they agree off the range of `e` (`ManyBody.placeAlong_apply`). This file keeps
the configuration identities used with that placement that QICLean does not state: the
predicate of agreeing off the range, the parametrization of the configurations agreeing with a
given one off the range, and the configurations of `n` sites carrying an input on the last
sites.

These configurations index the gates of the local circuits of arXiv:2307.01696, main text
before Theorem 1 and paragraph "The sequential-RG circuit": a unitary "with constant support"
is a unitary `X` on a constant number `m` of sites, applied at the sites `e 0, …, e (m - 1)`.

## Main definitions

* `QuantumCircuit.AgreeOff` — two configurations agree off the range of `e`.
* `QuantumCircuit.inputCfg` — the configuration carrying a given configuration on the last
  sites and `0` elsewhere.

## Main results

* `QuantumCircuit.sum_agreeOff` — the configurations agreeing with `x` off the range of an
  injective `e` are parametrized by their values on the range.
* `QuantumCircuit.sum_extend_zero` — a sum over extensions by zero along an injection.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Two configurations of the sites `ι` agree at every site outside the range of `e`. -/
def AgreeOff (e : κ → ι) (x y : ι → Fin d) : Prop :=
  ∀ i, (∀ j, e j ≠ i) → x i = y i

instance (e : κ → ι) : DecidableRel (AgreeOff (d := d) e) := fun _ _ => by
  unfold AgreeOff; infer_instance

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem agreeOff_refl (e : κ → ι) (x : ι → Fin d) : AgreeOff e x x := fun _ _ => rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem AgreeOff.symm {e : κ → ι} {x y : ι → Fin d} (h : AgreeOff e x y) :
    AgreeOff e y x := fun i hi => (h i hi).symm

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem AgreeOff.trans {e : κ → ι} {x y z : ι → Fin d} (h : AgreeOff e x y)
    (h' : AgreeOff e y z) : AgreeOff e x z := fun i hi => (h i hi).trans (h' i hi)

/-- The configurations agreeing with `x` off the range of an injective `e` are parametrized by
their values on the range. -/
theorem sum_agreeOff {e : κ → ι} (he : Function.Injective e) (x : ι → Fin d)
    (F : (κ → Fin d) → ℂ) :
    ∑ z : ι → Fin d, (if AgreeOff e x z then F (z ∘ e) else 0) = ∑ u, F u := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun z => z ∘ e) (fun u => Function.extend e u x) ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_univ _
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    rw [Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    funext i
    by_cases h : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [he.extend_apply]; rfl
    · rw [Function.extend_apply' _ _ _ h]
      exact hz i fun j hj => h ⟨j, hj⟩
  · intro u _
    exact Function.extend_comp he _ _
  · intro z _; rfl

/-! ### Configurations with the input on the last sites -/

/-- The configuration of `n` sites carrying `w` on the last `r` sites and `0` elsewhere. -/
def inputCfg (hd : 0 < d) {r : ℕ} (n : ℕ) (w : Fin r → Fin d) : Fin n → Fin d :=
  fun i => if h : n - r ≤ i.val then w ⟨i.val - (n - r), by omega⟩ else ⟨0, hd⟩

theorem inputCfg_self (hd : 0 < d) {r : ℕ} (w : Fin r → Fin d) : inputCfg hd r w = w := by
  funext i
  simp only [inputCfg, Nat.sub_self, zero_le, dite_true, Nat.sub_zero]

/-! ### Sums over extensions by zero -/

theorem sum_extend_zero {α β : Type*} [Fintype α] [Fintype β] {s : α → β}
    (hs : Function.Injective s) (f : α → ℂ) (H : β → ℂ → ℂ) (hH : ∀ u, H u 0 = 0) :
    ∑ u, H u (Function.extend s f 0 u) = ∑ p, H (s p) (f p) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image s))]
  · rw [Finset.sum_image fun p _ p' _ h => hs h]
    exact Finset.sum_congr rfl fun p _ => by rw [hs.extend_apply]
  · intro u _ hu
    have : ¬∃ p, s p = u := by simpa using hu
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, hH]

omit [Fintype ι] [DecidableEq κ] [DecidableEq ι] [Fintype κ] in
theorem eq_extend_of_agreeOff {e : κ → ι} (he : Function.Injective e)
    {y z : ι → Fin d} (h : AgreeOff e y z) : z = Function.extend e (z ∘ e) y := by
  funext i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [he.extend_apply]; rfl
  · rw [Function.extend_apply' _ _ _ hi]
    exact (h i fun j hj => hi ⟨j, hj⟩).symm

end QuantumCircuit
