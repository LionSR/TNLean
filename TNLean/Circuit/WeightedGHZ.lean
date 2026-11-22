/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Protocol.WeightedGHZ

/-!
# Normalized weighted binary GHZ vectors

The weighted binary GHZ vector `a|0…0⟩ + b|1…1⟩` on a nonempty chain is a unit vector when
`|a|² + |b|² = 1`: its squared norm is the sum of the two branch weights
(`QuantumCircuit.norm_ghzState_sq`). The vector, its expectations and its separated
correlations are those of `QICLean.Circuit.Protocol.WeightedGHZ`.

## Main results

* `QuantumCircuit.norm_ghzState_two` — the normalization of the weighted binary GHZ vector.
-/

open Matrix

namespace QuantumCircuit

variable {N : ℕ}

/-- A binary GHZ vector on a nonempty chain is normalized when its two orthogonal branch weights
sum to one. -/
theorem norm_ghzState_two [NeZero N] {a b : ℂ} (hab : star a * a + star b * b = 1) :
    ‖(WithLp.toLp 2 (ghzState (ι := Fin N) ![a, b]) :
      EuclideanSpace ℂ (Fin N → Fin 2))‖ = 1 := by
  have : Nonempty (Fin N) := ⟨0⟩
  have hs : ‖(WithLp.toLp 2 (ghzState (ι := Fin N) ![a, b]) :
      EuclideanSpace ℂ (Fin N → Fin 2))‖ ^ 2 = 1 := by
    rw [norm_ghzState_sq, Fin.sum_univ_two]
    apply Complex.ofReal_injective
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_add,
      Complex.ofReal_pow, Complex.ofReal_one]
    simpa only [Complex.star_def, Complex.conj_mul'] using hab
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hs

end QuantumCircuit
