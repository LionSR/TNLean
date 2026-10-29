/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm

/-!
# The matrix product form at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1320), extends the high-temperature
matrix product form to every temperature. For `β > β₀` he sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` the smallest even integer such that
`β/n ≤ β₀`. Taking `n` even makes `ρ(β, l_proj)` positive, and the `n` indices at each site, one
from each factor, group into a single index, so the power is again in the form of eq. `mpf`.

This file proves the structural part of that step for any Hermitian operator in product form.

* An even power of a Hermitian matrix is positive semidefinite: `A^{2k} = (A^k)ᴴ A^k`.
* A power of an operator in product form of range `l` is in product form of range `l`
  (`TNLean.Lattice.HasProductForm.pow`, which groups the indices of the factors).
* For `β ≥ 0` and `β₀ > 0` an even `n ≥ 2` with `β/n ≤ β₀` exists.

The actual truncated high-temperature operator is Hermitian, and its even powers have
the required positivity and product form in `TruncatedAllTemperatures.lean`. The error
estimates at every temperature are proved in `TemperatureError.lean`, and the actual local
index counts are proved in `LocalIndexCount.lean`. The least positive even factor count
at positive temperature lies in the interval `[β/β₀, β/β₀ + 2)`.

**Local fix (positivity at every temperature):** the source states that `ρ(β, l_proj)` is
positive definite. An even power of a Hermitian operator is positive semidefinite, and positive
definite only when the base `ρ(β/n, l_proj)` is invertible, which the source does not establish.
The results here state positive semidefiniteness, which is what the even power is used for.
Documented in `docs/paper-gaps/hastings05_mplt_positivity.tex`.

The product-form statements apply to every finite site set and every locality relation;
in particular, they apply to the source's arbitrary finite metric lattice. No planar
embedding is assumed.

## Main results

* `TNLean.Lattice.ClusterExpansion.posSemidef_pow_of_even`: `A^m ≥ 0` for Hermitian `A` and even
  `m`.
* `TNLean.Lattice.HasProductForm.pow_of_even`: for Hermitian `ρ` in product
  form of range `l` and even `m`, `ρ^m` is positive semidefinite and in product form of range `l`.
* `TNLean.Lattice.ClusterExpansion.exists_even_div_le`: an even number of factors suffices.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1320.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An even power `A^{2k} = (A^k)ᴴ A^k` of a Hermitian matrix is positive semidefinite. -/
theorem posSemidef_pow_two_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ (2 * k)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (A ^ k)
  rwa [(hA.pow k).eq, ← pow_add, ← two_mul] at h

/-- **Positivity at every temperature.** An even power of a Hermitian matrix is positive
semidefinite. This is why Hastings takes the number of factors in eq. `mplt` even.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1313–1314. -/
theorem posSemidef_pow_of_even {A : Matrix n n ℂ} (hA : A.IsHermitian) {m : ℕ} (hm : Even m) :
    (A ^ m).PosSemidef := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul]
  exact posSemidef_pow_two_mul hA k

/-- **Eq. `mplt` keeps the matrix product form.** Let `ρ` be a Hermitian operator in product form
of range `l`, as the truncated high-temperature density matrix `ρ(β/n, l_proj)` is. For even `m`
the power `ρ^m` is positive semidefinite and again in product form of range `l`, the `m`
indices at each site being grouped into one. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1303–1317. -/
theorem _root_.TNLean.Lattice.HasProductForm.pow_of_even
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {near : ι → ι → Prop}
    {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hρ : HasProductForm q near ρ)
    (hH : ρ.IsHermitian) {m : ℕ} (hm : Even m) :
    HasProductForm q near (ρ ^ m) ∧ (ρ ^ m).PosSemidef :=
  ⟨hρ.pow m, posSemidef_pow_of_even hH hm⟩

/-- The least even integer not below the temperature ratio. For positive temperatures
this integer is positive. Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312. -/
noncomputable def evenTemperatureFactors (β β₀ : ℝ) : ℕ := 2 * ⌈(β / β₀) / 2⌉₊

/-- The canonical even factor count is positive, reaches the high-temperature regime,
and differs from `β/β₀` by less than two.
Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312 and 1334–1347. -/
theorem evenTemperatureFactors_spec {β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) :
    Even (evenTemperatureFactors β β₀) ∧ 2 ≤ evenTemperatureFactors β β₀ ∧
      β / evenTemperatureFactors β β₀ ≤ β₀ ∧
      β / β₀ ≤ evenTemperatureFactors β β₀ ∧
      (evenTemperatureFactors β β₀ : ℝ) < β / β₀ + 2 := by
  have hhalf : 0 < (β / β₀) / 2 := div_pos (div_pos hβ hβ₀) (by norm_num)
  have hceil : 0 < ⌈(β / β₀) / 2⌉₊ := Nat.ceil_pos.mpr hhalf
  have hm : 2 ≤ evenTemperatureFactors β β₀ := by unfold evenTemperatureFactors; omega
  have hmreal : (0 : ℝ) < evenTemperatureFactors β β₀ := by exact_mod_cast (by omega :
    0 < evenTemperatureFactors β β₀)
  have hlo : β / β₀ ≤ evenTemperatureFactors β β₀ := by
    have := Nat.le_ceil ((β / β₀) / 2)
    unfold evenTemperatureFactors
    push_cast
    nlinarith
  refine ⟨even_two_mul _, hm, ?_, hlo, ?_⟩
  · rw [div_le_iff₀ hmreal]
    have := (div_le_iff₀ hβ₀).mp hlo
    nlinarith
  · have := Nat.ceil_lt_add_one hhalf.le
    unfold evenTemperatureFactors
    push_cast
    nlinarith

/-- The canonical factor count is minimal among positive even choices that enter the
high-temperature regime. Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312. -/
theorem evenTemperatureFactors_le {β β₀ : ℝ} (hβ₀ : 0 < β₀) {m : ℕ}
    (hm : Even m) (hmpos : 0 < m) (hdiv : β / m ≤ β₀) : evenTemperatureFactors β β₀ ≤ m := by
  obtain ⟨k, rfl⟩ := hm
  have hmreal : (0 : ℝ) < ((k + k : ℕ) : ℝ) := by exact_mod_cast hmpos
  have hbound := (div_le_iff₀ hmreal).mp hdiv
  have hceil : ⌈(β / β₀) / 2⌉₊ ≤ k := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), div_le_iff₀ hβ₀]
    push_cast at hbound
    nlinarith
  unfold evenTemperatureFactors
  omega

/-- The factor count yields the corrected `β/β₀ + 2` exponential bound for every
nonnegative cluster weight. Hastings, arXiv:cond-mat/0508554v3, lines 1334–1347;
`docs/paper-gaps/hastings05_temperature_factor_count.tex`. -/
theorem exp_evenTemperatureFactors_mul_sub_one_le {β β₀ A : ℝ}
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hA : 0 ≤ A) :
    Real.exp ((evenTemperatureFactors β β₀ : ℝ) * A) - 1 ≤
      Real.exp ((β / β₀ + 2) * A) - 1 := by
  have hcount := (evenTemperatureFactors_spec hβ hβ₀).2.2.2.2
  exact sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcount.le hA)) 1

/-- **The number of factors in eq. `mplt`.** For `β ≥ 0` and `β₀ > 0` there is an even
`n ≥ 2` with `β/n ≤ β₀`. At positive temperature the witness is the least such even integer;
at `β = 0` take two factors. Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312. -/
theorem exists_even_div_le {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : 0 < β₀) :
    ∃ m : ℕ, Even m ∧ 2 ≤ m ∧ β / m ≤ β₀ := by
  rcases hβ.eq_or_lt with hzero | hpos
  · refine ⟨2, by decide, le_rfl, ?_⟩
    simpa only [← hzero, zero_div] using hβ₀.le
  · have hs := evenTemperatureFactors_spec hpos hβ₀
    exact ⟨evenTemperatureFactors β β₀, hs.1, hs.2.1, hs.2.2.1⟩

end TNLean.Lattice.ClusterExpansion
