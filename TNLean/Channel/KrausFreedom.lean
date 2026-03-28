/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.KrausRepresentation

/-!
# Kraus freedom theorem — rectangular isometry version

This file states the **rectangular Kraus freedom theorem**: if two Kraus
families define the same CP map and the first family has at least as many
operators as the second, then the first family can be expressed as linear
combinations of the second via a rectangular isometry `V` with `V†V = 1`.

This is the necessary direction of Theorem 2.1 item 4 in Wolf (2012),
extended to the case where the two families may have different sizes.
The sufficient direction is `kraus_same_map_of_unitary_combination` in
`TNLean.Channel.KrausRepresentation`.

## Main result

* `kraus_exists_rectangular_isometry` — if `∑ K_i X K_i† = ∑ L_j X L_j†`
  for all `X` and `|ι| ≥ |κ|`, then `∃ V, V†V = 1 ∧ K_i = ∑_j V_ij L_j`.

## References

* M. M. Wolf, *Quantum Channels & Operations*, Theorem 2.1 item 4
* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum
  Information*, Theorem 8.2
-/

open scoped Matrix BigOperators
open Matrix Finset

/-- **Rectangular Kraus freedom theorem** (necessary direction).

If two Kraus families `{K_i}_{i ∈ ι}` and `{L_j}_{j ∈ κ}` define the same
CP map (`∑_i K_i X K_i† = ∑_j L_j X L_j†` for all `X`) and the first
family is at least as large (`card κ ≤ card ι`), then the first family
can be expressed as linear combinations of the second via a rectangular
isometry `V : Matrix ι κ ℂ` satisfying `V†V = 1`.

TODO: prove via Choi matrix PSD factorization and spectral decomposition. -/
theorem kraus_exists_rectangular_isometry
    {D : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (K : ι → Matrix (Fin D) (Fin D) ℂ)
    (L : κ → Matrix (Fin D) (Fin D) ℂ)
    (hcard : Fintype.card κ ≤ Fintype.card ι)
    (heq : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ i, K i * X * (K i)ᴴ = ∑ j, L j * X * (L j)ᴴ) :
    ∃ V : Matrix ι κ ℂ, V.conjTranspose * V = 1 ∧
      ∀ i, K i = ∑ j, V i j • L j := by
  sorry
