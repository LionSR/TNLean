/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LiebRobinson.CommutatorRecursion

/-!
# Energy and time rescaling of Heisenberg evolution

Multiplying a Hamiltonian by a real scalar multiplies the evolution time by the same
scalar. In particular, evolution under `H / Δ` at time `Δ t` agrees with evolution under
`H` at physical time `t`. This is the change of units used in Hastings,
arXiv:0705.2024v4, eq. `lrb` and the definition of `ξ`, lines 96–112 and 139–142.
-/

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rescaling the energy by `c` rescales time by `c` in Heisenberg evolution.
Hastings, arXiv:0705.2024v4, lines 96–112 and 139–142. -/
theorem heisenbergEvolution_smul (H : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (c t : ℝ) (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    heisenbergEvolution ((c : ℂ) • H) t A = heisenbergEvolution H (c * t) A := by
  simp only [heisenbergEvolution, smul_comm Complex.I (c : ℂ), ← Complex.coe_smul,
    smul_smul, mul_comm c t, Complex.ofReal_mul, Complex.ofReal_neg, mul_assoc, neg_mul]

/-- Dividing the Hamiltonian by a nonzero energy scale and multiplying time by that
scale leaves Heisenberg evolution unchanged. Hastings, arXiv:0705.2024v4,
lines 96–112 and 139–142. -/
theorem heisenbergEvolution_inv_smul_mul (H : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    {Δ : ℝ} (hΔ : Δ ≠ 0) (t : ℝ) (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    heisenbergEvolution (((Δ⁻¹ : ℝ) : ℂ) • H) (Δ * t) A =
      heisenbergEvolution H t A := by
  rw [heisenbergEvolution_smul, ← mul_assoc, inv_mul_cancel₀ hΔ, one_mul]

end QuantumCircuit
