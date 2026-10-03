/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ExactUniformMerging
import TNLean.Circuit.Gates.ControlledProducts

/-!
# A physical qudit circuit for success attenuation

The binary attenuation rotation is placed on physical levels zero and one of
a qudit of dimension `d ≥ 2`, and acts as the identity on the other levels.
Its initialized first column is exactly
`t |0⟩ + sqrt (1 - t²) |1⟩`. The physical matrix is unitary whenever `t² ≤ 1`.
Placing it at any site of a chain of `n ≥ 2` sites gives an actual circuit of
at most `2 * n` neighboring-pair gates, with its phase retained.

For the prescribed merger attenuation, feasibility is derived from the exact
amplification budget. No rotation, unitary, circuit, or additional angle
witness is assumed. Source: the fixed-size attenuation primitive in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. This module proves the
physical primitive, separately from the complete recursive circuit theorem.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix

namespace MPUCircuit

/-- The binary attenuation rotation on physical levels zero and one, extended
by the identity on the remaining qudit levels. -/
noncomputable def attenuationQuditRotation {d : ℕ} (hd : 2 ≤ d) (t : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  twoLevel (Fin.castLE hd 0) (Fin.castLE hd 1) (Matrix.attenuationRotation t)

/-- The physical attenuation rotation is unitary on all qudit inputs. -/
theorem attenuationQuditRotation_mem_unitary {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht : t ^ 2 ≤ 1) :
    attenuationQuditRotation hd t ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  exact twoLevel_mem_unitary
    (fun h ↦ (by decide : (0 : Fin 2) ≠ 1) (Fin.castLE_injective hd h))
    (Matrix.attenuationRotation_mem_unitaryGroup t ht)

/-- The initialized flag has exactly the two required real amplitudes. -/
theorem attenuationQuditRotation_mulVec_zero {d : ℕ} (hd : 2 ≤ d) (t : ℝ) :
    attenuationQuditRotation hd t *ᵥ (Pi.single (Fin.castLE hd 0) (1 : ℂ)) =
      (t : ℂ) • Pi.single (Fin.castLE hd 0) (1 : ℂ) +
      (Real.sqrt (1 - t ^ 2) : ℂ) • Pi.single (Fin.castLE hd 1) (1 : ℂ) := by
  ext a
  rw [attenuationQuditRotation, twoLevel_mulVec_apply
    (fun h ↦ (by decide : (0 : Fin 2) ≠ 1) (Fin.castLE_injective hd h))]
  simp [Matrix.attenuationRotation, Pi.single_apply, Fin.ext_iff, eq_comm]
  split_ifs <;> simp_all

/-- The physically placed rotation has an actual neighboring-pair circuit.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_siteOp_attenuationQuditRotation {d n : ℕ}
    (hd : 2 ≤ d) (hn : 2 ≤ n) (k : Fin n) (t : ℝ) (ht : t ^ 2 ≤ 1) :
    IsPairProduct d n (2 * n) (siteOp k (attenuationQuditRotation hd t)) := by
  exact isPairProduct_of_mem_supportedOperators_card_le_two (by omega) hn
    (T := {k}) (by simp)
    (siteOp_mem_unitary k (attenuationQuditRotation_mem_unitary hd t ht))
    (by simpa using siteOp_mem_supportedOperators k (attenuationQuditRotation hd t))

/-- The prescribed merger attenuation has a derived physical circuit, with no
additional angle or unitary hypothesis.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_siteOp_mergingAttenuation {d n : ℕ}
    (hd : 2 ≤ d) (hn : 2 ≤ n) (k : Fin n) (r : ℕ) (hr : 0 < r) :
    IsPairProduct d n (2 * n)
      (siteOp k (attenuationQuditRotation hd (mergingAttenuation r))) := by
  apply isPairProduct_siteOp_attenuationQuditRotation hd hn k
  have ht := mergingAttenuation_pos_le_one r hr
  nlinarith [ht.1, ht.2]

end MPUCircuit
