/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ImageReflectionCircuit
import TNLean.MPS.Preparation.CleanUnitaryImplementation

/-!
# Exact amplification circuits with a shared initialized workspace

The implementing child circuit and the two reflection circuits are the
induction data. Their common workspace is represented by an isometric
inclusion `J`. Each circuit implements its logical unitary on the entire
initialized logical space. The inverse child call is therefore clean,
and all reflection rounds reuse the same workspace.

The resulting circuit acts exactly as normalized postselection on the
specified input isometry, with its complete global phase retained.
Source: the circuit assembly in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

/-- Clean child and reflection circuits assemble into the phase-exact
amplification circuit. The workspace inclusion and each clean action are
the induction data, and the logical child unitarity and inverse cleanup
are derived from them. Source: the circuit assembly in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_exact_clean_amplification_circuit
    {d n K B L : ℕ} {κ m : Type*} [Fintype κ] [Fintype m]
    [DecidableEq κ] [DecidableEq m]
    (hn : 2 ≤ n) (J : Matrix (Cfg d n) κ ℂ) (hJ : J.IsIsometry)
    (E : Matrix κ m ℂ) (hE : E.IsIsometry)
    (Z : Matrix κ κ ℂ) (U R S : Matrix (Cfg d n) (Cfg d n) ℂ)
    (hU : IsPairProduct d n K U) (hUclean : IsCleanImplementation J U Z)
    (hR : IsPairProduct d n B R)
    (hRclean : IsCleanImplementation J R (subspaceReflection (E * Eᴴ)))
    (P : Matrix κ κ ℂ) (hP : IsStarProjection P)
    (hS : IsPairProduct d n L S)
    (hSclean : IsCleanImplementation J S (subspaceReflection P))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hprob : (Z * E)ᴴ * P * (Z * E) =
      (Real.sin (Real.pi / (4 * (ℓ : ℝ) + 2)) : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    ∃ W : Matrix (Cfg d n) (Cfg d n) ℂ,
      IsPairProduct d n (ℓ * (1 + (2 * K + B + L)) + K) W ∧
      IsCleanImplementation J W
        (postselectionAmplificationStep (Z * E) P ^ ℓ * Z) ∧
      W * (J * E) = J * postselectionSuccess (Z * E) P
        (Real.sin (Real.pi / (4 * (ℓ : ℝ) + 2))) := by
  have hZ := hUclean.logical_mem_unitary hJ hU.mem_unitary
  have hZgram : Zᴴ * Z = 1 := Unitary.star_mul_self_of_mem hZ
  have hV : (Z * E)ᴴ * (Z * E) = 1 := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Zᴴ Z, hZgram, Matrix.one_mul, hE]
  let Q : Matrix (Cfg d n) (Cfg d n) ℂ := -(U * R * Uᴴ * S)
  have hQ : IsPairProduct d n (1 + (2 * K + B + L)) Q := by
    have hprod := ((hU.mul hR).mul hU.star).mul hS
    have hphase := MPSPreparation.isPairProduct_neg_one (d := d) hn
    simpa only [Q, star_eq_conjTranspose, neg_one_mul,
      show K + B + K + L = 2 * K + B + L by omega] using hphase.mul hprod
  have hQclean : IsCleanImplementation J Q (postselectionAmplificationStep (Z * E) P) := by
    have hprod := ((hUclean.mul hRclean).mul
      (hUclean.conjTranspose_of_isometry hJ hU.mem_unitary)).mul hSclean
    change (U * R * Uᴴ * S) * J =
      J * (Z * subspaceReflection (E * Eᴴ) * Zᴴ * subspaceReflection P) at hprod
    change -(U * R * Uᴴ * S) * J = J *
      -(subspaceReflection ((Z * E) * (Z * E)ᴴ) * subspaceReflection P)
    rw [Matrix.neg_mul, hprod, Matrix.mul_neg, subspaceReflection_image Z E hZ]
  refine ⟨Q ^ ℓ * U, (hQ.pow ℓ).mul hU,
    (hQclean.pow ℓ).mul hUclean, ?_⟩
  have hclean := (hQclean.pow ℓ).mul hUclean
  change (Q ^ ℓ * U) * J = J * (postselectionAmplificationStep (Z * E) P ^ ℓ * Z)
    at hclean
  rw [← Matrix.mul_assoc, hclean]
  simp only [Matrix.mul_assoc]
  rw [postselectionAmplificationStep_pow_eq_success (Z * E) P hV hP ℓ hℓ hprob]

end MPUCircuit
