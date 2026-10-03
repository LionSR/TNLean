/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.UniformPostselection
import TNLean.Circuit.Gates.TwoSiteUniversality
import TNLean.Circuit.PairProductPowers
open QuantumCircuit

/-!
# Circuits for reflections about implemented images

If a unitary circuit implements an isometry on an initialized subspace,
reflection about its image is obtained by conjugating the initialized
subspace reflection by that circuit. Reversing the implementing circuit
costs the same number of gates. Repeating the resulting two-reflection
amplification step therefore has a gate count linear in the number of
rounds.

These are the circuit composition identities in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The existence of the
initialization reflection and of the recursively implementing circuit is
established separately.
-/

open Matrix

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- Unitary conjugation carries a subspace reflection to reflection about
the transported image. Source: the image reflection construction in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem subspaceReflection_image (U : Matrix n n ℂ) (E : Matrix n m ℂ)
    (hU : U ∈ unitaryGroup n ℂ) :
    subspaceReflection ((U * E) * (U * E)ᴴ) =
      U * subspaceReflection (E * Eᴴ) * Uᴴ := by
  have hu : U * Uᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using (mem_unitaryGroup_iff.mp hU)
  simp only [subspaceReflection, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hu, Matrix.mul_assoc]

end Matrix

namespace QuantumCircuit.IsPairProduct

variable {d n K L J : ℕ}

/-- Reflection about the implemented image costs one forward circuit, the
initialized-subspace reflection, and one inverse circuit. Source: the image
reflection construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem subspaceReflection_image {m : Type*} [Fintype m]
    (E : Matrix ((Fin n → Fin d)) m ℂ) {U : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ}
    (hU : IsPairProduct d n K U)
    (hR : IsPairProduct d n L (Matrix.subspaceReflection (E * Eᴴ))) :
    IsPairProduct d n (2 * K + L)
      (Matrix.subspaceReflection ((U * E) * (U * E)ᴴ)) := by
  rw [Matrix.subspaceReflection_image U E hU.mem_unitary]
  have h := (hU.mul hR).mul hU.star
  simpa only [Matrix.star_eq_conjTranspose, show K + L + K = 2 * K + L by omega] using h

/-- One amplification round includes both reflections and its prescribed
global phase. Source: the phase-exact amplification construction in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem postselectionAmplificationStep {m : Type*} [Fintype m]
    (hd : 0 < d) (hn : 2 ≤ n) (V : Matrix ((Fin n → Fin d)) m ℂ)
    (P : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)
    (hV : IsPairProduct d n K (Matrix.subspaceReflection (V * Vᴴ)))
    (hP : IsPairProduct d n L (Matrix.subspaceReflection P)) :
    IsPairProduct d n (2 * n + (K + L))
      (Matrix.postselectionAmplificationStep V P) := by
  have hphase := isPairProduct_smul_one (d := d) hd hn
    (μ := (-1 : ℂ)) (by simp)
  simpa only [Matrix.postselectionAmplificationStep, neg_one_smul, neg_mul,
    Matrix.one_mul] using hphase.mul (hV.mul hP)

end QuantumCircuit.IsPairProduct
