/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryMulVecInner
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Preparation.StateApproximationError
import TNLean.Circuit.LocalCircuit

/-!
# Circuit conversion through compatible coherent seeds

A sufficient version of the discussion remark of arXiv:2307.01696: two
normalized states approximated by local unitaries from compatible seeds are
converted by `U_B R U_A†`. All vectors and unitaries live on the same physical
ring. No measurement is inverted, and no ancillary output is discarded.
If auxiliary registers are used in an application, the endpoint equalities
must include their specified reset states in these full vectors.

**Scope restriction (compatible seeds):** equality of parent groundspaces
alone does not identify the normalized periodic vector or its sector weights.
The seed compatibility required here is explicit; the informal general phase
claim remains unresolved. See
`docs/paper-gaps/mswc24_same_phase_compatible_seed.tex`.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit

namespace MPSPreparation

variable {d N : ℕ} [NeZero N]

/-- Conversion through compatible seeds, with additive circuit depths and
explicit approximation errors. Source context: arXiv:2307.01696, discussion
remark and the coherent unitary stage of "Long-range MPS using measurements".
The compatibility equation concerns full normalized vectors, not reduced
states or measurement outcomes. -/
theorem exists_isLocalCircuitOfDepth_of_compatible_seeds
    {a b χA χB a' b' : MPVSpace d N}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hχA : ‖χA‖ = 1)
    {UA UB R : Matrix (Cfg d N) (Cfg d N) ℂ} {TA TB TR : ℕ}
    (hUA : IsLocalCircuitOfDepth UA TA) (hUB : IsLocalCircuitOfDepth UB TB)
    (hR : IsLocalCircuitOfDepth R TR)
    (hA : (fun s => a' s) = UA *ᵥ fun s => χA s)
    (hB : (fun s => b' s) = UB *ᵥ fun s => χB s)
    (hseed : (fun s => χB s) = R *ᵥ fun s => χA s)
    {εA εB : ℝ} (herrA : 1 - ‖⟪a', a⟫_ℂ‖ ≤ εA)
    (herrB : 1 - ‖⟪b', b⟫_ℂ‖ ≤ εB) :
    ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (ψ : MPVSpace d N),
      U = UB * R * star UA ∧ IsLocalCircuitOfDepth U (TA + TR + TB) ∧
      (fun s => ψ s) = U *ᵥ (fun s => a s) ∧
      1 - ‖⟪ψ, b⟫_ℂ‖ ≤ 2 * (εA + εB) := by
  let U := UB * R * star UA
  have hU : IsLocalCircuitOfDepth U (TA + TR + TB) := by
    simpa only [U, Matrix.mul_assoc] using (hUA.star.mul hR).mul hUB
  have hUa : U *ᵥ (fun s => a' s) = fun s => b' s := by
    change (UB * R * star UA) *ᵥ (fun s => a' s) = fun s => b' s
    rw [hA, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Unitary.star_mul_self_of_mem hUA.mem_unitary, Matrix.mul_one,
      ← mulVec_mulVec, ← hseed, ← hB]
  let ψ : MPVSpace d N := WithLp.toLp 2 (U *ᵥ fun s => a s)
  have hψ : (fun s => ψ s) = U *ᵥ fun s => a s := rfl
  have hψn : ‖ψ‖ = 1 := (Matrix.norm_eq_of_mulVec_eq hU.mem_unitary hψ).trans ha
  have hχB : ‖χB‖ = 1 := (Matrix.norm_eq_of_mulVec_eq hR.mem_unitary hseed).trans hχA
  have hb'n : ‖b'‖ = 1 := (Matrix.norm_eq_of_mulVec_eq hUB.mem_unitary hB).trans hχB
  have hi : ⟪ψ, b'⟫_ℂ = ⟪a, a'⟫_ℂ :=
    Matrix.inner_eq_of_mulVec_eq hU.mem_unitary hψ hUa.symm
  have ht := one_sub_norm_inner_le_two_mul_add hψn hb'n hb
  rw [hi, norm_inner_symm a a'] at ht
  exact ⟨U, ψ, rfl, hU, hψ, by linarith⟩

/-- The exact common-seed specialization, requiring no matching gate.
Source context: arXiv:2307.01696, discussion remark, with a common coherent
GHZ seed supplied to both unitary preparation stages. -/
theorem exists_isLocalCircuitOfDepth_of_common_seed
    {a b χ a' b' : MPVSpace d N}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hχ : ‖χ‖ = 1)
    {UA UB : Matrix (Cfg d N) (Cfg d N) ℂ} {TA TB : ℕ}
    (hUA : IsLocalCircuitOfDepth UA TA) (hUB : IsLocalCircuitOfDepth UB TB)
    (hA : (fun s => a' s) = UA *ᵥ fun s => χ s)
    (hB : (fun s => b' s) = UB *ᵥ fun s => χ s)
    {εA εB : ℝ} (herrA : 1 - ‖⟪a', a⟫_ℂ‖ ≤ εA)
    (herrB : 1 - ‖⟪b', b⟫_ℂ‖ ≤ εB) :
    ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (ψ : MPVSpace d N),
      U = UB * star UA ∧ IsLocalCircuitOfDepth U (TA + TB) ∧
      (fun s => ψ s) = U *ᵥ (fun s => a s) ∧
      1 - ‖⟪ψ, b⟫_ℂ‖ ≤ 2 * (εA + εB) := by
  have hI : IsLocalCircuitOfDepth (1 : Matrix (Cfg d N) (Cfg d N) ℂ) 0 :=
    ⟨[], rfl, rfl⟩
  simpa only [Matrix.mul_one, Nat.add_zero] using
    exists_isLocalCircuitOfDepth_of_compatible_seeds ha hb hχ hUA hUB hI hA hB
      (by simp only [Matrix.one_mulVec]) herrA herrB

/-- Uniform logarithmic-depth conversion from compatible coherent seed
approximations. The constants precede both length and accuracy; circuits and
seeds may depend on them. Source context: arXiv:2307.01696, discussion remark,
with the explicit sufficient seed-compatibility restriction of this module. -/
theorem exists_isLocalCircuitOfDepth_le_log_of_compatible_seeds
    (a b : ∀ N : ℕ, MPVSpace d N) (cA cB cR : ℝ) (N₀ : ℕ)
    (hprepare : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (χA χB a' b' : MPVSpace d N)
        (UA UB R : Matrix (Cfg d N) (Cfg d N) ℂ) (TA TB TR : ℕ),
        ‖a N‖ = 1 ∧ ‖b N‖ = 1 ∧ ‖χA‖ = 1 ∧
        IsLocalCircuitOfDepth UA TA ∧ IsLocalCircuitOfDepth UB TB ∧
        IsLocalCircuitOfDepth R TR ∧
        (TA : ℝ) ≤ cA * Real.log (N / ε) ∧
        (TB : ℝ) ≤ cB * Real.log (N / ε) ∧
        (TR : ℝ) ≤ cR * Real.log (N / ε) ∧
        (fun s => a' s) = UA *ᵥ (fun s => χA s) ∧
        (fun s => b' s) = UB *ᵥ (fun s => χB s) ∧
        (fun s => χB s) = R *ᵥ (fun s => χA s) ∧
        1 - ‖⟪a', a N⟫_ℂ‖ ≤ ε / 4 ∧
        1 - ‖⟪b', b N⟫_ℂ‖ ≤ ε / 4) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ) (ψ : MPVSpace d N),
        IsLocalCircuitOfDepth U T ∧
        (T : ℝ) ≤ (cA + cB + cR) * Real.log (N / ε) ∧
        (fun s => ψ s) = U *ᵥ (fun s => a N s) ∧
        1 - ‖⟪ψ, b N⟫_ℂ‖ ≤ ε := by
  intro ε hε hε1 N _ hN
  obtain ⟨χA, χB, a', b', UA, UB, R, TA, TB, TR,
    ha, hb, hχA, hUA, hUB, hR, hTA, hTB, hTR, hA, hB, hseed, heA, heB⟩ :=
    hprepare ε hε hε1 N hN
  obtain ⟨U, ψ, -, hU, hψ, he⟩ := exists_isLocalCircuitOfDepth_of_compatible_seeds
    ha hb hχA hUA hUB hR hA hB hseed heA heB
  refine ⟨U, TA + TR + TB, ψ, hU, ?_, hψ, by linarith⟩
  push_cast
  nlinarith

end MPSPreparation
