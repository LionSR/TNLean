/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LocalRootChannels

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix TNLean.PEPS.AreaLaw
open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLeanTest.LocalRootChannels

variable {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
  [Fintype Aux] [DecidableEq Aux]

-- Both endpoint contractions give the identity channel on arbitrary observables.
example (K : Finset ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannel K 0 B = B := by
  have hzero : siteExpectation q K (0 : Matrix (ι → Fin q) (ι → Fin q) ℂ) = 0 := by
    simpa only [siteExpectationLM_apply] using (siteExpectationLM q K).map_zero
  simp [localRootChannel, spectatorRootChannel, rootChannel, hzero,
    Matrix.one_kronecker_one]

example (K : Finset ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannel K 1 B = B := by
  simp [localRootChannel, spectatorRootChannel, rootChannel, siteExpectation_one,
    Matrix.one_kronecker_one]

-- Consecutive equal regions have literally zero shell, without positivity assumptions.
example (K : Finset ι) (k : Matrix (ι → Fin q) (ι → Fin q) ℂ) (l : ℕ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannelShell (fun _ => K) k (l + 1) B = 0 := by
  simp [localRootChannelShell]

-- The public contraction bound permits an empty spectator index type.
example (K : Finset ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Fin 0) ((ι → Fin q) × Fin 0) ℂ) :
    ‖localRootChannel K k B‖ ≤ ‖B‖ :=
  norm_localRootChannel_le K hk₀ hk₁ B

-- Spectator-only operators are fixed with no Hermiticity restriction on C.
theorem fixes_spectator (K : Finset ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (C : Matrix Aux Aux ℂ) :
    localRootChannel K k ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C) = 1 ⊗ₖ C := by
  apply localRootChannel_eq_self_of_forall_commute K hk₀ hk₁
  intro A _
  change (A ⊗ₖ 1) * (1 ⊗ₖ C) = (1 ⊗ₖ C) * (A ⊗ₖ 1)
  simp only [← Matrix.mul_kronecker_mul, mul_one, one_mul]

-- This upper-triangular spectator matrix is not Hermitian.
example : ¬(!![(0 : ℂ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  intro h
  have h01 := congrFun (congrFun h.eq 0) 1
  norm_num [Matrix.conjTranspose_apply] at h01

example (K : Finset ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) :
    localRootChannel K k
        ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ !![(0 : ℂ), 1; 0, 0]) =
      1 ⊗ₖ !![(0 : ℂ), 1; 0, 0] :=
  fixes_spectator K hk₀ hk₁ _

-- A genuinely zero expectation error gives equality of the full and local channels.
example (K : Finset ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (hK : k ∈ supportedOperators q (K : Set ι))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannel k B = localRootChannel K k B := by
  have herror : ‖k - siteExpectation q K k‖ ≤ 0 := by
    simp [siteExpectation_of_mem_supportedOperators K hK]
  have h := norm_spectatorRootChannel_sub_localRootChannel_le K hk₀ hk₁ herror B
  have hz : ‖spectatorRootChannel k B - localRootChannel K k B‖ = 0 :=
    le_antisymm (by simpa using h) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

-- The covariance API accepts every operator outside K, without a unitary hypothesis.
example (K : Finset ι) {k U : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (hU : U ∈ supportedOperators q ((K : Set ι)ᶜ))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖(U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * localRootChannel K k B -
      localRootChannel K k B * (U ⊗ₖ 1)‖ ≤ ‖(U ⊗ₖ 1) * B - B * (U ⊗ₖ 1)‖ := by
  rw [localRootChannel_commutator K hk₀ hk₁ hU]
  exact norm_localRootChannel_le K hk₀ hk₁ _

end TNLeanTest.LocalRootChannels
