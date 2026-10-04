/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.UnitalCanonicalSpectrum
import TNLean.MPS.Periodic.StateVectorDecomposition
import QICLean.Channel.Peripheral.CyclicDecomposition.LetterShift

/-!
# PGVWC07 periodic decomposition from the printed canonical hypotheses

A one-block unital canonical tensor has cyclic peripheral spectrum, with the
period equal to its peripheral eigenvalue count. The corresponding orthogonal
projectors split the original state into explicit periodic component chains of
the original bond dimension. At lengths not divisible by the period, every
component and the original state vanish.

The proof uses the original unital transfer map. It neither assumes the
trace-preserving `IsPeriodic` normalization nor changes the physical state by
conjugating or reversing its coefficients. The faithful adjoint fixed matrix
may be diagonal, as in the source, but diagonality is unnecessary here.

## References

PGVWC07, arXiv:quant-ph/0608197, Theorem 5 (`Th:periodic`), lines 849–880,
with the one-block canonical conditions of Theorem 4 (`Th:TIcanonical`).
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

/-- **PGVWC07 Theorem 5 from the source hypotheses.** The unital canonical
conditions and peripheral eigenvalue count produce the explicit cyclic
projectors and the complete fixed-length periodic decomposition. Every
component has bond dimension `D` and repeats a `p`-site matrix pattern.
Non-divisible lengths give the zero vector, component by component.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 5 and its proof,
lines 849–880, with the canonical conditions of Theorem 4. -/
theorem pgvwc07_unital_stateVector_decomposition {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hU : ∑ i, A i * (A i)ᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hUnique : ∀ X, Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1)
    (p : ℕ) (hp : (peripheralEigenvalues (Kraus.transferMap A)).ncard = p) :
    ∃ hpPos : 0 < p,
      let _ : NeZero p := ⟨hpPos.ne'⟩
      ∃ Q : Fin p → MatrixAlg D,
        (∀ k, IsOrthogonalProjection (Q k)) ∧
        (∑ k, Q k = 1) ∧
        (∀ k, Q k ≠ 0) ∧
        (∀ k i, Q k * A i = A i * Q (k + 1)) ∧
        (∀ (N : ℕ) (u : Fin p) (j : Fin N) (i : Fin d),
          projectorComponentChain Q A u N j i =
            Q (u + j.val • (1 : Fin p)) * A i *
              Q (u + j.val • (1 : Fin p) + 1)) ∧
        (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
          mpv A σ = ∑ u : Fin p,
            MPSChainTensor.coeff (projectorComponentChain Q A u N) σ) ∧
        (∀ N, ¬p ∣ N → ∀ (u : Fin p) (σ : Fin N → Fin d),
          MPSChainTensor.coeff (projectorComponentChain Q A u N) σ = 0) ∧
        (∀ N, ¬p ∣ N → ∀ σ : Fin N → Fin d, mpv A σ = 0) := by
  obtain ⟨hpPos, γ, hγ, hper⟩ :=
    exists_peripheral_generator_of_unital_canonical A hU Λ hΛ hΛfix hUnique p hp
  let : NeZero p := ⟨hpPos.ne'⟩
  have hIrr := isIrreducible_transferMap_of_unital_canonical A hU Λ hΛ hΛfix hUnique
  obtain ⟨_, Q, _, _, _, hQproj, hQsum, _, hcyclic⟩ :=
    Kraus.exists_cyclic_decomposition_of_irreducible_schwarz
      A hU Λ hΛ
        (by simpa only [Kraus.adjointMap_apply, Kraus.transferMap_apply,
          Matrix.conjTranspose_conjTranspose] using hΛfix) hIrr hγ hper
  have hshift : ∀ k i, Q k * A i = A i * Q (k + 1) := by
    intro k i
    exact (Kraus.kraus_mul_cyclicProj A Q hQproj hQsum hcyclic i k).symm
  have hsum : ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
      mpv A σ = ∑ u : Fin p,
        MPSChainTensor.coeff (projectorComponentChain Q A u N) σ := by
    intro N hN
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    exact mpv_eq_sum_projectorComponentChain_coeff Q A hQproj hQsum hshift
  have hzero : ∀ N, ¬p ∣ N → ∀ (u : Fin p) (σ : Fin N → Fin d),
      MPSChainTensor.coeff (projectorComponentChain Q A u N) σ = 0 := by
    intro N hN
    exact projectorComponentChain_coeff_eq_zero_of_not_dvd Q A hQproj hQsum hshift hN
  refine ⟨hpPos, Q, hQproj, hQsum,
    cyclic_projection_ne_zero_of_sum_one hQsum hcyclic, hshift, ?_, hsum, hzero, ?_⟩
  · intro N u j i
    rfl
  · intro N hN σ
    have hNpos : 0 < N := by
      by_contra h
      exact hN (Nat.eq_zero_of_not_pos h ▸ dvd_zero p)
    rw [hsum N hNpos σ]
    exact Finset.sum_eq_zero fun u _ => hzero N hN u σ

end MPSTensor
