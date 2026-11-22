/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.GaussianFilter.GridPropagation
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.GaussianFilter.GridParameters

/-!
# Uniform physical propagation at prescribed accuracy

Original nearest-neighbor interaction terms determine a single family of operators
approximating their full unitary evolution on a prescribed time interval. The integer
buffer radius is chosen explicitly from the cutoff, chain length and precision. Every
member of the same family has the simultaneous operator-Schmidt bond bound at all cuts.
Neither a partition nor any approximate propagator is supplied as input.

Source: Osborne, arXiv:quant-ph/0508031v2, Figure 2 and equations (12)--(13), and Huang,
arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- **The physical chain propagator.** The grid propagator at the Lieb--Robinson radius of
the time window and accuracy, with grid width `2r + 2`. Huang, arXiv:1406.6355v6,
Section 5.4, Lemma 19. -/
noncomputable def physicalChainPropagator {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (hHerm : ∀ i, (Φ.term i).IsHermitian) (T epsilon : ℝ) (t : ℝ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  chainGridPropagator (w := 2 * chainPropagationRadius L T epsilon + 2) (by omega)
    (chainPropagationRadius L T epsilon) Φ hHerm t

/-- The physical chain propagator approximates the evolution within the time window at
the prescribed accuracy, with simultaneous cut-rank bounds. Huang, arXiv:1406.6355v6,
Section 5.4, Lemma 19. -/
theorem physicalChainPropagator_spec {L q : ℕ} (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hnorm : ∀ i, ‖Φ.term i‖ ≤ 1) {T epsilon : ℝ} (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    let r := chainPropagationRadius L T epsilon
    let K := physicalChainPropagator Φ hHerm T epsilon
    (∀ t : ℝ, |t| ≤ T → ‖hermitianUnitaryPath Φ.hamiltonian (-t) - K t‖ ≤ epsilon) ∧
      ∀ (t : ℝ) (cut : ℕ), operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L cut) (K t)) ≤
          q ^ (8 * r + 8) := by
  intro r K
  let w := 2 * r + 2
  have hK (t : ℝ) := chainGridPropagator_spec (w := w) (r := r) hq le_rfl Φ hHerm hnorm t
  have hC := chainGridLRPrefactor_pos
  have hv : 0 ≤ chainGridLRVelocity := by unfold chainGridLRVelocity; positivity
  refine ⟨?_, ?_⟩
  · intro t ht
    have hexp : Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) ≤
        Real.exp (chainGridLRVelocity * T - (r : ℝ) / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left ht hv])
    have hcoefficient : 0 ≤ (((L - 1) / w : ℕ) : ℝ) * chainGridLRPrefactor := by positivity
    calc
      _ ≤ (((L - 1) / w : ℕ) : ℝ) * chainGridLRPrefactor *
          Real.exp (chainGridLRVelocity * |t| - (r : ℝ) / 2) * |t| := (hK t).1
      _ ≤ (((L - 1) / w : ℕ) : ℝ) * chainGridLRPrefactor *
          Real.exp (chainGridLRVelocity * T - (r : ℝ) / 2) * T :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp hcoefficient) ht
          (abs_nonneg t) (by positivity)
      _ ≤ epsilon := chainPropagationRadius_error_le L ((L - 1) / w)
        ((Nat.div_le_self (L - 1) w).trans (Nat.sub_le L 1)) hT hepsilon
  · intro t cut
    have hexponent : 2 * (w + (2 * r + 2)) = 8 * r + 8 := by dsimp only [w]; ring
    simpa only [K, physicalChainPropagator, hexponent] using (hK t).2 cut

/-- The physical chain propagator approximates the evolution within the time window at
the prescribed accuracy, with simultaneous cut-rank bounds: the existence form of
`physicalChainPropagator_spec`. Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19. -/
theorem exists_physical_chain_propagator_approximation {L q : ℕ} (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hnorm : ∀ i, ‖Φ.term i‖ ≤ 1) {T epsilon : ℝ} (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    let r := chainPropagationRadius L T epsilon
    ∃ K : ℝ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (∀ t : ℝ, |t| ≤ T → ‖hermitianUnitaryPath Φ.hamiltonian (-t) - K t‖ ≤ epsilon) ∧
      ∀ (t : ℝ) (cut : ℕ), operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L cut) (K t)) ≤
          q ^ (8 * r + 8) :=
  ⟨physicalChainPropagator Φ hHerm T epsilon,
    physicalChainPropagator_spec hq Φ hHerm hnorm hT hepsilon⟩

/-- **The propagator of a positive chain**: the physical chain propagator, with
Hermiticity of the terms derived from positivity. Huang, arXiv:1406.6355v6, Section 2
and Section 5.4, Lemma 19. -/
noncomputable def positiveChainPropagator {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q) (h0 : ∀ i, 0 ≤ Φ.term i)
    (T epsilon : ℝ) (t : ℝ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  physicalChainPropagator Φ (fun i ↦ (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian)
    T epsilon t

/-- The propagation conclusion for the original positive-contraction interactions,
with Hermiticity and norm bounds derived internally. This is the physical normalization
in Huang, arXiv:1406.6355v6, Section 2 and Section 5.4, Lemma 19. -/
theorem positiveChainPropagator_spec {L q : ℕ} (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    {T epsilon : ℝ} (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    let r := chainPropagationRadius L T epsilon
    let K := positiveChainPropagator Φ h0 T epsilon
    (∀ t : ℝ, |t| ≤ T → ‖hermitianUnitaryPath Φ.hamiltonian (-t) - K t‖ ≤ epsilon) ∧
      ∀ (t : ℝ) (cut : ℕ), operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L cut) (K t)) ≤
          q ^ (8 * r + 8) :=
  physicalChainPropagator_spec hq Φ
    (fun i ↦ (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian)
    (fun i ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i)) hT hepsilon

/-- The propagation conclusion for the original positive-contraction interactions: the
existence form of `positiveChainPropagator_spec`. Huang, arXiv:1406.6355v6, Section 2
and Section 5.4, Lemma 19. -/
theorem exists_positive_chain_propagator_approximation {L q : ℕ} (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    {T epsilon : ℝ} (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    let r := chainPropagationRadius L T epsilon
    ∃ K : ℝ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (∀ t : ℝ, |t| ≤ T → ‖hermitianUnitaryPath Φ.hamiltonian (-t) - K t‖ ≤ epsilon) ∧
      ∀ (t : ℝ) (cut : ℕ), operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L cut) (K t)) ≤
          q ^ (8 * r + 8) :=
  ⟨positiveChainPropagator Φ h0 T epsilon,
    positiveChainPropagator_spec hq Φ h0 h1 hT hepsilon⟩

end TNLean.MPS.AreaLaw
