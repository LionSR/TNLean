/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.GridPropagation
import TNLean.MPS.AreaLaw.Huang.GridParameters

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

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- A physical nearest-neighbor chain has a uniform propagation approximation of
simultaneously bounded operator-Schmidt rank at every cut. Its actual block width is
`2 r + 2`, where `r` is the explicitly chosen radius; `chainPropagationRadius_width_le`
gives the time-linear, logarithmic-length and logarithmic-precision width bound.
Osborne, arXiv:quant-ph/0508031v2, equations (12)--(13); Huang, Lemma 19. -/
theorem exists_physical_chain_propagator_approximation {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (hHerm : ∀ i, (h i).IsHermitian)
    (hnorm : ∀ i, ‖h i‖ ≤ 1) {T epsilon : ℝ} (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    let r := chainPropagationRadius L T epsilon
    ∃ K : ℝ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (∀ t : ℝ, |t| ≤ T → ‖hermitianUnitaryPath (∑ i, h i) (-t) - K t‖ ≤ epsilon) ∧
      ∀ (t : ℝ) (cut : ℕ), operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (K t)) ≤
          q ^ (8 * r + 8) := by
  intro r
  let w := 2 * r + 2
  obtain ⟨K, hK⟩ := exists_chainGrid_propagator_approximation
    (w := w) (r := r) hq le_rfl h hs hHerm hnorm
  have hC := chainGridLRPrefactor_pos
  have hv : 0 ≤ chainGridLRVelocity := by unfold chainGridLRVelocity; positivity
  refine ⟨K, ?_, ?_⟩
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
    simpa only [hexponent] using (hK t).2 cut

/-- The propagation conclusion for the original positive-contraction interactions,
with Hermiticity and norm bounds derived internally. This is the physical normalization
in Huang, arXiv:1406.6355v6, Section 2 and Section 5.4, Lemma 19. -/
theorem exists_positive_chain_propagator_approximation {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    {T epsilon : ℝ} (hT : 0 ≤ T) (hepsilon : 0 < epsilon) :
    let r := chainPropagationRadius L T epsilon
    ∃ K : ℝ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (∀ t : ℝ, |t| ≤ T → ‖hermitianUnitaryPath (∑ i, h i) (-t) - K t‖ ≤ epsilon) ∧
      ∀ (t : ℝ) (cut : ℕ), operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (K t)) ≤
          q ^ (8 * r + 8) := by
  let : NeZero q := ⟨by omega⟩
  exact exists_physical_chain_propagator_approximation hq h hs
    (fun i ↦ (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian)
    (fun i ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i)) hT hepsilon

end TNLean.MPS.AreaLaw
