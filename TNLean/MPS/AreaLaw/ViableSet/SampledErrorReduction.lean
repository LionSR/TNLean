/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledCutDecomposition

/-!
# Error reduction by the sampled power projector

Sampling and deterministic error reduction give one family of left factors at each
cut. With `ℓ` words and multiplicity bound `κ`, there are at most `ℓ * q^(2κ)`
factors, each with operator Schmidt rank at most `q^(2κ)` at every internal left cut.
These factors are chosen before the input viable family.

**Local fix (witness normalization):** approximation error `δ / 4` yields viability
error `δ`, as recorded in `docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.
The two approximations are each made at precision `δ / 8`.

The normalization and sample count depend explicitly on the specified ground energy.
This theorem does not assert that these counts have polynomial growth uniformly over
unbounded ground-energy-to-gap ratios.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claim `c:errorreduction`, lines 580–592, and Corollary `c:agsp`, lines 626–649.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

/-- The sampled projector supplies both the decomposition and its simultaneous left
rank bounds for deterministic error reduction. LVV13, Claim `c:errorreduction`,
lines 580–592, with the documented witness-normalization correction. -/
theorem exists_sampled_errorReduction {L q : ℕ} [NeZero L] (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let η := δ / 8
    let m := ⌈((L - E₀) / Δ) * Real.log (1 / η)⌉₊
    let ℓ := sampledProjectorWordCount q L E₀ η m
    let D := q ^ (2 * sampledProjectorLetterBound L ℓ m)
    ∃ I : Fin ℓ → Fin m → Fin L,
      ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 4 ∧
      ∀ i : ℕ, i ≤ L → ∃ (N : ℕ) (A : Fin N → LeftBlockMatrix L q i)
        (B : Fin N → RightBlockMatrix L q i),
        N ≤ ℓ * D ∧ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i)
          (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B j ∧
        (∀ j k, 0 < k → k < i → operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
            ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D) ∧
        ∀ (s b : ℕ) (S : Finset (LeftBlockVector L q i)), IsViableMPS Γ s b (1 / 2) S →
          IsViableMPS Γ (ℓ * D * s) (D * max 1 b) δ
            (errorReductionSet Finset.univ A S) := by
  classical
  intro η m ℓ D
  obtain ⟨I, hpower, hsample, hcount, _⟩ :=
    exists_sampledProjector h hs h0 h1 hgs hΔ (div_pos hδ (by norm_num)) m (Nat.le_ceil _)
  have hproj : ‖sampledProjector h E₀ I -
      vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 4 := by
    calc
      _ ≤ ‖sampledProjector h E₀ I - powerProjector (∑ j, h j) L E₀ m‖ +
          ‖powerProjector (∑ j, h j) L E₀ m -
            vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < η + η := add_lt_add_of_lt_of_le hsample hpower
      _ = δ / 4 := by dsimp only [η]; ring
  refine ⟨I, hproj, fun i hi ↦ ?_⟩
  obtain ⟨N, A, B, hN, hdec, hleft⟩ := exists_sampledProjector_cutDecomposition hi h E₀ I
    (fun t k ↦ operatorSchmidtRank_cutOperator_bondComplementWord_le_all hq h hs (I t)
      (hcount t) k)
  refine ⟨N, A, B, hN, hdec, hleft, fun s b S hS ↦ ?_⟩
  have hout := IsViableMPS.errorReduction_of_norm_sub_groundProjection_le
    (J := Finset.univ) hi hS hgs.1 hdec
    (fun j _ k hk0 hki ↦ hleft j k hk0 hki) hproj.le (by linarith only [hδ1])
  have hout' : IsViableMPS Γ (N * s) (D * max 1 b) δ
      (errorReductionSet Finset.univ A S) := by
    simpa only [Finset.card_univ, Fintype.card_fin, show 4 * (δ / 4) = δ by ring] using hout
  exact ⟨hout'.1.trans (Nat.mul_le_mul_right s hN), hout'.2⟩

end TNLean.MPS.AreaLaw
