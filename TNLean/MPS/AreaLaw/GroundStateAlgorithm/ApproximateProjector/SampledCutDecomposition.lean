/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ApproximateProjector.CutDecomposition
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ApproximateProjector.SampledProjector
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ApproximateProjector.ErrorReduction
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Simultaneous bond bounds for the sampled left factors

Decompose each sampled word separately. If every word has operator Schmidt rank at
most `D` at every cut, its left factors can be chosen with the same bound at all
internal cuts. The sampled sum therefore has at most `ℓ * D` product terms, while
each left factor still has bond bound `D`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claim `c:errorreduction`, decomposition `e:decomp`, lines 584–591.

## Error reduction by the sampled power projector

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

section

open ManyBody (interval)

open Matrix
open scoped BigOperators Kronecker

namespace TNLean.MPS.AreaLaw

private theorem operatorSchmidtRank_cutOperator_endpoint_le_one {L q k : ℕ}
    (hk : k = 0 ∨ L ≤ k) (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (leftBlock L k) K) ≤ 1 := by
  classical
  have hs : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) K Finset.univ := by
    constructor
    · simp
    · intro σ τ σ' τ' hσ hτ _ _
      have hσ' : σ = σ' := funext fun v ↦ hσ v (Finset.mem_univ v)
      have hτ' : τ = τ' := funext fun v ↦ hτ v (Finset.mem_univ v)
      rw [hσ', hτ']
  apply hs.operatorSchmidtRank_cutOperator_le_one
  rcases hk with rfl | hk
  · right
    simp [leftBlock]
  · left
    intro v _
    exact mem_leftBlock.mpr (lt_of_lt_of_le v.isLt hk)

/-- Multiplicity bounds give word-rank bounds at every cut, including the two
endpoints. LVV13, `algo53.tex`, lines 584–591 and 626–649. -/
theorem operatorSchmidtRank_cutOperator_bondComplementWord_le_all {L q m κ : ℕ}
    (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (I : Fin m → Fin L)
    (hI : ∀ j, letterCount I j ≤ κ) (k : ℕ) :
    operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (leftBlock L k) (bondComplementWord Φ I)) ≤ q ^ (2 * κ) := by
  by_cases hk0 : k = 0
  · exact (operatorSchmidtRank_cutOperator_endpoint_le_one (Or.inl hk0) _).trans
      (Nat.one_le_pow _ _ hq)
  by_cases hkL : k < L
  · let b : Fin (L - 1) := ⟨k - 1, by omega⟩
    have hb : b.val + 1 = k := by dsimp [b]; omega
    rw [← hb]
    apply operatorSchmidtRank_cutOperator_bondComplementWord_le Φ b I
    simpa only [letterCount, Fin.ext_iff] using hI ⟨b.val, by omega⟩
  · exact (operatorSchmidtRank_cutOperator_endpoint_le_one (Or.inr (by omega)) _).trans
      (Nat.one_le_pow _ _ hq)

/-- Decompose each sampled word at a fixed cut, retaining its rank bound at all
internal left cuts. LVV13, `algo53.tex`, decomposition `e:decomp`, lines 584–591. -/
theorem exists_sampledProjector_cutDecomposition {L q ℓ m i D : ℕ}
    (hi : i ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (E₀ : ℝ) (I : Fin ℓ → Fin m → Fin L)
    (hrank : ∀ t k, operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L k)
        (bondComplementWord Φ (I t))) ≤ D) :
    ∃ (N : ℕ) (A : Fin N → LeftBlockMatrix L q i)
      (B : Fin N → RightBlockMatrix L q i),
      N ≤ ℓ * D ∧ ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L i)
        (sampledProjector Φ E₀ I) = ∑ j, A j ⊗ₖ B j ∧
      ∀ j k, 0 < k → k < i → operatorSchmidtRank
        (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock i k)
          ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D := by
  classical
  choose N A B hN hdec hleft using fun t ↦
    exists_cutDecomposition_of_operatorSchmidtRank_le hi (bondComplementWord Φ (I t))
      (hrank t)
  let J := (t : Fin ℓ) × Fin (N t)
  let e := (Fintype.equivFin J).symm
  let c : ℂ := (powerNormalization L E₀ ^ m * (ℓ : ℝ)⁻¹ : ℝ)
  refine ⟨Fintype.card J, fun j ↦ c • A (e j).1 (e j).2,
    fun j ↦ B (e j).1 (e j).2, ?_, ?_, ?_⟩
  · change Fintype.card ((t : Fin ℓ) × Fin (N t)) ≤ _
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun t _ ↦ hN t)
  · rw [Equiv.sum_comp e (fun j : J ↦ (c • A j.1 j.2) ⊗ₖ B j.1 j.2),
      Fintype.sum_sigma]
    simp only [Matrix.smul_kronecker, ← Finset.smul_sum, ← hdec]
    ext x y
    simp [sampledProjector, ManyBody.cutOperator, reindex_apply, submatrix_apply,
      Matrix.sum_apply, Matrix.smul_apply, c, mul_assoc]
  · intro j k hk0 hki
    have heq : ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock i k)
        ((c • A (e j).1 (e j).2).submatrix leftConfigOfFin leftConfigOfFin) =
        c • ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock i k)
          ((A (e j).1 (e j).2).submatrix leftConfigOfFin leftConfigOfFin) := rfl
    rw [heq]
    exact (operatorSchmidtRank_smul_le _ _).trans (hleft _ _ k hk0 hki)

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- The sampled projector supplies both the decomposition and its simultaneous left
rank bounds for deterministic error reduction. LVV13, Claim `c:errorreduction`,
lines 580–592, with the documented witness-normalization correction. -/
theorem exists_sampled_errorReduction {L q : ℕ} [NeZero L] (hq : 1 ≤ q)
    (Φ : ManyBody.BondInteraction L q) (h0 : ∀ i, (Φ.term i).PosSemidef) (h1 : ∀ i, Φ.term i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Γ‖ = 1) (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (hspan : groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Γ}) (hΔ : 0 < Δ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let η := δ / 8
    let m := ⌈((L - E₀) / Δ) * Real.log (1 / η)⌉₊
    let ℓ := sampledProjectorWordCount q L E₀ η m
    let D := q ^ (2 * sampledProjectorLetterBound L ℓ m)
    ∃ I : Fin ℓ → Fin m → Fin L,
      ‖sampledProjector Φ E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 4 ∧
      ∀ i : ℕ, i ≤ L → ∃ (N : ℕ) (A : Fin N → LeftBlockMatrix L q i)
        (B : Fin N → RightBlockMatrix L q i),
        N ≤ ℓ * D ∧ ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L i)
          (sampledProjector Φ E₀ I) = ∑ j, A j ⊗ₖ B j ∧
        (∀ j k, 0 < k → k < i → operatorSchmidtRank
          (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock i k)
            ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D) ∧
        ∀ (s b : ℕ) (S : Finset (LeftBlockVector L q i)), IsViableMPS Γ s b (1 / 2) S →
          IsViableMPS Γ (ℓ * D * s) (D * max 1 b) δ
            (errorReductionSet Finset.univ A S) := by
  classical
  intro η m ℓ D
  obtain ⟨I, hpower, hsample, hcount, _⟩ :=
    exists_sampledProjector Φ h0 h1 hΩ hgap hspan hΔ (div_pos hδ (by norm_num)) m (Nat.le_ceil _)
  have hproj : ‖sampledProjector Φ E₀ I -
      vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 4 := by
    calc
      _ ≤ ‖sampledProjector Φ E₀ I - powerProjector Φ.hamiltonian L E₀ m‖ +
          ‖powerProjector Φ.hamiltonian L E₀ m -
            vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < η + η := add_lt_add_of_lt_of_le hsample hpower
      _ = δ / 4 := by dsimp only [η]; ring
  refine ⟨I, hproj, fun i hi ↦ ?_⟩
  obtain ⟨N, A, B, hN, hdec, hleft⟩ := exists_sampledProjector_cutDecomposition hi Φ E₀ I
    (fun t k ↦ operatorSchmidtRank_cutOperator_bondComplementWord_le_all hq Φ (I t)
      (hcount t) k)
  refine ⟨N, A, B, hN, hdec, hleft, fun s b S hS ↦ ?_⟩
  have hout := IsViableMPS.errorReduction_of_norm_sub_groundProjection_le
    (J := Finset.univ) hi hS hΩ hdec
    (fun j _ k hk0 hki ↦ hleft j k hk0 hki) hproj.le (by linarith only [hδ1])
  have hout' : IsViableMPS Γ (N * s) (D * max 1 b) δ
      (errorReductionSet Finset.univ A S) := by
    simpa only [Finset.card_univ, Fintype.card_fin, show 4 * (δ / 4) = δ by ring] using hout
  exact ⟨hout'.1.trans (Nat.mul_le_mul_right s hN), hout'.2⟩

end TNLean.MPS.AreaLaw

end
