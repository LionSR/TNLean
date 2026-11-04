/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.CutDecomposition
import TNLean.MPS.AreaLaw.ViableSet.SampledProjector
import TNLean.MPS.AreaLaw.ViableSet.ErrorReduction

/-!
# The left factors of the sampled projector

The sampled approximate ground-state projector `K = C^m ℓ⁻¹ ∑_t P_{I_t}` is a scaled sum of
the words `P_{I_t}`. Its left factors at a cut are the chosen left factors of the cut
decomposition of each word, scaled by `C^m / ℓ`: the family `sampledFactors`. Their number
is at most `ℓ D` and their operator-Schmidt ranks at the internal cuts are at most `D`
whenever every word has rank at most `D` at every cut, and the error-reduced family
`{A s : A ∈ sampledFactors, s ∈ S}` is viable whenever `S` is half-viable and `K` is within
`η < 1/2` of the ground projection. This is the sampled error-reduction step of Claim
`c:errorreduction` with its output named.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, Definition `d:sagsp`, line 611, and the
proof of Claim `c:errorreduction`, lines 584--592.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The scale `C^m / ℓ` of every word in the sampled projector. -/
noncomputable def sampledScale (L : ℕ) (E₀ : ℝ) (ℓ m : ℕ) : ℝ :=
  powerNormalization L E₀ ^ m * (ℓ : ℝ)⁻¹

/-- The sampled projector is the sum of the scaled words. -/
theorem sampledProjector_eq_sum_smul
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) :
    sampledProjector h E₀ I = ∑ t, sampledScale L E₀ ℓ m • bondComplementWord h (I t) := by
  simp only [sampledProjector, sampledScale, Finset.smul_sum, smul_smul]

/-- The chosen left factor of the word `I t` at the cut after `i` sites, scaled by
`C^m / ℓ`. -/
noncomputable def sampledLeftFactor
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (i : ℕ) (t : Fin ℓ)
    (j : Fin (operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L i) (bondComplementWord h (I t))))) : LeftBlockMatrix L q i :=
  sampledScale L E₀ ℓ m • cutLeftFactor (bondComplementWord h (I t)) j

/-- **The left factors of the sampled projector** at the cut after `i` sites: the scaled
chosen left factors of all its words. LVV13, `algo53.tex`, line 611 and lines 584--592. -/
noncomputable def sampledFactors
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (i : ℕ) : Finset (LeftBlockMatrix L q i) :=
  open Classical in Finset.univ.biUnion fun t ↦ Finset.univ.image (sampledLeftFactor h E₀ I i t)

/-- The sampled projector in cut coordinates is the sum of the scaled chosen decompositions
of its words. -/
theorem cutOperator_sampledProjector_eq_sum
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (i : ℕ) :
    Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) (sampledProjector h E₀ I) =
      ∑ p : (t : Fin ℓ) × Fin (operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
        (leftBlock L i) (bondComplementWord h (I t)))),
        sampledLeftFactor h E₀ I i p.1 p.2 ⊗ₖ
          cutRightFactor (bondComplementWord h (I p.1)) p.2 := by
  rw [Fintype.sum_sigma]
  have hlin : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i)
      (sampledProjector h E₀ I) = ∑ t, sampledScale L E₀ ℓ m •
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i)
          (bondComplementWord h (I t)) := by
    rw [sampledProjector_eq_sum_smul]
    ext a b
    simp [Matrix.sum_apply]
  rw [hlin]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hdec := congrArg (fun M ↦ sampledScale L E₀ ℓ m • M)
    (cutOperator_eq_sum_cutLeftFactor_kronecker (i := i) (bondComplementWord h (I t)))
  rw [hdec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [sampledLeftFactor, Matrix.smul_kronecker]

/-- The sampled factors number at most `ℓ D` when every word has rank at most `D` at the
cut. -/
theorem card_sampledFactors_le
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (i : ℕ) {D : ℕ}
    (hrank : ∀ t, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L i) (bondComplementWord h (I t))) ≤ D) :
    (sampledFactors h E₀ I i).card ≤ ℓ * D := by
  classical
  calc
    (sampledFactors h E₀ I i).card
        ≤ ∑ t : Fin ℓ, (Finset.univ.image (sampledLeftFactor h E₀ I i t)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _t : Fin ℓ, D := Finset.sum_le_sum fun t _ ↦
          Finset.card_image_le.trans (by
            rw [Finset.card_univ, Fintype.card_fin]
            exact hrank t)
    _ = ℓ * D := by simp

/-- Every sampled factor has operator-Schmidt rank at most `D` at every internal cut when
every word has rank at most `D` at every cut. -/
theorem operatorSchmidtRank_of_mem_sampledFactors {i : ℕ} (hi : i ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) {D : ℕ}
    (hrank : ∀ t k, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) (bondComplementWord h (I t))) ≤ D)
    {A : LeftBlockMatrix L q i} (hA : A ∈ sampledFactors h E₀ I i) (k : ℕ) (hki : k < i) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
      (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ D := by
  classical
  simp only [sampledFactors, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image] at hA
  obtain ⟨t, j, -, rfl⟩ := hA
  have hbase := operatorSchmidtRank_cutLeftFactor_le hi (bondComplementWord h (I t)) (hrank t)
    j k hki
  have hsmul : Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
      ((sampledLeftFactor h E₀ I i t j).submatrix leftConfigOfFin leftConfigOfFin) =
      sampledScale L E₀ ℓ m • Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        ((cutLeftFactor (bondComplementWord h (I t)) j).submatrix leftConfigOfFin
          leftConfigOfFin) := by
    ext a b
    simp [sampledLeftFactor]
  rw [hsmul]
  have hcoe : sampledScale L E₀ ℓ m • Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
      ((cutLeftFactor (bondComplementWord h (I t)) j).submatrix leftConfigOfFin leftConfigOfFin) =
      ((sampledScale L E₀ ℓ m : ℝ) : ℂ) • Entropy.cutOperator (n := fun _ : Fin i ↦ q)
        (leftBlock i k) ((cutLeftFactor (bondComplementWord h (I t)) j).submatrix leftConfigOfFin
          leftConfigOfFin) := by
    ext a b
    simp [Complex.real_smul]
  rw [hcoe]
  exact (operatorSchmidtRank_smul_le _ _).trans hbase

/-- The error-reduced family of the sampled factors is the error-reduced family of the
indexed scaled factors. -/
theorem errorReductionSet_sampledFactors
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) {i : ℕ} (S : Finset (LeftBlockVector L q i)) :
    errorReductionSet (sampledFactors h E₀ I i) id S =
      errorReductionSet (Finset.univ : Finset ((t : Fin ℓ) × Fin (operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i)
          (bondComplementWord h (I t))))))
        (fun p ↦ sampledLeftFactor h E₀ I i p.1 p.2) S := by
  classical
  ext v
  simp only [errorReductionSet, Finset.mem_image₂, sampledFactors, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image, id, Sigma.exists]
  constructor
  · rintro ⟨A, ⟨t, j, rfl⟩, s, hs, rfl⟩
    exact ⟨t, j, s, hs, rfl⟩
  · rintro ⟨t, j, s, hs, rfl⟩
    exact ⟨_, ⟨t, j, rfl⟩, s, hs, rfl⟩

/-- **The sampled error-reduction step with its output named.** When `S` is half-viable
with at most `s` members of bond dimension at most `b`, every word has rank at most `D` at
every cut, and the sampled projector is within `η < 1/2` of the ground projection, the family
`{A s : A ∈ sampledFactors, s ∈ S}` has at most `ℓ D s` members of bond dimension at most
`D max(1, b)` and is `4 η`-viable. LVV13, `algo53.tex`, Claim `c:errorreduction`, lines
584--592. -/
theorem isViableMPS_errorReductionSet_sampledFactors {i : ℕ} (hi : i ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) {D : ℕ}
    (hrank : ∀ t k, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) (bondComplementWord h (I t))) ≤ D)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1) {s b : ℕ}
    {S : Finset (LeftBlockVector L q i)} (hS : IsViableMPS Γ s b (1 / 2) S) {η : ℝ}
    (hKP : ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤ η)
    (hη : η < 1 / 2) :
    IsViableMPS Γ (ℓ * D * s) (D * max 1 b) (4 * η)
      (errorReductionSet (sampledFactors h E₀ I i) id S) := by
  classical
  rw [errorReductionSet_sampledFactors]
  have hout := hS.errorReduction_of_norm_sub_groundProjection_le hi hΓ
    (cutOperator_sampledProjector_eq_sum h E₀ I i)
    (fun p _ k hk0 hki ↦ operatorSchmidtRank_of_mem_sampledFactors hi h E₀ I hrank
      (A := sampledLeftFactor h E₀ I i p.1 p.2) (by
        simp only [sampledFactors, Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.mem_image]
        exact ⟨p.1, p.2, rfl⟩) k hki)
    hKP hη
  refine ⟨hout.1.trans (Nat.mul_le_mul_right s ?_), hout.2.1, hout.2.2⟩
  calc
    (Finset.univ : Finset ((t : Fin ℓ) × Fin _)).card
        = ∑ t : Fin ℓ, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
            (leftBlock L i) (bondComplementWord h (I t))) := by
          rw [Finset.card_univ, Fintype.card_sigma]
          simp only [Fintype.card_fin]
    _ ≤ ∑ _t : Fin ℓ, D := Finset.sum_le_sum fun t _ ↦ hrank t i
    _ = ℓ * D := by simp

end TNLean.MPS.AreaLaw
