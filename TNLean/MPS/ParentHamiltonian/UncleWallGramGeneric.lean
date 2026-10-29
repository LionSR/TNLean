/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleWallGramQuadratic
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Generic positivity of the actual one-wall norm coefficient

The actual source wall coefficient is a nonnegative real quadratic form.
Its zero set is its radical, a real linear subspace; the explicit positive
wall witness makes this subspace proper. Consequently its complement is
open and dense and the exceptional set has zero additive Haar measure.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1250–1265.
These are the one-wall coefficients. The actual two-wall norm estimate
still needs the separating-transfer factorization error bound.
-/

open scoped Matrix BigOperators ComplexOrder TNOperatorSpace Topology
open MeasureTheory Filter

namespace MPSTensor

variable {d a b : ℕ}

private theorem wallQuadratic_polar_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : ∀ x, 0 ≤ Q x) {x : V} (hx : Q x = 0) (y : V) :
    QuadraticMap.polar Q x y = 0 := by
  let p := QuadraticMap.polar Q x y
  let t := -p / (Q y + 1)
  have hd : 0 < Q y + 1 := by linarith [hQ y]
  have heq : Q (x + t • y) = -(p * p) / (Q y + 1) ^ 2 := by
    rw [QuadraticMap.map_add (Q : V → ℝ) x (t • y), Q.map_smul,
      QuadraticMap.polar_smul_right, hx]
    simp only [zero_add, smul_eq_mul]
    change (t * t) * Q y + t * p = _
    dsimp [t]
    field_simp [ne_of_gt hd]
    ring
  have hnonneg := hQ (x + t • y)
  rw [heq] at hnonneg
  have hscaled := mul_nonneg hnonneg (le_of_lt (sq_pos_of_pos hd))
  have hp : p * p = 0 := by
    have hden : (Q y + 1) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hd)
    rw [div_mul_cancel₀ _ hden] at hscaled
    nlinarith [sq_nonneg p]
  exact (mul_self_eq_zero.mp hp : p = 0)

private theorem wallQuadratic_mem_radical_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : ∀ x, 0 ≤ Q x) (x : V) :
    x ∈ Q.radical ↔ Q x = 0 := by
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    change Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0
    refine ⟨hx, ?_⟩
    apply LinearMap.ext
    intro y
    exact wallQuadratic_polar_eq_zero Q hQ hx y

private theorem wallQuadratic_radical_ne_top {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : Q ≠ 0) : Q.radical ≠ ⊤ := by
  intro htop
  apply hQ
  ext x
  have hx : x ∈ Q.radical := by rw [htop]; trivial
  exact hx.1

/-- The zero set of the actual source quadratic coefficient is its real
linear radical. This is derived from nonnegative actual finite Gram
weights, not assumed as a genericity premise; arXiv:1210.6613,
proof of Lemma lowenergystates. -/
theorem uncleWallSlopeQuadratic_mem_radical_iff
    (A : MPSTensor d a) (B : MPSTensor d b)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosSemidef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) :
    R ∈ (uncleWallSlopeQuadratic A B ρ hSpect).radical ↔
      uncleWallSlopeQuadratic A B ρ hSpect R = 0 :=
  wallQuadratic_mem_radical_iff _ (uncleWallSlopeQuadratic_nonneg A B ρ hρ hA hB hSpect) R

/-- The exceptional subspace of zero actual wall coefficients is proper in
the source full-perturbation setting; arXiv:1210.6613, proof of Lemma
lowenergystates, nonzero quadratic coefficient. -/
theorem uncleWallSlopeQuadratic_radical_ne_top [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    (uncleWallSlopeQuadratic A B ρ hSpect).radical ≠ ⊤ :=
  wallQuadratic_radical_ne_top _
    (uncleWallSlopeQuadratic_ne_zero A B R₀ L₀ hPert ρ hρ hSpect)

private theorem wallQuadratic_positive_set_eq_compl_radical {V : Type*}
    [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V) (hQ : ∀ x, 0 ≤ Q x) :
    {x | 0 < Q x} = (Q.radical : Set V)ᶜ := by
  ext x
  change 0 < Q x ↔ ¬ x ∈ Q.radical
  rw [wallQuadratic_mem_radical_iff Q hQ x]
  exact ⟨ne_of_gt, fun hx ↦ lt_of_le_of_ne (hQ x) (Ne.symm hx)⟩

/-- Positive actual wall slopes form an open dense set under the source
canonical normalizations and full perturbation span. This assertion
concerns the coefficient itself, not the full two-wall trial norm;
arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallSlopeQuadratic_positive_open_dense [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    IsOpen {R | 0 < uncleWallSlopeQuadratic A B ρ hSpect R} ∧
      Dense {R | 0 < uncleWallSlopeQuadratic A B ρ hSpect R} := by
  let S := (uncleWallSlopeQuadratic A B ρ hSpect).radical
  have hproper : S ≠ ⊤ :=
    uncleWallSlopeQuadratic_radical_ne_top A B R₀ L₀ hPert ρ hρ hSpect
  simp only [wallQuadratic_positive_set_eq_compl_radical _
    (uncleWallSlopeQuadratic_nonneg A B ρ hρ.posSemidef hA hB hSpect)]
  refine ⟨S.closed_of_finiteDimensional.isOpen_compl, ?_⟩
  apply interior_eq_empty_iff_dense_compl.mp
  by_contra h
  exact hproper (S.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr h))

/-- The actual zero wall coefficient has zero additive Haar measure;
arXiv:1210.6613, proof of Lemma lowenergystates. The exceptional set is
the derived proper linear radical of its nonnegative quadratic form. -/
theorem uncleWallSlopeQuadratic_zero_measure [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1)
    (μ : Measure (Fin d → Matrix (Fin a) (Fin b) ℂ)) [Measure.IsAddHaarMeasure μ] :
    μ {R | uncleWallSlopeQuadratic A B ρ hSpect R = 0} = 0 := by
  have hset : {R | uncleWallSlopeQuadratic A B ρ hSpect R = 0} =
      ((uncleWallSlopeQuadratic A B ρ hSpect).radical :
        Set (Fin d → Matrix (Fin a) (Fin b) ℂ)) := by
    ext R
    exact (uncleWallSlopeQuadratic_mem_radical_iff A B ρ hρ.posSemidef hA hB hSpect R).symm
  rw [hset]
  exact addHaar_submodule μ _
    (uncleWallSlopeQuadratic_radical_ne_top A B R₀ L₀ hPert ρ hρ hSpect)

/-- Almost every wall has strictly positive actual limiting Gram slope
under the source canonical normalizations and a full perturbation span.
This supplies the one-wall generic positivity step; the two-wall norm
factorization estimate remains separate. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, lines 1250–1265. -/
theorem uncleWallNormSlope_ae_pos [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1)
    (μ : Measure (Fin d → Matrix (Fin a) (Fin b) ℂ)) [Measure.IsAddHaarMeasure μ] :
    ∀ᵐ R ∂μ, 0 < uncleWallNormSlope A B R ρ := by
  have hq : ∀ᵐ R ∂μ, 0 < uncleWallSlopeQuadratic A B ρ hSpect R := by
    have hset : {R | ¬ 0 < uncleWallSlopeQuadratic A B ρ hSpect R} =
        {R | uncleWallSlopeQuadratic A B ρ hSpect R = 0} := by
      ext R
      simp only [Set.mem_ofPred_eq, not_lt]
      exact ⟨fun h ↦ le_antisymm h
        (uncleWallSlopeQuadratic_nonneg A B ρ hρ.posSemidef hA hB hSpect R), fun h ↦ h.le⟩
    rw [ae_iff, hset]
    exact uncleWallSlopeQuadratic_zero_measure A B R₀ L₀ hPert ρ hρ hA hB hSpect μ
  filter_upwards [hq] with R hR
  apply Complex.pos_iff.mpr
  rw [uncleWallSlopeQuadratic_apply] at hR
  exact ⟨hR, (Complex.nonneg_iff.mp
    (uncleWallNormSlope_nonneg A B R ρ hρ.posSemidef hA hB hSpect)).2⟩

/-- For almost every pair of walls, both actual one-wall limiting
coefficients are strictly positive. A single additive Haar measure on
the pair space is used; independence of component measures is not a
hypothesis. Source: arXiv:1210.6613, proof of Lemma lowenergystates,
the two quadratic coefficients in the norm factorization. -/
theorem uncleWallNormSlope_pair_ae_pos [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef)
    (hA : Kraus.adjointMap A ρA = ρA) (hB : Kraus.adjointMap B ρB = ρB)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1)
    (μ : Measure ((Fin d → Matrix (Fin a) (Fin b) ℂ) ×
      (Fin d → Matrix (Fin b) (Fin a) ℂ))) [Measure.IsAddHaarMeasure μ] :
    ∀ᵐ P ∂μ, 0 < uncleWallNormSlope A B P.1 ρA ∧
      0 < uncleWallNormSlope B A P.2 ρB := by
  have hdim : (a + b) * (a + b) ≤ d := by
    have h := finrank_le_of_span_eq_top hPert.span_eq_top
    simpa [Module.finrank_matrix] using h
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have hdA : a * a < d :=
    lt_of_lt_of_le (Nat.mul_self_lt_mul_self (show a < a + b by omega)) hdim
  have hdB : b * b < d :=
    lt_of_lt_of_le (Nat.mul_self_lt_mul_self (show b < a + b by omega)) hdim
  let Q₁ := uncleWallSlopeQuadratic A B ρA hAB
  let Q₂ := uncleWallSlopeQuadratic B A ρB hBA
  let S₁ := Q₁.radical
  let S₂ := Q₂.radical
  have hQ₁ : ∀ R, 0 ≤ Q₁ R :=
    uncleWallSlopeQuadratic_nonneg A B ρA hρA.posSemidef hA hUB hAB
  have hQ₂ : ∀ L, 0 ≤ Q₂ L :=
    uncleWallSlopeQuadratic_nonneg B A ρB hρB.posSemidef hB hUA hBA
  have hS₁ : S₁ ≠ ⊤ := wallQuadratic_radical_ne_top Q₁
    (uncleWallSlopeQuadratic_ne_zero_of_bond_sq_lt A B ρA hρA hdB hAB)
  have hS₂ : S₂ ≠ ⊤ := wallQuadratic_radical_ne_top Q₂
    (uncleWallSlopeQuadratic_ne_zero_of_bond_sq_lt B A ρB hρB hdA hBA)
  have hnull₁ : μ (S₁.prod ⊤) = 0 := addHaar_submodule μ _
    (fun h ↦ hS₁ (Submodule.prod_eq_top_iff.mp h).1)
  have hnull₂ : μ ((⊤ : Submodule ℝ (Fin d → Matrix (Fin a) (Fin b) ℂ)).prod S₂) = 0 :=
    addHaar_submodule μ _ (fun h ↦ hS₂ (Submodule.prod_eq_top_iff.mp h).2)
  have hae₁ : ∀ᵐ P ∂μ, P.1 ∉ S₁ := by
    have hset : {P : (Fin d → Matrix (Fin a) (Fin b) ℂ) ×
        (Fin d → Matrix (Fin b) (Fin a) ℂ) | P.1 ∈ S₁} = (S₁.prod (⊤ :
        Submodule ℝ (Fin d → Matrix (Fin b) (Fin a) ℂ)) : Set _) := by
      ext P
      simp
    rw [ae_iff]
    simpa only [not_not, hset] using hnull₁
  have hae₂ : ∀ᵐ P ∂μ, P.2 ∉ S₂ := by
    have hset : {P : (Fin d → Matrix (Fin a) (Fin b) ℂ) ×
        (Fin d → Matrix (Fin b) (Fin a) ℂ) | P.2 ∈ S₂} = ((⊤ :
        Submodule ℝ (Fin d → Matrix (Fin a) (Fin b) ℂ)).prod S₂ : Set _) := by
      ext P
      simp
    rw [ae_iff]
    simpa only [not_not, hset] using hnull₂
  filter_upwards [hae₁, hae₂] with P hP₁ hP₂
  have hp₁ : 0 < Q₁ P.1 := lt_of_le_of_ne (hQ₁ P.1)
    (fun h ↦ hP₁ ((wallQuadratic_mem_radical_iff Q₁ hQ₁ P.1).mpr h.symm))
  have hp₂ : 0 < Q₂ P.2 := lt_of_le_of_ne (hQ₂ P.2)
    (fun h ↦ hP₂ ((wallQuadratic_mem_radical_iff Q₂ hQ₂ P.2).mpr h.symm))
  change 0 < uncleWallSlopeQuadratic A B ρA hAB P.1 at hp₁
  change 0 < uncleWallSlopeQuadratic B A ρB hBA P.2 at hp₂
  rw [uncleWallSlopeQuadratic_apply] at hp₁ hp₂
  exact ⟨Complex.pos_iff.mpr ⟨hp₁, (Complex.nonneg_iff.mp
      (uncleWallNormSlope_nonneg A B P.1 ρA hρA.posSemidef hA hUB hAB)).2⟩,
    Complex.pos_iff.mpr ⟨hp₂, (Complex.nonneg_iff.mp
      (uncleWallNormSlope_nonneg B A P.2 ρB hρB.posSemidef hB hUA hBA)).2⟩⟩

end MPSTensor
