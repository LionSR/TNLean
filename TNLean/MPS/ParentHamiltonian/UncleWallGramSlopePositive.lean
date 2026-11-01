/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleWallGramAsymptotics
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Nonnegativity and a positive witness for the wall coefficient

The normalized Gram limit is nonnegative for a positive density.
A wall with vanishing correlation seed has slope equal to its positive
one-site Gram weight whenever the density is faithful and the wall is
nonzero. A physical coefficient annihilating the right-block letters
constructs such a wall when the physical dimension exceeds the square of
that block's bond dimension.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1250–1265.
This gives an explicit positive case for the source norm coefficient;
polynomial dependence and the proper exceptional-set conclusion are
separate statements.
-/

open scoped Matrix BigOperators ComplexOrder TNOperatorSpace Topology
open Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- Nonnegativity of the limiting wall coefficient follows from the
positive finite Gram weights; arXiv:1210.6613, proof of Lemma lowenergystates.
This does not assert strict positivity or genericity. -/
theorem uncleWallNormSlope_nonneg (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosSemidef)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    0 ≤ uncleWallNormSlope A B R ρ := by
  have hlim := uncleWallGramWeight_normalized_tendsto A B R ρ hρ.isHermitian hA hB hSpect
  have hnonneg (n : ℕ) : 0 ≤ ((n : ℝ)⁻¹) • uncleWallGramWeight A B R ρ n :=
    smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (uncleWallGramWeight_nonneg A B R ρ hρ n)
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hlim)
      (fun n ↦ (Complex.nonneg_iff.mp (hnonneg n)).1)
  · have him := (Complex.continuous_im.tendsto _).comp hlim
    have hzero : Tendsto (fun n : ℕ ↦
        (((n : ℝ)⁻¹) • uncleWallGramWeight A B R ρ n).im) atTop (𝓝 (0 : ℝ)) :=
      Tendsto.congr (fun n ↦ (Complex.nonneg_iff.mp (hnonneg n)).2) tendsto_const_nhds
    exact tendsto_nhds_unique hzero him

/-- If the correlation seed vanishes, every mixed correlation term
vanishes, so the source slope is exactly its one-site Gram contraction;
arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallNormSlope_of_seed_eq_zero (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hC : uncleWallSeed B R = 0) :
    uncleWallNormSlope A B R ρ = Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ) := by
  simp [uncleWallNormSlope, uncleWallCorrelationLimit, hC]

private theorem uncleWall_oneSiteGram_ne_zero
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (hR : R ≠ 0) :
    (∑ i, R i * (R i)ᴴ) ≠ 0 := by
  intro hG
  apply hR
  funext i
  have hnonneg (j : Fin d) : 0 ≤ (Matrix.trace (R j * (R j)ᴴ)).re :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose (R j)).trace_nonneg).1
  have hsum : ∑ j, (Matrix.trace (R j * (R j)ᴴ)).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, hG]
    simp
  have hre : (Matrix.trace (R i * (R i)ᴴ)).re = 0 :=
    congrFun (Fintype.sum_eq_zero_iff_of_nonneg hnonneg |>.mp hsum) i
  have him : (Matrix.trace (R i * (R i)ᴴ)).im = 0 :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose (R i)).trace_nonneg).2.symm
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (Complex.ext hre him)

/-- A nonzero wall with zero correlation seed has strictly positive
slope for a faithful density. This is a derived positive case, not a
norm-growth premise; arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallNormSlope_pos_of_seed_eq_zero
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hC : uncleWallSeed B R = 0) (hR : R ≠ 0) :
    0 < uncleWallNormSlope A B R ρ := by
  rw [uncleWallNormSlope_of_seed_eq_zero A B R ρ hC]
  exact hρ.trace_mul_pos_of_posSemidef_of_ne_zero
    (Matrix.posSemidef_sum _ fun i _ ↦ Matrix.posSemidef_self_mul_conjTranspose (R i))
    (uncleWall_oneSiteGram_ne_zero R hR)

/-- A physical coefficient annihilating the adjoint right-block letters
makes a rectangular scalar wall have zero correlation seed;
arXiv:1210.6613, positive norm-coefficient construction in the proof of
Lemma lowenergystates. -/
theorem uncleWallSeed_smul_of_annihilator (B : MPSTensor d b) (c : Fin d → ℂ)
    (M : Matrix (Fin a) (Fin b) ℂ) (hc : ∑ i, c i • (B i)ᴴ = 0) :
    uncleWallSeed B (fun i ↦ c i • M) = 0 := by
  unfold uncleWallSeed
  simp_rw [Matrix.smul_mul, ← Matrix.mul_smul]
  rw [← Matrix.mul_sum, hc, Matrix.mul_zero]

/-- There is a nonzero physical coefficient annihilating the adjoint
right-block letters when the physical dimension exceeds their matrix
space dimension. This constructs the source positive case rather than
assuming a nonzero asymptotic norm coefficient; arXiv:1210.6613,
proof of Lemma lowenergystates. -/
theorem exists_uncleWall_adjoint_annihilator (B : MPSTensor d b) (hd : b * b < d) :
    ∃ c : Fin d → ℂ, c ≠ 0 ∧ ∑ i, c i • (B i)ᴴ = 0 := by
  classical
  let f := Fintype.linearCombination ℂ (fun i : Fin d ↦ (B i)ᴴ)
  have hnot : ¬ Function.Injective f := by
    intro hf
    have hdim := LinearMap.finrank_le_finrank_of_injective hf
    have hle : d ≤ b * b := by
      simpa [Module.finrank_fintype_fun_eq_card, Module.finrank_matrix] using hdim
    exact (Nat.not_le_of_gt hd) hle
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnot
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  change f (x - y) = 0
  rw [map_sub, hxy, sub_self]

/-- An explicit scalar rectangular wall gives a positive value of the
source norm coefficient whenever the physical dimension exceeds the
right-block matrix dimension and both bond dimensions are positive.
This proves existence of a positive value, not an almost-everywhere
assertion; arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem exists_uncleWallNormSlope_pos [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef) (hd : b * b < d) :
    ∃ R : Fin d → Matrix (Fin a) (Fin b) ℂ,
      uncleWallSeed B R = 0 ∧ R ≠ 0 ∧ 0 < uncleWallNormSlope A B R ρ := by
  classical
  obtain ⟨c, hc, hczero⟩ := exists_uncleWall_adjoint_annihilator B hd
  let M : Matrix (Fin a) (Fin b) ℂ := Matrix.single 0 0 1
  have hM : M ≠ 0 := by
    intro h
    have he := congrFun (congrFun h 0) 0
    simp [M] at he
  let R : Fin d → Matrix (Fin a) (Fin b) ℂ := fun i ↦ c i • M
  have hR : R ≠ 0 := by
    intro h
    apply hc
    funext i
    have hi : c i • M = 0 := congrFun h i
    exact (smul_eq_zero.mp hi).resolve_right hM
  have hC : uncleWallSeed B R = 0 := uncleWallSeed_smul_of_annihilator B c M hczero
  exact ⟨R, hC, hR, uncleWallNormSlope_pos_of_seed_eq_zero A B R ρ hρ hC hR⟩

/-- The source full perturbation span supplies enough physical coefficients
for the preceding positive wall witness. This shows that the coefficient
has a positive value somewhere in wall space; it does not require that the
constructed witness preserve the full perturbation span, and it does not
assert a genericity theorem. Source: arXiv:1210.6613, proof of Lemma
lowenergystates, nonzero quadratic norm coefficients. -/
theorem exists_uncleWallNormSlope_pos_of_injective_perturbation [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀))
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef) :
    ∃ R : Fin d → Matrix (Fin a) (Fin b) ℂ,
      uncleWallSeed B R = 0 ∧ R ≠ 0 ∧ 0 < uncleWallNormSlope A B R ρ := by
  have hdim : (a + b) * (a + b) ≤ d := by
    have h := finrank_le_of_span_eq_top hPert.span_eq_top
    simpa [Module.finrank_matrix] using h
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hd : b * b < d :=
    lt_of_lt_of_le (Nat.mul_self_lt_mul_self (show b < a + b by omega)) hdim
  exact exists_uncleWallNormSlope_pos A B ρ hρ hd

end MPSTensor
