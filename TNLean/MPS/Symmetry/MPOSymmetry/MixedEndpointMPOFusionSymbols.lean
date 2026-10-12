/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointTripleMaps
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusionMaps
import TNLean.MPS.MPDO.BoundaryFusionFMatrix

/-!
# Source-oriented F symbols of the mixed endpoint fusion maps

The actual left analysis and right synthesis trees of the chosen mixed
fusion maps are supported on the two matching triple-bond sectors. Their
normalized trace is the dimension-weighted sum of the endpoint raw F
matrices, with rows `(e,mu,nu)` and columns `(f,lambda,sigma)`.
Equal endpoint raw F matrices therefore give the common raw F matrix of
the mixed maps. The endpoint analysis F-move equations lift to these actual
mixed fusion trees.

All incoming and outgoing dimensions are independent. No tensor
injectivity, ambient completeness, or nonzero multiplicity is assumed.
Empty final bonds have zero raw coefficients, so no positivity is required.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3,
`Fsymbolsdef` and `REsubmission.tex`, lines 1667--1685.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {r : ℕ} {χ : Fin r → ℕ} {N : Fin r → Fin r → Fin r → ℕ}

/-- The actual left analysis tree in the source's F-move, with multiplicity
order `(e,mu,nu)`. Source: GLM23, `Fsymbolsdef`. -/
noncomputable def fusionLeftTreeAnalysis
    (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (a b c d : Fin r) (q : FusionLeftMultiplicity N a b c d) :
    Matrix (Fin (χ d)) ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) ℂ :=
  fun z v ↦ ∑ t : Fin (χ q.1),
    V q.1 c d q.2.2 z (finProdFinEquiv (t, v.2)) *
      V a b q.1 q.2.1 t (finProdFinEquiv v.1)

/-- The actual right analysis tree in the source's F-move, with multiplicity
order `(f,lambda,sigma)`. Source: GLM23, `Fsymbolsdef`. -/
noncomputable def fusionRightTreeAnalysis
    (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (a b c d : Fin r) (q : FusionRightMultiplicity N a b c d) :
    Matrix (Fin (χ d)) ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) ℂ :=
  fun z v ↦ ∑ t : Fin (χ q.1),
    V a q.1 d q.2.2 z (finProdFinEquiv (v.1.1, t)) *
      V b c q.1 q.2.1 t (finProdFinEquiv (v.1.2, v.2))

/-- The actual right synthesis tree paired against left analysis to read
an F coefficient. Source: GLM23, `Fsymbolsdef` and `eq:orthoW`. -/
noncomputable def fusionRightTreeSynthesis
    (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (a b c d : Fin r) (q : FusionRightMultiplicity N a b c d) :
    Matrix ((Fin (χ a) × Fin (χ b)) × Fin (χ c)) (Fin (χ d)) ℂ :=
  fun v z ↦ ∑ t : Fin (χ q.1),
    W b c q.1 q.2.1 (finProdFinEquiv (v.1.2, v.2)) t *
      W a q.1 d q.2.2 (finProdFinEquiv (v.1.1, t)) z

/-- The named source trees are precisely the two contractions defining the
actual raw F matrix. Source: GLM23, `Fsymbolsdef`. -/
theorem fusionFMatrix_eq_inv_dim_mul_trace
    (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (a b c d : Fin r) (q : FusionLeftMultiplicity N a b c d)
    (t : FusionRightMultiplicity N a b c d) :
    fusionFMatrix V W a b c d q t = (χ d : ℂ)⁻¹ *
      Matrix.trace (fusionLeftTreeAnalysis V a b c d q *
        fusionRightTreeSynthesis W a b c d t) := by
  rcases q with ⟨e, mu, nu⟩
  rcases t with ⟨f, lambda, sigma⟩
  rfl

end MPOTensor

namespace MPSTensor.MPOSymmetry

section Coordinates

variable {χa₀ χa₁ χb₀ χb₁ χc₀ χc₁ : ℕ}

/-- Evaluation of mixed fusion analysis on direct-sum coordinates.
Source: GLM23, mixed fusion tensors, lines 1667--1685. -/
@[simp] theorem mixedEndpointMPOFusionAnalysis_sum_apply
    (V₀ : Matrix (Fin χc₀) (Fin (χa₀ * χb₀)) ℂ)
    (V₁ : Matrix (Fin χc₁) (Fin (χa₁ * χb₁)) ℂ)
    (z : Fin χc₀ ⊕ Fin χc₁) (α : Fin χa₀ ⊕ Fin χa₁)
    (β : Fin χb₀ ⊕ Fin χb₁) :
    mixedEndpointMPOFusionAnalysis V₀ V₁ (finSumFinEquiv z)
        (finProdFinEquiv (finSumFinEquiv α, finSumFinEquiv β)) =
      mixedEndpointFusionAnalysis V₀ V₁ z (α, β) := by
  change mixedEndpointMPOFusionAnalysis V₀ V₁ (finSumFinEquiv z)
    (mixedEndpointActedEquiv χa₀ χa₁ χb₀ χb₁ (α, β)) = _
  simp only [mixedEndpointMPOFusionAnalysis, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]

/-- Evaluation of mixed fusion synthesis on direct-sum coordinates.
Source: GLM23, mixed fusion tensors, lines 1667--1685. -/
@[simp] theorem mixedEndpointMPOFusionSynthesis_sum_apply
    (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χc₀) ℂ)
    (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χc₁) ℂ)
    (α : Fin χa₀ ⊕ Fin χa₁) (β : Fin χb₀ ⊕ Fin χb₁)
    (z : Fin χc₀ ⊕ Fin χc₁) :
    mixedEndpointMPOFusionSynthesis W₀ W₁
        (finProdFinEquiv (finSumFinEquiv α, finSumFinEquiv β)) (finSumFinEquiv z) =
      mixedEndpointFusionSynthesis W₀ W₁ (α, β) z := by
  change mixedEndpointMPOFusionSynthesis W₀ W₁
    (mixedEndpointActedEquiv χa₀ χa₁ χb₀ χb₁ (α, β)) (finSumFinEquiv z) = _
  simp only [mixedEndpointMPOFusionSynthesis, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]

end Coordinates

section Fusion

variable {r : ℕ} {χ₀ χ₁ : Fin r → ℕ} {N : Fin r → Fin r → Fin r → ℕ}
  (V₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (W₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (V₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (W₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)

/-- The actual mixed left fusion tree is the matching-sector sum of the
endpoint left trees. Source: GLM23, `Fsymbolsdef`, lines 1667--1685. -/
theorem mixedEndpointMPOFusion_leftTreeAnalysis (a b c d : Fin r)
    (q : MPOTensor.FusionLeftMultiplicity N a b c d) :
    (MPOTensor.fusionLeftTreeAnalysis
      (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
      a b c d q).submatrix finSumFinEquiv
        (Equiv.prodCongr (Equiv.prodCongr finSumFinEquiv finSumFinEquiv)
          finSumFinEquiv) =
      mixedEndpointTripleAnalysis (MPOTensor.fusionLeftTreeAnalysis V₀ a b c d q)
        (MPOTensor.fusionLeftTreeAnalysis V₁ a b c d q) := by
  classical
  rcases q with ⟨e, mu, nu⟩
  ext z ⟨⟨α, β⟩, γ⟩
  change (∑ t : Fin (χ₀ e + χ₁ e),
    mixedEndpointMPOFusionAnalysis (V₀ e c d nu) (V₁ e c d nu) (finSumFinEquiv z)
        (finProdFinEquiv (t, finSumFinEquiv γ)) *
      mixedEndpointMPOFusionAnalysis (V₀ a b e mu) (V₁ a b e mu) t
        (finProdFinEquiv (finSumFinEquiv α, finSumFinEquiv β))) =
    mixedEndpointTripleAnalysis
      (MPOTensor.fusionLeftTreeAnalysis V₀ a b c d ⟨e, mu, nu⟩)
      (MPOTensor.fusionLeftTreeAnalysis V₁ a b c d ⟨e, mu, nu⟩) z ((α, β), γ)
  rw [← finSumFinEquiv.sum_comp]
  simp_rw [mixedEndpointMPOFusionAnalysis_sum_apply]
  rw [Fintype.sum_sum_type]
  cases z <;> cases α <;> cases β <;> cases γ <;>
    simp [mixedEndpointFusionAnalysis, mixedEndpointTripleAnalysis,
      MPOTensor.fusionLeftTreeAnalysis]

/-- The actual mixed right fusion analysis tree is supported on the two
matching triple sectors. Source: GLM23, `Fsymbolsdef`, lines 1667--1685. -/
theorem mixedEndpointMPOFusion_rightTreeAnalysis (a b c d : Fin r)
    (q : MPOTensor.FusionRightMultiplicity N a b c d) :
    (MPOTensor.fusionRightTreeAnalysis
      (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
      a b c d q).submatrix finSumFinEquiv
        (Equiv.prodCongr (Equiv.prodCongr finSumFinEquiv finSumFinEquiv)
          finSumFinEquiv) =
      mixedEndpointTripleAnalysis (MPOTensor.fusionRightTreeAnalysis V₀ a b c d q)
        (MPOTensor.fusionRightTreeAnalysis V₁ a b c d q) := by
  classical
  rcases q with ⟨f, lambda, sigma⟩
  ext z ⟨⟨α, β⟩, γ⟩
  change (∑ t : Fin (χ₀ f + χ₁ f),
    mixedEndpointMPOFusionAnalysis (V₀ a f d sigma) (V₁ a f d sigma) (finSumFinEquiv z)
        (finProdFinEquiv (finSumFinEquiv α, t)) *
      mixedEndpointMPOFusionAnalysis (V₀ b c f lambda) (V₁ b c f lambda) t
        (finProdFinEquiv (finSumFinEquiv β, finSumFinEquiv γ))) =
    mixedEndpointTripleAnalysis
      (MPOTensor.fusionRightTreeAnalysis V₀ a b c d ⟨f, lambda, sigma⟩)
      (MPOTensor.fusionRightTreeAnalysis V₁ a b c d ⟨f, lambda, sigma⟩) z ((α, β), γ)
  rw [← finSumFinEquiv.sum_comp]
  simp_rw [mixedEndpointMPOFusionAnalysis_sum_apply]
  rw [Fintype.sum_sum_type]
  cases z <;> cases α <;> cases β <;> cases γ <;>
    simp [mixedEndpointFusionAnalysis, mixedEndpointTripleAnalysis,
      MPOTensor.fusionRightTreeAnalysis]

/-- The actual mixed right fusion synthesis tree is supported on the two
matching triple sectors. Source: GLM23, `Fsymbolsdef`, lines 1667--1685. -/
theorem mixedEndpointMPOFusion_rightTreeSynthesis (a b c d : Fin r)
    (q : MPOTensor.FusionRightMultiplicity N a b c d) :
    (MPOTensor.fusionRightTreeSynthesis
      (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
      a b c d q).submatrix
        (Equiv.prodCongr (Equiv.prodCongr finSumFinEquiv finSumFinEquiv)
          finSumFinEquiv) finSumFinEquiv =
      mixedEndpointTripleSynthesis (MPOTensor.fusionRightTreeSynthesis W₀ a b c d q)
        (MPOTensor.fusionRightTreeSynthesis W₁ a b c d q) := by
  classical
  rcases q with ⟨f, lambda, sigma⟩
  ext ⟨⟨α, β⟩, γ⟩ z
  change (∑ t : Fin (χ₀ f + χ₁ f),
    mixedEndpointMPOFusionSynthesis (W₀ b c f lambda) (W₁ b c f lambda)
        (finProdFinEquiv (finSumFinEquiv β, finSumFinEquiv γ)) t *
      mixedEndpointMPOFusionSynthesis (W₀ a f d sigma) (W₁ a f d sigma)
        (finProdFinEquiv (finSumFinEquiv α, t)) (finSumFinEquiv z)) =
    mixedEndpointTripleSynthesis
      (MPOTensor.fusionRightTreeSynthesis W₀ a b c d ⟨f, lambda, sigma⟩)
      (MPOTensor.fusionRightTreeSynthesis W₁ a b c d ⟨f, lambda, sigma⟩) ((α, β), γ) z
  rw [← finSumFinEquiv.sum_comp]
  simp_rw [mixedEndpointMPOFusionSynthesis_sum_apply]
  rw [Fintype.sum_sum_type]
  cases z <;> cases α <;> cases β <;> cases γ <;>
    simp [mixedEndpointFusionSynthesis, mixedEndpointTripleSynthesis,
      MPOTensor.fusionRightTreeSynthesis]

/-- The actual source-oriented raw F coefficient of the mixed maps is the
final-bond-dimension-weighted mean of the two endpoint coefficients.
This includes empty bonds and zero fusion multiplicities.
Source: GLM23, `Fsymbolsdef` and lines 1667--1685. -/
theorem mixedEndpointMPOFusion_fusionFMatrix_eq_weighted (a b c d : Fin r)
    (q : MPOTensor.FusionLeftMultiplicity N a b c d)
    (t : MPOTensor.FusionRightMultiplicity N a b c d) :
    MPOTensor.fusionFMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
        a b c d q t =
      ((χ₀ d + χ₁ d : ℕ) : ℂ)⁻¹ *
        ((χ₀ d : ℂ) * MPOTensor.fusionFMatrix V₀ W₀ a b c d q t +
          (χ₁ d : ℂ) * MPOTensor.fusionFMatrix V₁ W₁ a b c d q t) := by
  have h := mixedEndpointTripleAnalysis_normalizedTrace_mul_synthesis
    (MPOTensor.fusionLeftTreeAnalysis V₀ a b c d q)
    (MPOTensor.fusionLeftTreeAnalysis V₁ a b c d q)
    (MPOTensor.fusionRightTreeSynthesis W₀ a b c d t)
    (MPOTensor.fusionRightTreeSynthesis W₁ a b c d t)
  rw [← mixedEndpointMPOFusion_leftTreeAnalysis V₀ V₁ a b c d q,
    ← mixedEndpointMPOFusion_rightTreeSynthesis W₀ W₁ a b c d t,
    Matrix.submatrix_mul_equiv, Matrix.trace_submatrix_equiv] at h
  simpa only [MPOTensor.fusionFMatrix_eq_inv_dim_mul_trace] using h

/-- Equal endpoint raw F matrices give that same raw F matrix for the
chosen mixed maps. A zero total final bond is included: then both raw
matrices vanish. Source: GLM23, lines 1667--1685. -/
theorem mixedEndpointMPOFusion_fusionFMatrix_of_eq (a b c d : Fin r)
    (hF : MPOTensor.fusionFMatrix V₀ W₀ a b c d =
      MPOTensor.fusionFMatrix V₁ W₁ a b c d) :
    MPOTensor.fusionFMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
        a b c d = MPOTensor.fusionFMatrix V₀ W₀ a b c d := by
  ext q t
  rw [mixedEndpointMPOFusion_fusionFMatrix_eq_weighted, ← hF]
  by_cases hχ : χ₀ d + χ₁ d = 0
  · have hχ₀ : χ₀ d = 0 := (Nat.add_eq_zero_iff.mp hχ).1
    simp [MPOTensor.fusionFMatrix_eq_inv_dim_mul_trace, hχ₀]
  · have hne : ((χ₀ d + χ₁ d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hχ
    rw [← add_mul, ← Nat.cast_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The endpoint analysis F-move equations lift to the actual mixed fusion
trees with their actual common raw F matrix. This is a lift of endpoint
relations; it assumes no F-move identity for the mixed maps.
Source: GLM23, `Fsymbolsdef` and lines 1667--1685. -/
theorem mixedEndpointMPOFusion_fusionFMatrix_analysis (a b c d : Fin r)
    (hF : MPOTensor.fusionFMatrix V₀ W₀ a b c d =
      MPOTensor.fusionFMatrix V₁ W₁ a b c d)
    (hMove₀ : ∀ q : MPOTensor.FusionLeftMultiplicity N a b c d,
      MPOTensor.fusionLeftTreeAnalysis V₀ a b c d q =
        ∑ t : MPOTensor.FusionRightMultiplicity N a b c d,
          MPOTensor.fusionFMatrix V₀ W₀ a b c d q t •
            MPOTensor.fusionRightTreeAnalysis V₀ a b c d t)
    (hMove₁ : ∀ q : MPOTensor.FusionLeftMultiplicity N a b c d,
      MPOTensor.fusionLeftTreeAnalysis V₁ a b c d q =
        ∑ t : MPOTensor.FusionRightMultiplicity N a b c d,
          MPOTensor.fusionFMatrix V₁ W₁ a b c d q t •
            MPOTensor.fusionRightTreeAnalysis V₁ a b c d t)
    (q : MPOTensor.FusionLeftMultiplicity N a b c d) :
    MPOTensor.fusionLeftTreeAnalysis
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        a b c d q =
      ∑ t : MPOTensor.FusionRightMultiplicity N a b c d,
        MPOTensor.fusionFMatrix
            (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
            (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
            a b c d q t •
          MPOTensor.fusionRightTreeAnalysis
            (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
            a b c d t := by
  classical
  rw [mixedEndpointMPOFusion_fusionFMatrix_of_eq V₀ W₀ V₁ W₁ a b c d hF]
  ext z ⟨⟨α, β⟩, γ⟩
  obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective z
  obtain ⟨α, rfl⟩ := finSumFinEquiv.surjective α
  obtain ⟨β, rfl⟩ := finSumFinEquiv.surjective β
  obtain ⟨γ, rfl⟩ := finSumFinEquiv.surjective γ
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hLeft := congrArg (fun H ↦ H z ((α, β), γ))
    (mixedEndpointMPOFusion_leftTreeAnalysis V₀ V₁ a b c d q)
  have hRight (t : MPOTensor.FusionRightMultiplicity N a b c d) :=
    congrArg (fun H ↦ H z ((α, β), γ))
      (mixedEndpointMPOFusion_rightTreeAnalysis V₀ V₁ a b c d t)
  simp only [Matrix.submatrix_apply, Equiv.prodCongr_apply, Prod.map_apply] at hLeft hRight
  rw [hLeft]
  simp_rw [hRight]
  cases z <;> cases α <;> cases β <;> cases γ <;>
    simp only [mixedEndpointTripleAnalysis, mul_zero, Finset.sum_const_zero]
  · rename_i z α β γ
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun H ↦ H z ((α, β), γ)) (hMove₀ q)
  · rename_i z α β γ
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hF] using
      congrArg (fun H ↦ H z ((α, β), γ)) (hMove₁ q)

end Fusion

end MPSTensor.MPOSymmetry
