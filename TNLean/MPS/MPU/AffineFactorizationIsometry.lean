/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineIntervalIsometry
import TNLean.MPS.MPU.PrefixGramNormalizer

/-!
# Balanced interval isometries from a globally isometric factorization

A three-part factorization determines the prefix and suffix operators at
both bounding cuts of its middle interval. Global isometry supplies the
boundary trace normalizations. Spanning rows and columns at the two cuts
supply positive-definite boundary Grams. Determinant balancing then gives
an interval isometry and contraction constants depending only on the two
bond dimensions.

This is the boundary-to-interval argument in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. No interval-isometry or
boundary-normalizer witness is assumed.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPUCircuit

variable {a b c d e f r s : Type*}
  [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f]
  [Fintype r] [Fintype s]

/-- The prefix obtained by adjoining the middle interval to the first factor.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def prefixIntervalProduct (F : a → Matrix b r ℂ)
    (A : c → d → Matrix r s ℂ) : (a × c) → Matrix (b × d) s ℂ :=
  fun ac ↦ Matrix.of fun bd y ↦ ∑ x, F ac.1 bd.1 x * A ac.2 bd.2 x y

/-- The suffix obtained by adjoining the middle interval to the last factor.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def intervalSuffixProduct (A : c → d → Matrix r s ℂ)
    (G : e → Matrix s f ℂ) : (c × e) → Matrix r (d × f) ℂ :=
  fun ce ↦ Matrix.of fun x df ↦ ∑ y, A ce.1 df.1 x y * G ce.2 y df.2

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f] in
/-- The two cuts of a three-part factorization differ only by reassociation
of their physical indices. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem factorizedOperator_reassociate
    (F : a → Matrix b r ℂ) (A : c → d → Matrix r s ℂ) (G : e → Matrix s f ℂ) :
    MPUPrefixGram.factorizedOperator (prefixIntervalProduct F A) G =
      Matrix.reindex (Equiv.prodAssoc a c e).symm (Equiv.prodAssoc b d f).symm
        (MPUPrefixGram.factorizedOperator F (intervalSuffixProduct A G)) := by
  ext ace bdf
  rcases ace with ⟨⟨aa, cc⟩, ee⟩
  rcases bdf with ⟨⟨bb, dd⟩, ff⟩
  change ((F aa * A cc dd) * G ee) bb ff =
    (F aa * (A cc dd * G ee)) bb ff
  rw [Matrix.mul_assoc]

omit [Fintype b] [Fintype d] [Fintype f] in
open scoped Classical in
/-- Global isometry at the first cut implies global isometry at the second
cut of the same three-part factorization. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem factorizedOperator_isometry_reassociate
    [DecidableEq b] [DecidableEq d] [DecidableEq f]
    (F : a → Matrix b r ℂ) (A : c → d → Matrix r s ℂ) (G : e → Matrix s f ℂ)
    (hU : (MPUPrefixGram.factorizedOperator F (intervalSuffixProduct A G)).IsIsometry) :
    (MPUPrefixGram.factorizedOperator (prefixIntervalProduct F A) G).IsIsometry := by
  rw [factorizedOperator_reassociate]
  exact hU.reindex _ (Equiv.prodAssoc a c e).symm (Equiv.prodAssoc b d f).symm

omit [Fintype f] in
open scoped Classical in
/-- Global isometry and spanning suffix columns give a positive-definite
normalizer on the entire real affine hull of prefix Grams. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_posDef_prefixGramAffineHull_normalizer_of_isIsometry
    [Finite f] [Nonempty f] [DecidableEq b] [DecidableEq f]
    (F : a → Matrix b r ℂ) (G : e → Matrix r f ℂ)
    (hU : (MPUPrefixGram.factorizedOperator F G).IsIsometry)
    (hspan : Submodule.span ℂ
      (Set.range (fun ef : e × f ↦ fun x ↦ G ef.1 x ef.2)) = ⊤) :
    ∃ Q : Matrix r r ℂ, Q.PosDef ∧
      ∀ X ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F aa bb x),
        trace (X * Q) = 1 := by
  obtain ⟨Q, hQ, hnorm⟩ :=
    MPUPrefixGram.exists_posDef_prefixInputGram_normalizer_of_isIsometry F G hU hspan
  refine ⟨Q, hQ, ?_⟩
  intro X hX
  apply trace_mul_eq_of_mem_real_affineSpan Q 1 ?_ hX
  rintro Y ⟨ρ, _, hρtrace, rfl⟩
  exact hnorm ρ hρtrace

omit [Fintype f] in
open scoped Classical in
/-- A globally isometric three-part factorization with spanning rows and
columns at both bounding cuts admits balanced positive metrics for its
middle interval. The interval isometry, both affine normalization identities,
and both dimension-squared contraction constants are conclusions. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_balanced_interval_isometry_of_factorizedOperator_isometry
    {D E : ℕ} [Nonempty (Fin D)] [Nonempty (Fin E)]
    [Finite f] [Nonempty b] [Nonempty d] [Nonempty f]
    [DecidableEq b] [DecidableEq d] [DecidableEq f]
    (F : a → Matrix b (Fin D) ℂ)
    (A : c → d → Matrix (Fin D) (Fin E) ℂ)
    (G : e → Matrix (Fin E) f ℂ)
    (hU : (MPUPrefixGram.factorizedOperator F (intervalSuffixProduct A G)).IsIsometry)
    (hFspan : Submodule.span ℂ
      (Set.range (fun ab : a × b ↦ fun x ↦ F ab.1 ab.2 x)) = ⊤)
    (hAGspan : Submodule.span ℂ
      (Set.range (fun ef : (c × e) × (d × f) ↦
        fun x ↦ intervalSuffixProduct A G ef.1 x ef.2)) = ⊤)
    (hFAspan : Submodule.span ℂ
      (Set.range (fun ab : (a × c) × (b × d) ↦
        fun y ↦ prefixIntervalProduct F A ab.1 ab.2 y)) = ⊤)
    (hGspan : Submodule.span ℂ
      (Set.range (fun ef : e × f ↦ fun y ↦ G ef.1 y ef.2)) = ⊤) :
    ∃ P ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F aa bb x),
      ∃ S ∈ prefixGramAffineHull
        (fun ac bd (_ : Unit) y ↦ prefixIntervalProduct F A ac bd y),
        P.PosDef ∧ S.PosDef ∧ (dualGramMetric P).PosDef ∧ (dualGramMetric S).PosDef ∧
        (∀ X ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F aa bb x),
          trace (X * dualGramMetric P) = 1) ∧
        (∀ X ∈ prefixGramAffineHull
          (fun ac bd (_ : Unit) y ↦ prefixIntervalProduct F A ac bd y),
            trace (X * dualGramMetric S) = 1) ∧
        trace ((dualGramMetric P)⁻¹ * P⁻¹) = (D : ℂ) ^ 2 ∧
        trace ((dualGramMetric S)⁻¹ * S⁻¹) = (E : ℂ) ^ 2 ∧
        (vectorizedWeightedInterval A (CFC.sqrt P) (CFC.sqrt (dualGramMetric S)))ᴴ *
          vectorizedWeightedInterval A (CFC.sqrt P) (CFC.sqrt (dualGramMetric S)) = 1 := by
  obtain ⟨Q₀, hQ₀, hleftNorm⟩ :=
    exists_posDef_prefixGramAffineHull_normalizer_of_isIsometry
      F (intervalSuffixProduct A G) hU hAGspan
  have hU' := factorizedOperator_isometry_reassociate F A G hU
  obtain ⟨Q₁, hQ₁, hrightNorm⟩ :=
    exists_posDef_prefixGramAffineHull_normalizer_of_isIsometry
      (prefixIntervalProduct F A) G hU' hGspan
  have hleftPD := MPUPrefixGram.exists_posDef_mem_prefixGramAffineHull_of_span_eq_top
    F hFspan
  have hrightPD := MPUPrefixGram.exists_posDef_mem_prefixGramAffineHull_of_span_eq_top
    (prefixIntervalProduct F A) hFAspan
  have hrows :
      (fun (ac : a × c) (bd : b × d) (_ : Unit) y ↦ prefixIntervalProduct F A ac bd y) =
        (fun (ac : a × c) (bd : b × d) ↦
          (show Matrix Unit (Fin D) ℂ from fun (_ : Unit) x ↦ F ac.1 bd.1 x) *
            A ac.2 bd.2) := by
    funext ac bd u y
    rfl
  have hrightNorm' : ∀ X ∈ prefixGramAffineHull
      (fun (ac : a × c) (bd : b × d) ↦
        (show Matrix Unit (Fin D) ℂ from fun (_ : Unit) x ↦ F ac.1 bd.1 x) * A ac.2 bd.2),
        trace (X * Q₁) = 1 := by
    rw [← hrows]
    exact hrightNorm
  have hrightPD' : ∃ X ∈ prefixGramAffineHull
      (fun (ac : a × c) (bd : b × d) ↦
        (show Matrix Unit (Fin D) ℂ from fun (_ : Unit) x ↦ F ac.1 bd.1 x) * A ac.2 bd.2),
        X.PosDef := by
    rw [← hrows]
    exact hrightPD
  have hresult := exists_balanced_prefix_metrics_interval_isometry
    (fun aa bb (_ : Unit) x ↦ F aa bb x) A hQ₀ hleftNorm hleftPD
    hQ₁ hrightNorm' hrightPD'
  simp only [← hrows] at hresult
  obtain ⟨P, hPC, S, hSC, hP, hS, hdualP, hdualS,
    hPNorm, hSNorm, hPTrace, hSTrace, hiso⟩ := hresult
  refine ⟨P, hPC, S, hSC, hP, hS, hdualP, hdualS,
    hPNorm, hSNorm, hPTrace, hSTrace, ?_⟩
  convert hiso using 1
  ext u v
  by_cases huv : u = v
  · subst v
    simp
  · simp [huv]

end MPUCircuit
