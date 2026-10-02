/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineFactorizationIsometry
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Balanced interval isometries from minimal physical cuts

The coefficient matrix of a factorized operator groups each physical output
index with its corresponding input index. If its rank equals the intermediate
bond dimension, the prefix rows and suffix columns both span that bond space.
Applying this observation at the two bounding cuts of an interval derives the
four spanning conditions needed for determinant balancing.

The two rank equalities express minimality of the supplied bonds. This module
does not assume interval isometries or boundary Gram witnesses, and does not
assert a compression theorem for a nonminimal representation. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPUCircuit

variable {a b c d e f r s : Type*}
  [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f]
  [Fintype r] [Fintype s]

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f]
  [Fintype s] in
/-- A product whose rank equals the intermediate dimension has spanning rows
in its left factor and spanning columns in its right factor. This is the
minimality criterion used in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem spans_eq_top_of_rank_mul_eq_card {m n : Type*} [Finite m] [Fintype n]
    (X : Matrix m r ℂ) (Y : Matrix r n ℂ)
    (h : (X * Y).rank = Fintype.card r) :
    Submodule.span ℂ (Set.range X.row) = ⊤ ∧
      Submodule.span ℂ (Set.range Y.col) = ⊤ := by
  have hx : X.rank = Fintype.card r :=
    le_antisymm (rank_le_card_width X) (h ▸ rank_mul_le_left X Y)
  have hy : Y.rank = Fintype.card r :=
    le_antisymm (rank_le_card_height Y) (h ▸ rank_mul_le_right X Y)
  constructor
  · apply Submodule.eq_top_of_finrank_eq
    rw [← rank_eq_finrank_span_row]
    simpa only [Module.finrank_pi] using hx
  · apply Submodule.eq_top_of_finrank_eq
    rw [← rank_eq_finrank_span_cols]
    simpa only [Module.finrank_pi] using hy

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f]
  [Fintype s] in
/-- The physical coefficient flattening of a two-part operator, with output
and input indices grouped on each side of the cut. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def coefficientFlattening (F : a → Matrix b r ℂ)
    (G : e → Matrix r f ℂ) : Matrix (a × b) (e × f) ℂ :=
  fun ab ef ↦ (F ab.1 * G ef.1) ab.2 ef.2

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f]
  [Fintype s] in
/-- The physical coefficient flattening factors through its intermediate bond
space. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem coefficientFlattening_eq_mul (F : a → Matrix b r ℂ)
    (G : e → Matrix r f ℂ) :
    coefficientFlattening F G =
      (fun ab x ↦ F ab.1 ab.2 x) * (fun x ef ↦ G ef.1 x ef.2) := rfl

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype s] in
/-- Full rank of a physical coefficient flattening gives both bond-space
spans. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem spans_eq_top_of_coefficientFlattening_rank_eq_card
    [Finite a] [Finite b]
    (F : a → Matrix b r ℂ) (G : e → Matrix r f ℂ)
    (h : (coefficientFlattening F G).rank = Fintype.card r) :
    Submodule.span ℂ (Set.range (fun ab : a × b ↦ fun x ↦ F ab.1 ab.2 x)) = ⊤ ∧
      Submodule.span ℂ (Set.range (fun ef : e × f ↦ fun x ↦ G ef.1 x ef.2)) = ⊤ := by
  rw [coefficientFlattening_eq_mul] at h
  exact spans_eq_top_of_rank_mul_eq_card _ _ h

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f] in
/-- The coefficient flattening at the cut between the prefix and the middle
interval of a three-part operator. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def firstCutCoefficientFlattening (F : a → Matrix b r ℂ)
    (A : c → d → Matrix r s ℂ) (G : e → Matrix s f ℂ) :
    Matrix (a × b) ((c × e) × (d × f)) ℂ :=
  coefficientFlattening F (intervalSuffixProduct A G)

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f] in
/-- The coefficient flattening at the cut between the middle interval and the
suffix of a three-part operator. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def secondCutCoefficientFlattening (F : a → Matrix b r ℂ)
    (A : c → d → Matrix r s ℂ) (G : e → Matrix s f ℂ) :
    Matrix ((a × c) × (b × d)) (e × f) ℂ :=
  coefficientFlattening (prefixIntervalProduct F A) G

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [Fintype f] in
/-- The two physical cut flattenings contain the same coefficients, grouped
according to their respective cuts. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem secondCutCoefficientFlattening_apply (F : a → Matrix b r ℂ)
    (A : c → d → Matrix r s ℂ) (G : e → Matrix s f ℂ)
    (aa : a) (bb : b) (cc : c) (dd : d) (ee : e) (ff : f) :
    secondCutCoefficientFlattening F A G ((aa, cc), (bb, dd)) (ee, ff) =
      firstCutCoefficientFlattening F A G (aa, bb) ((cc, ee), (dd, ff)) := by
  change ((F aa * A cc dd) * G ee) bb ff =
    (F aa * (A cc dd * G ee)) bb ff
  rw [Matrix.mul_assoc]

omit [Fintype a] [Fintype b] in
/-- Minimal ranks at the two physical cuts imply exactly the four bond-space
spans used in the balanced interval argument. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem spans_eq_top_of_twoCutCoefficientFlattening_ranks
    [Finite a] [Finite b]
    (F : a → Matrix b r ℂ) (A : c → d → Matrix r s ℂ) (G : e → Matrix s f ℂ)
    (hfirst : (firstCutCoefficientFlattening F A G).rank = Fintype.card r)
    (hsecond : (secondCutCoefficientFlattening F A G).rank = Fintype.card s) :
    Submodule.span ℂ (Set.range (fun ab : a × b ↦ fun x ↦ F ab.1 ab.2 x)) = ⊤ ∧
      Submodule.span ℂ (Set.range (fun ef : (c × e) × (d × f) ↦
        fun x ↦ intervalSuffixProduct A G ef.1 x ef.2)) = ⊤ ∧
      Submodule.span ℂ (Set.range (fun ab : (a × c) × (b × d) ↦
        fun y ↦ prefixIntervalProduct F A ab.1 ab.2 y)) = ⊤ ∧
      Submodule.span ℂ (Set.range (fun ef : e × f ↦ fun y ↦ G ef.1 y ef.2)) = ⊤ := by
  obtain ⟨hF, hAG⟩ :=
    spans_eq_top_of_coefficientFlattening_rank_eq_card F (intervalSuffixProduct A G) hfirst
  obtain ⟨hFA, hG⟩ :=
    spans_eq_top_of_coefficientFlattening_rank_eq_card (prefixIntervalProduct F A) G hsecond
  exact ⟨hF, hAG, hFA, hG⟩

open scoped Classical in
/-- Global isometry and minimal physical cut ranks give balanced positive
metrics and an explicit interval isometry. The four bond-space spans are
derived from the two rank equalities; no boundary Gram or interval-isometry
witness is supplied. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_balanced_interval_isometry_of_coefficientFlattening_ranks
    {D E : ℕ} [Nonempty (Fin D)] [Nonempty (Fin E)]
    [Nonempty b] [Nonempty d] [Nonempty f]
    [DecidableEq b] [DecidableEq d] [DecidableEq f]
    (F : a → Matrix b (Fin D) ℂ)
    (A : c → d → Matrix (Fin D) (Fin E) ℂ)
    (G : e → Matrix (Fin E) f ℂ)
    (hU : (MPUPrefixGram.factorizedOperator F (intervalSuffixProduct A G)).IsIsometry)
    (hfirst : (firstCutCoefficientFlattening F A G).rank = D)
    (hsecond : (secondCutCoefficientFlattening F A G).rank = E) :
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
  have hfirst' : (firstCutCoefficientFlattening F A G).rank = Fintype.card (Fin D) := by
    simpa only [Fintype.card_fin] using hfirst
  have hsecond' : (secondCutCoefficientFlattening F A G).rank = Fintype.card (Fin E) := by
    simpa only [Fintype.card_fin] using hsecond
  obtain ⟨hF, hAG, hFA, hG⟩ :=
    spans_eq_top_of_twoCutCoefficientFlattening_ranks F A G hfirst' hsecond'
  exact exists_balanced_interval_isometry_of_factorizedOperator_isometry
    F A G hU hF hAG hFA hG

end MPUCircuit
