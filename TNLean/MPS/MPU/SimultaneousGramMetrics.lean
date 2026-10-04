/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineFactorizationRank

/-!
# Simultaneous balanced metrics at minimal cuts

A globally isometric two-part factorization with spanning prefix rows and
suffix columns admits a balanced positive metric on its bond space. Applying
this result to an indexed family and choosing one metric at each index gives
all affine normalization and dimension-squared contraction identities
simultaneously. Finite chains are a specialization of this statement.

The hypotheses are global isometry and ordinary bond-space minimality. No
boundary normalizer is supplied. Compatibility with interval transfer maps
is treated separately. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MPUCircuit

/-- Global isometry and minimality at a single cut yield a balanced positive
bond metric, its positive dual, normalization on the entire real affine Gram
hull, and the dimension-squared inverse-metric trace. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_balanced_prefix_metric_of_factorizedOperator_isometry
    {a b e f : Type*} [Fintype a] [Fintype b] [Fintype e] [Finite f]
    [Nonempty b] [Nonempty f] [DecidableEq b] [DecidableEq f]
    {D : ℕ} [Nonempty (Fin D)]
    (F : a → Matrix b (Fin D) ℂ) (G : e → Matrix (Fin D) f ℂ)
    (hU : (MPUPrefixGram.factorizedOperator F G).IsIsometry)
    (hFspan : Submodule.span ℂ
      (Set.range (fun ab : a × b ↦ fun x ↦ F ab.1 ab.2 x)) = ⊤)
    (hGspan : Submodule.span ℂ
      (Set.range (fun ef : e × f ↦ fun x ↦ G ef.1 x ef.2)) = ⊤) :
    ∃ P ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F aa bb x),
      P.PosDef ∧ (dualGramMetric P).PosDef ∧
      (∀ X ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F aa bb x),
        trace (X * dualGramMetric P) = 1) ∧
      trace ((dualGramMetric P)⁻¹ * P⁻¹) = (D : ℂ) ^ 2 := by
  obtain ⟨Q₀, hQ₀, hnorm⟩ :=
    exists_posDef_prefixGramAffineHull_normalizer_of_isIsometry F G hU hGspan
  have hPD := MPUPrefixGram.exists_posDef_mem_prefixGramAffineHull_of_span_eq_top F hFspan
  exact exists_posDef_dualGramMetric_on_affineSubspace
    (prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F aa bb x))
    (fun X hX ↦ isHermitian_of_mem_prefixGramAffineHull _ hX) hQ₀ hnorm hPD

/-- An indexed family of minimal globally isometric factorizations has one
simultaneously chosen balanced metric at each cut. All positive-definiteness,
affine normalization, and dimension-squared contraction identities hold for
the same chosen metric family. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_simultaneous_balanced_prefix_metrics_of_factorizedOperator_isometries
    {ι : Type*} {a b e f : ι → Type*} {D : ι → ℕ}
    [∀ j, Fintype (a j)] [∀ j, Fintype (b j)] [∀ j, Fintype (e j)]
    [∀ j, Finite (f j)] [∀ j, Nonempty (b j)] [∀ j, Nonempty (f j)]
    [∀ j, DecidableEq (b j)] [∀ j, DecidableEq (f j)]
    [∀ j, Nonempty (Fin (D j))]
    (F : ∀ j, a j → Matrix (b j) (Fin (D j)) ℂ)
    (G : ∀ j, e j → Matrix (Fin (D j)) (f j) ℂ)
    (hU : ∀ j, (MPUPrefixGram.factorizedOperator (F j) (G j)).IsIsometry)
    (hFspan : ∀ j, Submodule.span ℂ
      (Set.range (fun ab : a j × b j ↦ fun x ↦ F j ab.1 ab.2 x)) = ⊤)
    (hGspan : ∀ j, Submodule.span ℂ
      (Set.range (fun ef : e j × f j ↦ fun x ↦ G j ef.1 x ef.2)) = ⊤) :
    ∃ P : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ,
      ∀ j, P j ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F j aa bb x) ∧
        (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
        (∀ X ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F j aa bb x),
          trace (X * dualGramMetric (P j)) = 1) ∧
        trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) = (D j : ℂ) ^ 2 := by
  have hex := fun j ↦ exists_balanced_prefix_metric_of_factorizedOperator_isometry
    (F j) (G j) (hU j) (hFspan j) (hGspan j)
  exact ⟨fun j ↦ Classical.choose (hex j), fun j ↦ Classical.choose_spec (hex j)⟩

/-- Minimal physical coefficient ranks give a simultaneously chosen balanced
metric family. Both bond-space spans at every cut are derived from its rank
equality. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_simultaneous_balanced_prefix_metrics_of_coefficientFlattening_ranks
    {ι : Type*} {a b e f : ι → Type*} {D : ι → ℕ}
    [∀ j, Fintype (a j)] [∀ j, Fintype (b j)] [∀ j, Fintype (e j)]
    [∀ j, Fintype (f j)] [∀ j, Nonempty (b j)] [∀ j, Nonempty (f j)]
    [∀ j, DecidableEq (b j)] [∀ j, DecidableEq (f j)]
    [∀ j, Nonempty (Fin (D j))]
    (F : ∀ j, a j → Matrix (b j) (Fin (D j)) ℂ)
    (G : ∀ j, e j → Matrix (Fin (D j)) (f j) ℂ)
    (hU : ∀ j, (MPUPrefixGram.factorizedOperator (F j) (G j)).IsIsometry)
    (hrank : ∀ j, (coefficientFlattening (F j) (G j)).rank = D j) :
    ∃ P : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ,
      ∀ j, P j ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F j aa bb x) ∧
        (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
        (∀ X ∈ prefixGramAffineHull (fun aa bb (_ : Unit) x ↦ F j aa bb x),
          trace (X * dualGramMetric (P j)) = 1) ∧
        trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) = (D j : ℂ) ^ 2 := by
  have hspans := fun j ↦ spans_eq_top_of_coefficientFlattening_rank_eq_card (F j) (G j)
    (by simpa only [Fintype.card_fin] using hrank j)
  exact exists_simultaneous_balanced_prefix_metrics_of_factorizedOperator_isometries
    F G hU (fun j ↦ (hspans j).1) (fun j ↦ (hspans j).2)

end MPUCircuit
