/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import TNLean.MPS.Defs

/-!
# Rectangular reductions of matrix product state tensors

This file introduces the source-facing notion of a reduction between MPS
tensors of possibly different bond dimensions.  The existence theorem of
Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Proposition 20, is separate from
the definition below.
-/

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

/-- A rectangular reduction from `B` to `A` consists of matrices `V,W` with
$VW=1$ which intertwine every virtual word:
$V B^{\mathbf a} W=A^{\mathbf a}$.  The word clause includes the empty word.

Source: Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Definition following
Proposition 20, `cornerproblem.tex` lines 3137--3139; the equations are stated
at lines 3129--3132, and the empty-word equation is made explicit at lines
3934--3938. -/
def IsReduction (B : MPSTensor d D₂) (A : MPSTensor d D₁)
    (V : Matrix (Fin D₁) (Fin D₂) ℂ) (W : Matrix (Fin D₂) (Fin D₁) ℂ) : Prop :=
  V * W = 1 ∧
    ∀ w : List (Fin d), V * Kraus.evalWord B w * W = Kraus.evalWord A w

namespace IsReduction

variable {B : MPSTensor d D₂} {A : MPSTensor d D₁}
  {V : Matrix (Fin D₁) (Fin D₂) ℂ} {W : Matrix (Fin D₂) (Fin D₁) ℂ}

/-- The two rectangular matrices in a reduction have product one on the target
bond space. -/
theorem mul_eq_one (h : IsReduction B A V W) : V * W = 1 := h.1

/-- A reduction intertwines every word, including the empty word. -/
theorem evalWord (h : IsReduction B A V W) (w : List (Fin d)) :
    V * Kraus.evalWord B w * W = Kraus.evalWord A w := h.2 w

/-- The empty-word instance of the intertwining equation. -/
theorem evalWord_nil (h : IsReduction B A V W) :
    V * Kraus.evalWord B [] * W = Kraus.evalWord A [] := h.2 []

/-- Scaling both tensors by the same scalar preserves a rectangular reduction. -/
theorem smul (h : IsReduction B A V W) (c : ℂ) :
    IsReduction (fun i => c • B i) (fun i => c • A i) V W := by
  refine ⟨h.mul_eq_one, fun w => ?_⟩
  simp only [Kraus.evalWord_smul, Matrix.mul_smul, Matrix.smul_mul, h.evalWord]

/-- A reduction whose target is scaled by `c` intertwines an unscaled source
word with `c` to the word length times the corresponding unscaled target word.

This is the explicit corrected relation in MGSC18, Proposition 20,
`eq:mgsc18_reduction_proportionality_corrected_word_relation`; see
`docs/paper-gaps/mgsc18_reduction_proportionality_scalar.tex`, lines 96--120. -/
theorem evalWord_smul_target {c : ℂ}
    (h : IsReduction B (fun i => c • A i) V W) (w : List (Fin d)) :
    V * Kraus.evalWord B w * W = (c ^ w.length) • Kraus.evalWord A w := by
  simpa only [Kraus.evalWord_smul] using h.evalWord w

/-- A rectangular reduction cannot increase the bond dimension: the target
bond dimension is at most the source bond dimension. -/
theorem bondDim_le (h : IsReduction B A V W) : D₁ ≤ D₂ :=
  (rankCondition_iff_matrix.mp (inferInstance : RankCondition ℂ))
    D₂ D₁ W V h.mul_eq_one

/-- It is enough to state the all-word intertwining equation: its empty-word
case recovers $VW=1$. -/
theorem iff_forall_evalWord :
    IsReduction B A V W ↔
      ∀ w : List (Fin d), V * Kraus.evalWord B w * W = Kraus.evalWord A w := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    simpa using h []

end IsReduction

end MPSTensor
