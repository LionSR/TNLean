/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Injectivity
import TNLean.MPS.Core.Word

/-!
# Injectivity and normality of matrix product tensors

The injectivity and normality predicates for a matrix product tensor are the
corresponding finite-family predicates. This file preserves their established
MPS names.

## Main declarations

* `MPSTensor.IsInjective`: the one-site matrices span the full matrix algebra
* `MPSTensor.IsNBlkInjective`: words of length $N$ span the full matrix algebra
* `MPSTensor.IsNormal`: block injectivity holds at some positive length
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Algebraic injectivity: the tensor matrices span the full matrix algebra. -/
def IsInjective (A : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  Submodule.span ℂ (Set.range A) = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))

/-- The span of an injective tensor's matrices is the full matrix algebra. -/
lemma IsInjective.span_eq_top {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : IsInjective A) :
    Submodule.span ℂ (Set.range A) = ⊤ :=
  Kraus.IsInjective.span_eq_top hA

/-- Multiplication of every tensor matrix by a nonzero scalar preserves injectivity. -/
theorem IsInjective.smul
    {c : ℂ} {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : IsInjective A) (hc : c ≠ 0) :
    IsInjective (fun i ↦ c • A i) :=
  Kraus.IsInjective.smul hA hc

/-- An injective tensor with nonzero bond dimension has nonzero physical dimension. -/
theorem neZero_d_of_isInjective {A : Fin d → Matrix (Fin D) (Fin D) ℂ} [NeZero D]
    (hA : IsInjective A) : NeZero d :=
  Kraus.neZero_d_of_isInjective hA

/-- Block injectivity: words of length $N$ span the full matrix algebra. -/
def IsNBlkInjective (A : Fin d → Matrix (Fin D) (Fin D) ℂ) (N : ℕ) : Prop :=
  Kraus.wordSpan A N = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ))

/-- The literal-span form of block injectivity. -/
theorem IsNBlkInjective.span_eq_top {A : Fin d → Matrix (Fin D) (Fin D) ℂ} {N : ℕ}
    (hA : IsNBlkInjective A N) :
    Submodule.span ℂ (Set.range fun σ : Fin N → Fin d => Kraus.evalWord A (List.ofFn σ)) = ⊤ :=
  Kraus.IsNBlkInjective.span_eq_top hA

/-- Normality means block injectivity at some positive word length. -/
def IsNormal (A : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ IsNBlkInjective (d := d) (D := D) A N

@[simp] lemma isNormal_iff (A : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    IsNormal A ↔ ∃ N, 0 < N ∧ IsNBlkInjective A N := Iff.rfl

/-- Algebraic injectivity gives one-block injectivity. -/
theorem isNBlkInjective_one_of_isInjective {A : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (h : IsInjective A) : IsNBlkInjective A 1 :=
  Kraus.isNBlkInjective_one_of_isInjective h

/-- Algebraic injectivity implies normality. -/
lemma IsInjective.isNormal {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (h : IsInjective A) :
    IsNormal A :=
  Kraus.IsInjective.isNormal h

end MPSTensor
