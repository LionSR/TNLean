/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Word

/-!
# Word evaluation for matrix product tensors

A matrix product tensor is a finite family of square matrices. Its word
product is the finite-Kraus word evaluation. This file preserves the
established MPS names for that construction and its basic properties.

## Main declarations

* `MPSTensor` — a `Fin d`-indexed family of $D \times D$ complex matrices
* `MPSTensor.evalWord` — the product associated with a physical word
* `MPSTensor.evalWord_append` — evaluation sends concatenation to multiplication
-/

open scoped Matrix

/-- A periodic translation-invariant matrix product tensor: a family of
$D \times D$ matrices indexed by a physical index in `Fin d`. -/
abbrev MPSTensor (d D : ℕ) := Fin d → Matrix (Fin D) (Fin D) ℂ

namespace MPSTensor

variable {d D : ℕ}

/-- Evaluate a word $w = [i_1, i_2, \ldots, i_n]$ by multiplying the corresponding
matrices $A_{i_1} A_{i_2} \cdots A_{i_n}$. The empty word evaluates to the identity. -/
abbrev evalWord (A : MPSTensor d D) :
    List (Fin d) → Matrix (Fin D) (Fin D) ℂ :=
  Kraus.evalWord A

/-- The empty word evaluates to the identity. -/
@[simp] lemma evalWord_nil (A : MPSTensor d D) : evalWord A [] = 1 :=
  Kraus.evalWord_nil A

/-- The word with head $i$ followed by $w$ evaluates to $A_i$ times the evaluation of $w$. -/
@[simp] lemma evalWord_cons (A : MPSTensor d D) (i : Fin d) (w : List (Fin d)) :
    evalWord A (i :: w) = A i * evalWord A w :=
  Kraus.evalWord_cons A i w

/-- A rectangular matrix that intertwines every letter of two tensors also intertwines
all their word evaluations. -/
lemma evalWord_intertwine {n : ℕ} (A : MPSTensor d D) (B : MPSTensor d n)
    (V : Matrix (Fin D) (Fin n) ℂ) (hInt : ∀ i : Fin d, A i * V = V * B i) :
    ∀ w : List (Fin d), evalWord A w * V = V * evalWord B w :=
  Kraus.evalWord_intertwine A B V hInt

/-- Word evaluation sends concatenation to multiplication. -/
lemma evalWord_append (A : MPSTensor d D) :
    ∀ w₁ w₂ : List (Fin d), evalWord A (w₁ ++ w₂) = evalWord A w₁ * evalWord A w₂ :=
  Kraus.evalWord_append A

/-- If $P$ commutes with every letter of $A$, then it commutes with every evaluated word. -/
lemma commutes_evalWord_of_commutes_letters
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d), P * evalWord A w = evalWord A w * P :=
  Kraus.commutes_evalWord_of_commutes_letters P A hComm

/-- Scaling every tensor matrix by $\zeta$ scales a word product by $\zeta^{|w|}$. -/
lemma evalWord_smul (ζ : ℂ) (A : MPSTensor d D) :
    ∀ w : List (Fin d), evalWord (fun i => ζ • A i) w = (ζ ^ w.length) • evalWord A w :=
  Kraus.evalWord_smul ζ A

/-- Reindex the physical alphabet of a tensor by a map of physical indices. -/
noncomputable abbrev reindexPhysical {d₁ d₂ D : ℕ} (f : Fin d₁ → Fin d₂)
    (A : MPSTensor d₂ D) : MPSTensor d₁ D :=
  Kraus.reindexPhysical f A

/-- Word evaluation after physical reindexing is word evaluation on the mapped word. -/
theorem evalWord_reindexPhysical {d₁ d₂ D : ℕ} (f : Fin d₁ → Fin d₂)
    (A : MPSTensor d₂ D) (w : List (Fin d₁)) :
    evalWord (reindexPhysical f A) w = evalWord A (w.map f) :=
  Kraus.evalWord_reindexPhysical f A w

/-- Cyclicity of trace gives invariance under similarity. -/
lemma trace_conj_eq (X : GL (Fin D) ℂ) (M : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace
        ((X : Matrix (Fin D) (Fin D) ℂ) * M *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
      Matrix.trace M :=
  Kraus.trace_conj_eq X M

end MPSTensor
