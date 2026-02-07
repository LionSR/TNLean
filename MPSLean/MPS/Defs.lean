import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped Matrix

/-- A (periodic, translation-invariant) MPS tensor: a family of `D×D` matrices indexed by a
physical index in `Fin d`. -/
abbrev MPSTensor (d D : ℕ) := Fin d → Matrix (Fin D) (Fin D) ℂ

namespace MPSTensor

open scoped BigOperators

variable {d D : ℕ}

/-- Evaluate a word `w = [i₁, i₂, …, iₙ]` by multiplying the corresponding matrices
`A i₁ * A i₂ * ⋯ * A iₙ`. Returns `1` for the empty word. -/
def evalWord (A : MPSTensor d D) : List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | [] => 1
  | i :: w => A i * evalWord A w

/-- Word evaluation respects concatenation:
`evalWord A (w1 ++ w2) = evalWord A w1 * evalWord A w2`. -/
lemma evalWord_append (A : MPSTensor d D) :
    ∀ w1 w2 : List (Fin d), evalWord A (w1 ++ w2) = evalWord A w1 * evalWord A w2 := by
  intro w1 w2
  induction w1 with
  | nil =>
      simp [evalWord]
  | cons i w1 ih =>
      simp [evalWord, ih, Matrix.mul_assoc]

/-- The MPV coefficient for a word `w`, given by `trace (evalWord A w)`. -/
def coeff (A : MPSTensor d D) (w : List (Fin d)) : ℂ :=
  Matrix.trace (evalWord A w)

/-- The Matrix Product Vector (MPV) for system size `N`: for each basis state
`σ : Fin N → Fin d`, this returns the coefficient
`trace (A (σ 0) * A (σ 1) * ⋯ * A (σ (N-1)))`. -/
def mpv (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) : ℂ :=
  coeff A (List.ofFn σ)

/-- Gauge equivalence: `A` and `B` are related by simultaneous similarity
`B i = X * A i * X⁻¹` for some `X ∈ GL(D,ℂ)`. -/
def GaugeEquiv (A B : MPSTensor d D) : Prop :=
  ∃ X : GL (Fin D) ℂ, ∀ i : Fin d, B i = X * A i * X⁻¹

/-- Two tensors generate the same MPV family if they produce the same coefficient for every
system size `N` and every basis configuration `σ : Fin N → Fin d`. -/
def SameMPV (A B : MPSTensor d D) : Prop :=
  ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ

end MPSTensor
