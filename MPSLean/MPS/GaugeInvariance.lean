import MPSLean.MPS.Defs

open scoped Matrix

namespace MPSTensor

open scoped BigOperators

variable {d D : ℕ}

section

variable {A B : MPSTensor d D}

/-- Helper lemma: if `X ∈ GL(D,ℂ)` then (viewed as matrices) we have `(X⁻¹) * X = 1`. -/
lemma coe_inv_mul (X : GL (Fin D) ℂ) :
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  simp

/-- Helper lemma: if `X ∈ GL(D,ℂ)` then (viewed as matrices) we have `X * (X⁻¹) = 1`. -/
lemma coe_mul_inv (X : GL (Fin D) ℂ) :
    (X : Matrix (Fin D) (Fin D) ℂ) * ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  simp

/-- If `B i = X * A i * X⁻¹`, then word evaluation is conjugated:
`evalWord B w = X * evalWord A w * X⁻¹`. -/
lemma evalWord_gauge (X : GL (Fin D) ℂ)
    (hX :
      ∀ i : Fin d,
        B i =
          (X : Matrix (Fin D) (Fin D) ℂ) * A i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ w : List (Fin d),
      evalWord B w =
        (X : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  | [] => by
      simp [evalWord]
  | i :: w => by
      -- Expand the recursive definition and use the induction hypothesis.
      simp [evalWord, hX, evalWord_gauge X hX w, Matrix.mul_assoc]

/-- Cyclicity of trace gives invariance under similarity:
`trace (X * M * X⁻¹) = trace M` for `X ∈ GL`. -/
lemma trace_conj_eq (X : GL (Fin D) ℂ) (M : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace
        ((X : Matrix (Fin D) (Fin D) ℂ) * M *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
      Matrix.trace M := by
  -- One cyclic shift turns `X * M * X⁻¹` into `X⁻¹ * X * M`, then `X⁻¹ * X = 1`.
  simpa [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle (X : Matrix (Fin D) (Fin D) ℂ) M
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))

/-- Gauge equivalent tensors generate the same MPV family. -/
theorem GaugeEquiv.sameMPV {A B : MPSTensor d D} : GaugeEquiv A B → SameMPV A B := by
  rintro ⟨X, hX⟩
  intro N σ
  -- Unfold the MPV coefficient into a trace of a word evaluation.
  simp only [mpv, coeff]
  -- Rewrite `evalWord B` as a conjugation of `evalWord A`.
  have hw := evalWord_gauge (A := A) (B := B) X hX (List.ofFn σ)
  rw [hw]
  -- Now use cyclicity of trace to remove the conjugation.
  simpa using (trace_conj_eq X (evalWord A (List.ofFn σ))).symm

end

end MPSTensor
