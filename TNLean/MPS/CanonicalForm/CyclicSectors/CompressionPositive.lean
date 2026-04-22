/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.Compression

/-!
# Positive-length MPV preservation for cyclic-sector compression

This file extracts the positive-length MPV consequence of the supported
compression theorem.

## Main declarations

* `exists_compressedTensor_of_supported_projection_pos_mpv`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D : ℕ}

section CompressionPositiveMPV

/-- A supported-projection compression preserves MPVs at all positive lengths.

This is the usable replacement for a heterogeneous `SameMPV₂` statement: compression changes the
`N = 0` coefficient from `trace 1 = D` to `trace P`, so exact all-length equality is false in
general, but every positive-length MPV is preserved. -/
theorem exists_compressedTensor_of_supported_projection_pos_mpv
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ {N : ℕ}, 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = mpv C σ) := by
  obtain ⟨dim, C, _φ, hdim, hCtp, hCmpv, _hIntertwine, _hMul, _hStar⟩ :=
    exists_compressedTensor_of_supported_projection A P hP hSupp hTP
  refine ⟨dim, C, hdim, hCtp, ?_⟩
  have hleft : ∀ i : Fin d, P * A i = A i := by
    intro i
    calc
      P * A i = P * (P * A i * P) := by rw [hSupp i]
      _ = (P * P) * A i * P := by simp only [Matrix.mul_assoc]
      _ = P * A i * P := by rw [hP.2]
      _ = A i := by simpa [Matrix.mul_assoc] using hSupp i
  have hword :
      ∀ {w : List (Fin d)}, w ≠ [] → P * evalWord A w = evalWord A w := by
    intro w hw
    cases w with
    | nil =>
        cases hw rfl
    | cons i w =>
        calc
          P * evalWord A (i :: w) = P * (A i * evalWord A w) := by rfl
          _ = (P * A i) * evalWord A w := by rw [Matrix.mul_assoc]
          _ = A i * evalWord A w := by rw [hleft i]
          _ = evalWord A (i :: w) := by rfl
  intro N hN σ
  cases N with
  | zero =>
      cases Nat.not_lt_zero _ hN
  | succ n' =>
      have hPw :
          P * evalWord A (List.ofFn σ) = evalWord A (List.ofFn σ) := by
        apply hword
        simpa only [List.ofFn_succ] using
          (List.cons_ne_nil (σ 0) (List.ofFn fun i => σ i.succ))
      calc
        mpv A σ = Matrix.trace (evalWord A (List.ofFn σ)) := by rfl
        _ = Matrix.trace (P * evalWord A (List.ofFn σ)) := by
              exact congrArg Matrix.trace hPw.symm
        _ = mpv C σ := (hCmpv n'.succ σ).symm

end CompressionPositiveMPV

end MPSTensor
