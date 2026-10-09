/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs

/-!
# Word evaluation of a sandwiched tensor

For matrices `A : Matrix (Fin D') (Fin D) ℂ` and `B : Matrix (Fin D) (Fin D') ℂ` with
`B * A = 1`, the tensor with letters `A U^{ij} B` evaluates every nonempty word to
`A U^{i₁j₁} ⋯ U^{iₙjₙ} B`, by telescoping. Bond similarities (`A`, `B` square and mutually
inverse) and the adjunction of unused bond directions (`A` an isometry, `B = Aᴴ`) are instances.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Proposition IV.5, lines 773--804,
  and Definitions IV.3 and IV.4, lines 706--724.
-/

namespace MPOTensor

variable {d D D' : ℕ}

/-- Word evaluation commutes with a rectangular sandwich `U ↦ A U B` with `B * A = 1`, on every
word with a nonempty first component.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804, and Definitions IV.3 and IV.4,
lines 706--724. -/
theorem evalWord_sandwich (A : Matrix (Fin D') (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin D') ℂ) (hBA : B * A = 1) :
    ∀ is js : List (Fin d), is ≠ [] →
      evalWord (fun i j ↦ A * U i j * B : MPOTensor d D') is js = A * evalWord U is js * B
  | [], _, h => absurd rfl h
  | _ :: _, [], _ => by simp [evalWord]
  | [_], _ :: js, _ => by cases js <;> simp [evalWord]
  | i :: i' :: is, j :: js, _ => by
    rw [evalWord_cons, evalWord_sandwich A U B hBA (i' :: is) js (List.cons_ne_nil _ _),
      evalWord_cons]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]

end MPOTensor
