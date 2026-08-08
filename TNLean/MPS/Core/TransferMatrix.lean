/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.TransferMatrix
import TNLean.MPS.Core.Transfer

/-!
# Transfer-matrix representation of MPS transfer maps

This file relates the generic transfer matrix of a linear map to the transfer
map associated with an MPS tensor.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-- The MPS transfer map `E_A(X) = ∑ᵢ Aᵢ X Aᵢ†` has transfer matrix
`∑ᵢ Āᵢ ⊗ₖ Aᵢ`.

This relates Wolf's Section 2.2 transfer matrix for quantum channels to the MPS
transfer operator. -/
theorem transferMatrix_eq (A : MPSTensor d D) :
    transferMatrix (MPSTensor.transferMap A) =
      ∑ n : Fin d,
        (A n).map (starRingEnd ℂ) ⊗ₖ A n :=
  transferMatrix_kraus A _ (fun X => by simp [transferMap_apply])

end MPSTensor
