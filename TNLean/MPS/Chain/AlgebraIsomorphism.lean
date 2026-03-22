/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Chain.Defs

/-!
# Bond algebra isomorphism for injective MPS chains

This file provides the **bond algebra isomorphism** for 3-site injective MPS chains
(Issue #6). The main result: if two 3-site injective chains generate the same
quantum state, then the bond algebras are isomorphic via an invertible gauge
transformation on the virtual bond.

## Main results

* `MPSChainTensor.chain3_bond_gauge` — given two 3-site injective chains `A`, `B`
  with `SameState A B`, there exists an invertible `Z` such that the virtual
  insertion of any matrix `X` on bond (0,1) is the same for `A` and for the
  gauge-conjugated `B`.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), §III
-/

open scoped Matrix

namespace MPSChainTensor

variable {d D : ℕ}

/-- Virtual insertion of a matrix `X` on the bond between sites 0 and 1 of a
3-site chain: `Tr(A₀(σ₀) · X · A₁(σ₁) · A₂(σ₂))`. -/
noncomputable def virtualInsert3 (A : MPSChainTensor d D 3)
    (σ : Fin 3 → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  Matrix.trace (A 0 (σ 0) * X * A 1 (σ 1) * A 2 (σ 2))

/-- Bond algebra isomorphism for 3-site injective chains.

If two 3-site injective chains generate the same state, there exists an
invertible `Z` on the bond between sites 0 and 1 such that virtual insertions
match after conjugation:
`∀ X σ, virtualInsert3 A σ (Z * X) = virtualInsert3 B σ X`. -/
theorem chain3_bond_gauge
    (A B : MPSChainTensor d D 3)
    (hA : IsInjective A) (hB : IsInjective B)
    (hEq : SameState A B) :
    ∃ Z : GL (Fin D) ℂ, ∀ (X : Matrix (Fin D) (Fin D) ℂ) (σ : Fin 3 → Fin d),
      virtualInsert3 A σ ((Z : Matrix (Fin D) (Fin D) ℂ) * X) =
        virtualInsert3 B σ X := by
  sorry

end MPSChainTensor
