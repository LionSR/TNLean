import TNLean.MPS.Chain.VirtualInsertion
import TNLean.MPS.Structure.LinearExtension
import TNLean.Algebra.SkolemNoether

/-!
# Algebra isomorphism on the virtual bond for equal 3-site injective chains

This file introduces the chain-level bond gauge statement used in Stage 2.
The proof is intended to follow the direct trace-pairing construction route
(via `virtualInsertCoeff` identities), avoiding `physRealize_mul`.
TODO: replace this interface axiom with the direct trace-pairing proof.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Bond-gauge form for two 3-site injective chains with equal coefficients.

If two length-3 chains `A` and `B` are sitewise injective and have equal physical
coefficients on every configuration, then virtual insertion on the middle bond is
related by conjugation with a single invertible matrix. -/
axiom virtual_bond_gauge
    (A B : Fin 3 → MPSTensor d D)
    (hA : ∀ k, IsInjective (A k)) (hB : ∀ k, IsInjective (B k))
    (hEq : ∀ σ : Fin 3 → Fin d,
      Matrix.trace (Fin.prod fun k => A k (σ k)) =
      Matrix.trace (Fin.prod fun k => B k (σ k))) :
    ∃ Z : GL (Fin D) ℂ, ∀ (X : Matrix (Fin D) (Fin D) ℂ) (σ : Fin 3 → Fin d),
      virtualInsertCoeff (A 0) (A 1) (A 2) σ X =
      virtualInsertCoeff (B 0) (B 1) (B 2) σ (Z⁻¹ * X * Z)

end MPSTensor
