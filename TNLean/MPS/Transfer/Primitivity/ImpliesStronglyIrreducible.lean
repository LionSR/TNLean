/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Eigenvalue.EigenspaceMap
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive
import QICLean.Channel.Irreducible.InvariantProjection
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Kraus.Transfer
import TNLean.MPS.Tensor
import QICLean.Kraus.Wielandt.Primitivity.EasyDirections
import TNLean.MPS.Transfer.Primitivity.Definitions

/-!
# Spectral consequences of normality for the transfer map

A normal tensor spreads every nonzero vector to the whole space at one fixed
length (`MPSTensor.exists_vectorSpreadSpan_eq_top_of_isNormal`). This file
states the consequences of that spreading for the transfer map: irreducibility,
and, for a left-canonical tensor, a positive-definite fixed matrix and the
absence of peripheral eigenvalues other than one. The finite-Kraus proofs are in
`QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity` and
`QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive`.

These results are the direction (a) to (c) of Proposition 3 of Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347, stated from the equivalent
clause (b). The proposition itself is `MPSTensor.primitivity_tfae` in
`TNLean.Wielandt.Primitivity.Equivalence`.

## Main results

* `MPSTensor.isIrreducibleMap_transferMap_of_isNormal` and
  `MPSTensor.isIrreducibleFamily_of_isNormal`: a normal tensor is irreducible.
* `MPSTensor.isPrimitive_transferMap_of_isNormal`: the transfer map of a normal
  left-canonical tensor has peripheral spectrum `{1}`.
* `MPSTensor.exists_posDef_fixedPoint_of_isNormal`: it has a positive-definite
  fixed matrix.
* `MPSTensor.exists_vectorSpreadSpan_eq_top_of_isNormal`, `MPSTensor.qIndex_le_iIndex`: Proposition
  3, direction (b) to (a), and the index comparison.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

section EasyDirections

/-!
## Proposition 3, direction (b) to (a), and the index comparison

A normal tensor spreads every nonzero vector to the whole space at one fixed
length, and its primitivity index is at most its full-Kraus-rank index. Neither
statement needs a normalization of the tensor.

### Main results

* `MPSTensor.exists_vectorSpreadSpan_eq_top_of_isNormal`: Proposition 3,
  direction (b) to (a), of arXiv:0909.5347.
* `MPSTensor.qIndex_le_iIndex`: `q(E_A) ≤ i(A)` for a normal tensor.

### References

- Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Propositions 1 and 3.
-/

variable {d D : ℕ}

/-! ## (b)→(a): a full word span spreads every vector -/

/-- **Proposition 3, direction (b)⟹(a)**: if `S_N(A) = M_D(ℂ)` for a positive
`N`, then `H_N(A,φ) = ℂ^D` for every nonzero `φ`.

The hypothesis is clause (b) of the proposition, which is `Kraus.IsNormal A` by
definition; the conclusion is clause (a), written out.

Paper: "(b) ⟹ (a)" in Proposition 3, arXiv:0909.5347. -/
theorem exists_vectorSpreadSpan_eq_top_of_isNormal
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ q : ℕ, 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 → Kraus.vectorSpreadSpan A φ q = ⊤ := by
  obtain ⟨N, hNpos, hN⟩ := hA
  exact ⟨N, hNpos, fun φ hφ => Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top A hN φ hφ⟩

/-! ## Index bound: q(E_A) ≤ i(A) -/

/-- **q(E_A) ≤ i(A)**: the primitivity index is at most the full-Kraus-rank index,
provided the tensor is normal.

This is the normal case of "q(E_A) ≤ i(A)" (arXiv:0909.5347, Proposition 1);
the comparison for every channel is `qIndex_le_iIndex_of_tracePreserving`.

The proof uses `Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top`: since
`Kraus.wordSpan A (iIndex A) = ⊤`, we have `Kraus.vectorSpreadSpan A φ (iIndex A) = ⊤`
for all nonzero φ, so `qIndex A ≤ iIndex A`. -/
theorem qIndex_le_iIndex (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    qIndex A ≤ iIndex A := by
  -- iIndex A lies in the positive full-span set since hA makes it nonempty.
  have hne : {n : ℕ | 0 < n ∧ Kraus.wordSpan A n = ⊤}.Nonempty := by
    obtain ⟨N, hNpos, hN⟩ := hA
    exact ⟨N, hNpos, hN⟩
  have hi : Kraus.wordSpan A (iIndex A) = ⊤ := (Nat.sInf_mem hne).2
  -- iIndex A witnesses that the qIndex-defining set is nonempty
  have hq_mem : iIndex A ∈ {q : ℕ | 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 →
      Kraus.vectorSpreadSpan A φ q = ⊤} := by
    exact ⟨(Nat.sInf_mem hne).1,
      fun φ hφ => Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top A hi φ hφ⟩
  -- qIndex A = sInf of a set containing iIndex A, so qIndex A ≤ iIndex A
  exact Nat.sInf_le hq_mem

end EasyDirections

section ImpliesStronglyIrreducible

variable {d D : ℕ}

/-- The transfer map of a normal tensor has no nontrivial invariant orthogonal
projection. No normalization is needed.

Source: arXiv:0909.5347, Proposition 3, proof of (a)⟹(c). -/
theorem isIrreducibleMap_transferMap_of_isNormal
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
  obtain ⟨q, _, hq⟩ := exists_vectorSpreadSpan_eq_top_of_isNormal A hA
  simpa only using Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A hq

/-- A normal tensor has no nontrivial invariant orthogonal projection. The alphabet is
numbered by `Fintype.equivFin`, where the vector-spreading argument applies; neither notion
depends on the numbering. -/
theorem isIrreducibleFamily_of_isNormal {α : Type*} [Fintype α]
    (A : MPTensor α (Fin D)) (hA : Kraus.IsNormal A) :
    Kraus.IsIrreducibleFamily A := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hr : ∀ N : ℕ, Set.range (fun σ : Fin N → Fin (Fintype.card α) ↦
      Kraus.evalWord (Kraus.reindexPhysical e A) (List.ofFn σ)) =
      Set.range (fun σ : Fin N → α ↦ Kraus.evalWord A (List.ofFn σ)) := by
    intro N
    ext X
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨fun i ↦ e (σ i), by
        simp [Kraus.evalWord_reindexPhysical, List.map_ofFn, Function.comp_def]⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨fun i ↦ e.symm (σ i), by
        simp [Kraus.evalWord_reindexPhysical, List.map_ofFn, Function.comp_def]⟩
  have hN : Kraus.IsNormal (Kraus.reindexPhysical e A) := by
    simpa only [Kraus.IsNormal, Kraus.IsNBlkInjective, Kraus.wordSpan, hr] using hA
  exact (Kraus.isIrreducibleFamily_reindexPhysical_equiv e A).1
    (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (isIrreducibleMap_transferMap_of_isNormal _ hN))

section SpectralPerturbation

/-! ### Step 6: Conclusion — existence of a Hermitian, nonzero, trace-zero E^p-fixed point -/

/-- **From a nontrivial peripheral eigenvector, extract a nonzero Hermitian trace-zero
fixed point of `E^p` that is not positive semidefinite.** -/
theorem exists_hermitian_ne_zero_trace_zero_pow_fixedPoint
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {X : Matrix (Fin D) (Fin D) ℂ} {μ : ℂ}
    (hEig : Kraus.transferMap (ι := Fin d) (n := Fin D) A X = μ • X)
    (hX_ne : X ≠ 0) (hμ_ne : μ ≠ 1) {p : ℕ} (hroot : μ ^ p = 1) :
    ∃ H : Matrix (Fin D) (Fin D) ℂ,
      H.IsHermitian ∧ H ≠ 0 ∧ H.trace = 0 ∧
      ((Kraus.transferMap (ι := Fin d) (n := Fin D) A) ^ p) H = H ∧
      ¬H.PosSemidef := by
  obtain ⟨H, hH, hH_ne, hH_tr, hH_fix⟩ :=
    Kraus.exists_hermitian_ne_zero_trace_zero_pow_fixedPoint
      (Kraus.mapLM A) (Kraus.isChannel_mapLM A hNorm) hEig hX_ne hμ_ne hroot
  refine ⟨H, hH, hH_ne, hH_tr, ?_,
    fun hpsd => hH_ne ((Matrix.PosSemidef.trace_eq_zero_iff hpsd).mp hH_tr)⟩
  simpa only using hH_fix

end SpectralPerturbation

section Construction

/-- The transfer map of a normal left-canonical tensor has no eigenvalue of
modulus one other than one.

Source: arXiv:0909.5347, Proposition 3, (b)⟹(a)⟹(c); Wolf, Theorem 6.7. -/
theorem isPrimitive_transferMap_of_isNormal [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : Kraus.IsNormal A) :
    IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
  obtain ⟨q, _, hq⟩ := exists_vectorSpreadSpan_eq_top_of_isNormal A hA
  simpa only using
    Kraus.isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top A hNorm hq

/-- The transfer map of a normal left-canonical tensor has a positive-definite
fixed matrix.

Source: arXiv:0909.5347, Proposition 3, (b)⟹(a)⟹(c). -/
theorem exists_posDef_fixedPoint_of_isNormal [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : Kraus.IsNormal A) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosDef ∧ Kraus.transferMap (ι := Fin d) (n := Fin D) A ρ = ρ := by
  obtain ⟨q, _, hq⟩ := exists_vectorSpreadSpan_eq_top_of_isNormal A hA
  obtain ⟨ρ, hρ_pd, hρ_fix⟩ :=
    Kraus.exists_posDef_fixedPoint_of_isTP_of_vectorSpreadSpan_eq_top A hNorm hq
  exact ⟨ρ, hρ_pd, by simpa only using hρ_fix⟩

end Construction

end ImpliesStronglyIrreducible

end MPSTensor
