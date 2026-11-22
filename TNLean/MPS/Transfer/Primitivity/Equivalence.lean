/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.FromSpectral
import TNLean.MPS.Transfer.Primitivity.EasyDirections
import TNLean.MPS.Transfer.Primitivity.ImpliesStronglyIrreducible
import TNLean.MPS.Transfer.Primitivity.StronglyIrreducibleToFullRank
import TNLean.MPS.Tensor

/-!
# Proposition 3 of the quantum Wielandt paper

Sanz, Pérez-García, Wolf and Cirac, *A quantum version of Wielandt's inequality*
(arXiv:0909.5347, Section II) introduce three properties of a quantum channel
`E_A` and prove them equivalent (Proposition 3, `prop:equiv`;
`Papers/0909.5347/main.tex`, lines 403–430 and 501–509):

* **(a)** primitivity: there is `q ≥ 1` with `H_q(A,φ) = ℂ^D` for every `φ ≠ 0`;
* **(b)** eventually full Kraus rank: there is `n ≥ 1` with `S_n(A) = M_D(ℂ)`;
* **(c)** strong irreducibility: `E_A` has a unique eigenvalue of modulus one,
  and the corresponding eigenvector is positive definite.

`MPSTensor.primitivity_tfae` is this proposition, with the source's
hypotheses and each clause written out. The library has no predicate for any of
the three: clause (b) is `Kraus.IsNormal A` by definition, and the peripheral
part of clause (c) is `IsPrimitive (Kraus.transferMap A)`.

The three implications closing the cycle are **(b) → (a)**
(`exists_vectorSpreadSpan_eq_top_of_isNormal`), **(a) → (c)** (the finite-Kraus
results of `QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive`), and
**(c) → (b)** (`isNormal_of_isIrreducibleMap_of_isPrimitive`, after
`isIrreducibleMap_of_channel_posDef_fixedPoint_unique` derives irreducibility
from the literal clause).

## Main results

* `MPSTensor.primitivity_tfae`: Proposition 3 of arXiv:0909.5347.
* `MPSTensor.exists_hasComplementaryFixedPointGap_posDef_of_isNormal`: a normal left-canonical
  tensor has a complementary fixed-point gap at a positive-definite fixed matrix.
* `MPSTensor.qIndex_le_iIndex_of_tracePreserving`: Proposition 1 of the source.
* `MPSTensor.wolf_theorem_6_15`: uniqueness of the full-rank fixed point.

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347](https://arxiv.org/abs/0909.5347), Proposition 3
- Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6, Theorems 6.7
  and 6.8
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ}

/-! ## The complementary gap of a normal tensor -/

/-- A normal left-canonical tensor has a complementary fixed-point gap at a
positive-definite fixed matrix.

Source: arXiv:0909.5347, Proposition 3, (b)⟹(c); Wolf, Chapter 6, Theorem 6.7. -/
theorem exists_hasComplementaryFixedPointGap_posDef_of_isNormal [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : Kraus.IsNormal A) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, Kraus.HasComplementaryFixedPointGap A ρ ∧ ρ.PosDef :=
  exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive A hNorm
    (isIrreducibleMap_transferMap_of_isNormal A hA)
    (isPrimitive_transferMap_of_isNormal A hNorm hA)

/-! ## Proposition 3 -/

/-- **Proposition 3 of arXiv:0909.5347.** For a left-canonical tensor `A` of
positive bond dimension, with transfer map `E_A`, the following are equivalent:

* (a) `E_A` is *primitive*: there is `q ≥ 1` such that `H_q(A,φ) = ℂ^D` for
  every nonzero `φ`;
* (b) `E_A` has *eventually full Kraus rank*: there is `n ≥ 1` with
  `S_n(A) = M_D(ℂ)`;
* (c) `E_A` is *strongly irreducible*: it has a positive-definite fixed matrix
  `ρ` spanning the fixed eigenspace, and no eigenvalue of modulus one other
  than one.

Clause (b) is `Kraus.IsNormal A` by definition. Clause (c) is the source's
literal one: no irreducibility of `E_A` is assumed, it follows.

Source: arXiv:0909.5347, the three definitions at
`Papers/0909.5347/main.tex`, lines 403–430, and Proposition 3 (`prop:equiv`),
lines 501–509. The equivalence of (b) and (c) is also Wolf, *Quantum Channels &
Operations*, Theorems 6.7 and 6.8. -/
theorem primitivity_tfae [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    List.TFAE [
      ∃ q : ℕ, 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 → Kraus.vectorSpreadSpan A φ q = ⊤,
      ∃ n : ℕ, 0 < n ∧ Kraus.wordSpan A n = ⊤,
      ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosDef ∧
        Kraus.transferMap (ι := Fin d) (n := Fin D) A ρ = ρ ∧
        (∀ σ : Matrix (Fin D) (Fin D) ℂ,
          Kraus.transferMap (ι := Fin d) (n := Fin D) A σ = σ → ∃ c : ℂ, σ = c • ρ) ∧
        IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A)] := by
  tfae_have 2 → 1 := exists_vectorSpreadSpan_eq_top_of_isNormal A
  tfae_have 1 → 3 := by
    rintro ⟨q, -, hq⟩
    have hIrr : IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
      simpa only using Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A hq
    have hPrim : IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A) := by
      simpa only using
        Kraus.isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top A hNorm hq
    obtain ⟨ρ, hP, hρ⟩ :=
      exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive A hNorm hIrr
        hPrim
    exact ⟨ρ, hρ, hP.fixedPoint_is_fixed,
      fun σ hσ ↦ ⟨Matrix.trace σ / Matrix.trace ρ, hP.fixedPoint_unique σ hσ⟩, hPrim⟩
  tfae_have 3 → 2 := by
    rintro ⟨ρ, hρ, hfix, hunique, hPrim⟩
    exact isNormal_of_isIrreducibleMap_of_isPrimitive A hNorm
      (isIrreducibleMap_of_channel_posDef_fixedPoint_unique
        (Kraus.transferMap A) (Kraus.isChannel_mapLM A hNorm) ρ hρ hfix
        (fun σ _ hσ ↦ hunique σ hσ)) hPrim
  tfae_finish

/-! ## Proposition 1 -/

/-- The primitivity index of every trace-preserving channel is at most its
full-Kraus-rank index, including the nonprimitive case, where both indices
use the zero convention. Source: arXiv:0909.5347, Proposition 1 (`prop:iq`),
lines 447–449. -/
theorem qIndex_le_iIndex_of_tracePreserving [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    qIndex A ≤ iIndex A := by
  by_cases hA : Kraus.IsNormal A
  · exact qIndex_le_iIndex A hA
  · have hq : {q : ℕ | 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 →
        Kraus.vectorSpreadSpan A φ q = ⊤} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hab := (primitivity_tfae A hNorm).out 1 2
      exact hA (hab.mp ⟨q, hq⟩)
    rw [qIndex, hq, Nat.sInf_empty]
    exact Nat.zero_le _

/-! ## Wolf Theorem 6.15 -/

/-- **Wolf Theorem 6.15 (Unique fixed points of full rank)**: let `A` be a
normalized MPS tensor (`∑ᵢ Aᵢ† Aᵢ = 1`) that is normal, i.e.
homogeneous words of the Kraus operators `Aᵢ` of some length span the entire
matrix algebra `M_D(ℂ)`. Then there exists a unique positive definite density
matrix `ρ` such that every fixed point of the transfer map `E_A` is a scalar
multiple of `ρ`, i.e. the fixed point set is proportional to `ρ`.

Paper: Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6, Theorem
6.15; local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
statement lines 1517--1527, proof lines 1529--1538.

The source proves this by passing to `T^n`, showing every `T^n(|ψ⟩⟨ψ|)` has
full rank from the span hypothesis, concluding no stationary density has a
kernel, and ruling out a fixed-point space of dimension larger than one via
Corollary 6.5. This proof instead routes through Proposition 3
(arXiv:0909.5347): `exists_hasComplementaryFixedPointGap_posDef_of_isNormal` turns the span
hypothesis into a positive-definite fixed point `ρ₀` with a complementary
transfer-map gap around it, and that gap
(`Kraus.HasComplementaryFixedPointGap.fixedPoint_unique`) forces every fixed point of `E_A` to be
a scalar multiple of `ρ₀`; rescaling by the inverse trace gives the unique
density-matrix representative. Both routes are Wolf's own Chapter 6 machinery;
this one reuses the already-formalized Proposition 3 equivalence rather than
repeating the `T^n` / Corollary 6.5 argument. -/
theorem wolf_theorem_6_15 [NeZero D] (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hSpan : Kraus.IsNormal A) :
    ∃! ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ ∈ densityMatrices D ∧ ρ.PosDef ∧
      Kraus.transferMap (ι := Fin d) (n := Fin D) A ρ = ρ ∧
      ∀ σ : Matrix (Fin D) (Fin D) ℂ,
        Kraus.transferMap (ι := Fin d) (n := Fin D) A σ = σ → ∃ c : ℂ, σ = c • ρ := by
  obtain ⟨ρ₀, hPrim, hρ₀pd⟩ :=
    exists_hasComplementaryFixedPointGap_posDef_of_isNormal A hNorm hSpan
  have htr_pos : 0 < Matrix.trace ρ₀ := hρ₀pd.trace_pos
  have htr_ne : Matrix.trace ρ₀ ≠ 0 := ne_of_gt htr_pos
  set ρ := (Matrix.trace ρ₀)⁻¹ • ρ₀ with hρ_def
  have hρpd : ρ.PosDef := hρ₀pd.smul (inv_pos.mpr htr_pos)
  have hρ_trace : Matrix.trace ρ = 1 := by
    rw [hρ_def, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr_ne]
  have hρ_fix : Kraus.transferMap (ι := Fin d) (n := Fin D) A ρ = ρ := by
    rw [hρ_def, LinearMap.map_smul, hPrim.fixedPoint_is_fixed]
  have hunique : ∀ σ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.transferMap (ι := Fin d) (n := Fin D) A σ = σ → ∃ c : ℂ, σ = c • ρ := by
    intro σ hσ
    refine ⟨Matrix.trace σ, ?_⟩
    calc σ = (Matrix.trace σ / Matrix.trace ρ₀) • ρ₀ := hPrim.fixedPoint_unique σ hσ
      _ = Matrix.trace σ • ((Matrix.trace ρ₀)⁻¹ • ρ₀) := by rw [smul_smul, div_eq_mul_inv]
      _ = Matrix.trace σ • ρ := by rw [hρ_def]
  refine ⟨ρ, ⟨⟨hρpd.posSemidef, hρ_trace⟩, hρpd, hρ_fix, hunique⟩, ?_⟩
  rintro ρ' ⟨⟨_, hρ'_trace⟩, _, hρ'_fix, _⟩
  obtain ⟨c, hc⟩ := hunique ρ' hρ'_fix
  have hc1 : c = 1 := by
    have htr := congrArg Matrix.trace hc
    rw [Matrix.trace_smul, smul_eq_mul, hρ_trace, mul_one, hρ'_trace] at htr
    exact htr.symm
  rw [hc, hc1, one_smul]

end MPSTensor
