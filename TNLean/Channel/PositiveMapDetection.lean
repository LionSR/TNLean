/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.EntanglementWitness
import TNLean.Channel.Schwarz.ChoiCompression

/-!
# Positive maps from entanglement witnesses (Wolf Proposition 3.4)

Wolf's Chapter 3, Section 3.2 (Proposition 3.4) detects a bipartite state of Schmidt
number larger than `n` by an `n`-positive map: through the Choi–Jamiołkowski
correspondence, the entanglement witness of Proposition 3.3 becomes the Choi matrix of an
`n`-positive map under which the state fails to stay positive semidefinite.

This file supplies the two correspondence steps that turn the witness into an
`n`-positive map.

## The Choi correspondence as a linear isomorphism

The Choi map `T ↦ τ = (T ⊗ id)(|Ω⟩⟨Ω|)` is a complex-linear map between the
superoperator space `M_D(ℂ) → M_D(ℂ)` and the bipartite matrix space
`M_{D·D}(ℂ)`.  Both spaces have complex dimension `D⁴`, and the map is injective
(`ChoiJamiolkowski.choiMatrix_injective`), hence surjective: every bipartite matrix is the
Choi matrix of a unique superoperator.  In particular the Hermitian witness `W` is the
Choi matrix of some superoperator `T`.

## The witness condition as the `n`-positivity criterion

The `n`-positivity criterion
`ChoiJamiolkowski.isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg`
phrases `n`-positivity of `T` as nonnegativity of the Choi quadratic form
`⟨ψ| τ |ψ⟩ = star ψ ⬝ᵥ (τ *ᵥ ψ)` over vectors ψ of Schmidt rank at most `n`.  For `τ = W`
this quadratic form equals the witness expectation `Re tr(W |ψ⟩⟨ψ|)` (a real number, `W`
being Hermitian), which the witness condition makes nonnegative.  So the superoperator
whose Choi matrix is the witness is `n`-positive.

## Detection through the trace-pairing adjoint

The entanglement witness has negative expectation `Re tr(W ρ)` on ρ.  Writing `W = τ_T`
and pushing `T` across the trace pairing of the ampliation onto its trace-pairing adjoint
`T*` (`Matrix.trace_traceAdjointMap_mul`) turns this expectation into the Choi-vector
quadratic form of the ampliation of `T*`:

  `tr(W ρ) = ⟨Ω| (T* ⊗ id)(ρ) |Ω⟩`.

The trace-pairing adjoint of an `n`-positive map is again `n`-positive
(`IsNPositiveMap.traceAdjointMap`), so `T*` is the `n`-positive map detecting ρ: the
negative real part of `tr(W ρ)` forces `⟨Ω| (T* ⊗ id)(ρ) |Ω⟩` to have negative real part,
which a positive semidefinite matrix cannot, so `(T* ⊗ id)(ρ)` is not positive
semidefinite.

## Main results

* `ChoiJamiolkowski.exists_choiMatrix_eq`: **the Choi map is surjective** — every bipartite
  matrix is the Choi matrix of a superoperator.
* `ChoiJamiolkowski.exists_isNPositiveMap_choiMatrix_eq_of_witness`: **a Schmidt-`n` witness
  is the Choi matrix of an `n`-positive map**, the Choi–Jamiołkowski translation of the
  entanglement witness into an `n`-positive map.
* `ChoiJamiolkowski.trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap`: the
  trace pairing of the Choi matrix with ρ equals the Choi-vector quadratic form of the
  trace-pairing-adjoint ampliation.
* `Matrix.exists_isNPositiveMap_tensorMapId_not_posSemidef`: **Wolf Proposition 3.4 (if
  direction)** — a trace-one Hermitian state of Schmidt number larger than `n` is detected
  by an `n`-positive map whose ampliation makes the state not positive semidefinite.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Section 3.2, Proposition 3.4][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder
open Matrix

namespace ChoiJamiolkowski

variable {D : ℕ}

/-! ## Surjectivity of the Choi map -/

/-- **The Choi map is surjective.**  Every bipartite matrix `W` on `M_{D·D}(ℂ)` is the
Choi matrix `(T ⊗ id)(|Ω⟩⟨Ω|)` of some superoperator `T : M_D(ℂ) → M_D(ℂ)`.

The Choi map is complex-linear (`choiMatrixLinearMap`) and injective
(`choiMatrix_injective`); its domain (superoperators on `M_D(ℂ)`) and codomain
(bipartite matrices on `M_{D·D}(ℂ)`) have equal complex dimension `D⁴`, so injectivity
forces surjectivity. -/
theorem exists_choiMatrix_eq [NeZero D]
    (W : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    ∃ T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ, choiMatrix T = W := by
  -- Domain and codomain have equal complex dimension `D⁴`.
  have hdom :
      Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
        = D ^ 4 := by
    rw [Module.finrank_linearMap, Module.finrank_matrix, Module.finrank_self,
      Fintype.card_fin, mul_one]
    ring
  have hcod :
      Module.finrank ℂ (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) = D ^ 4 := by
    rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_prod, Fintype.card_fin,
      mul_one]
    ring
  have hdim :
      Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
        = Module.finrank ℂ (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := by
    rw [hdom, hcod]
  -- `choiMatrixLinearMap` is injective, so (equal finite dimensions) surjective.
  have hinj : Function.Injective (choiMatrixLinearMap (D := D)) := choiMatrix_injective
  have hsurj : Function.Surjective (choiMatrixLinearMap (D := D)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  obtain ⟨T, hT⟩ := hsurj W
  exact ⟨T, hT⟩

/-! ## The witness as the Choi matrix of an `n`-positive map -/

/-- The witness expectation on a pure-state projector equals the Choi quadratic form: for
any matrix `W` and any vector ψ,

  `tr(W |ψ⟩⟨ψ|) = star ψ ⬝ᵥ (W *ᵥ ψ)`.

This is the algebraic identity matching the entanglement-witness condition to the Choi
`n`-positivity criterion. -/
theorem trace_mul_vecMulVec_eq_dotProduct
    (W : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (ψ : Fin D × Fin D → ℂ) :
    (W * Matrix.vecMulVec ψ (star ψ)).trace = star ψ ⬝ᵥ (W *ᵥ ψ) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- **A Schmidt-`n` entanglement witness is the Choi matrix of an `n`-positive map.**
A Hermitian operator `W` whose expectation on every pure state of Schmidt rank at most `n`
is nonnegative is the Choi matrix `(T ⊗ id)(|Ω⟩⟨Ω|)` of an `n`-positive map `T`.

This is the Choi–Jamiołkowski translation of the entanglement-witness criterion (Wolf
Proposition 3.3) into an `n`-positive map (the map of Wolf Proposition 3.4).  Surjectivity
of the Choi map (`exists_choiMatrix_eq`) gives a superoperator `T` with `choiMatrix T = W`;
the witness condition `0 ≤ Re tr(W |ψ⟩⟨ψ|)`, which on the Hermitian `W` is the full
(real, nonnegative) Choi quadratic form `0 ≤ star ψ ⬝ᵥ (W *ᵥ ψ)`, is exactly the
`n`-positivity criterion for `T`. -/
theorem exists_isNPositiveMap_choiMatrix_eq_of_witness [NeZero D] {n : ℕ}
    {W : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ} (hWherm : W.IsHermitian)
    (hWpos : ∀ ψ : Fin D × Fin D → ℂ, Matrix.HasSchmidtRankLE n ψ →
      0 ≤ (W * Matrix.vecMulVec ψ (star ψ)).trace.re) :
    ∃ T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      IsNPositiveMap n T ∧ choiMatrix T = W := by
  obtain ⟨T, hT⟩ := exists_choiMatrix_eq W
  refine ⟨T, ?_, hT⟩
  rw [isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg]
  intro ψ hψ
  -- The Choi quadratic form for ψ is the witness expectation, a nonnegative real.
  rw [hT]
  have hreal : (W * Matrix.vecMulVec ψ (star ψ)).trace = star ψ ⬝ᵥ (W *ᵥ ψ) :=
    trace_mul_vecMulVec_eq_dotProduct W ψ
  -- `star ψ ⬝ᵥ (W *ᵥ ψ)` is real (W Hermitian) with nonnegative real part.
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · rw [← hreal]; exact hWpos ψ hψ
  · -- The imaginary part vanishes since `W` is Hermitian.
    have him := hWherm.im_star_dotProduct_mulVec_self ψ
    simp only [RCLike.im_to_complex] at him
    rw [him]

/-! ## Detection through the trace-pairing adjoint -/

/-- The trace pairing of the Choi matrix with ρ is the Choi-vector quadratic form of the
trace-pairing-adjoint ampliation:

  `tr(τ_T ρ) = ⟨Ω| (T* ⊗ id)(ρ) |Ω⟩`.

Here `T*` is the trace-pairing adjoint (`Matrix.traceAdjointMap`).  The identity moves `T`
across the trace pairing of its `id`-ampliation (`Matrix.trace_traceAdjointMap_mul`,
together with `nPositiveAmpliation_traceAdjointMap`) and reads the result as the quadratic
form of `(T* ⊗ id)(ρ)` on the maximally entangled vector, using
`τ_T = (T ⊗ id)(|Ω⟩⟨Ω|)` and `|Ω⟩⟨Ω| = |Ω⟩⟨Ω|`. -/
theorem trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    (choiMatrix T * ρ).trace
      = star (omegaVec D) ⬝ᵥ (tensorMapId (Matrix.traceAdjointMap T) ρ *ᵥ omegaVec D) := by
  -- `tr(τ_T ρ) = tr(ρ (T ⊗ id)(|Ω⟩⟨Ω|))`.
  have h1 : (choiMatrix T * ρ).trace = (ρ * tensorMapId T (omegaProj D)).trace := by
    rw [choiMatrix, Matrix.trace_mul_comm]
  -- Move `T` onto its trace-pairing adjoint across the ampliation trace pairing.
  have h2 : (ρ * tensorMapId T (omegaProj D)).trace
      = (tensorMapId (Matrix.traceAdjointMap T) ρ * omegaProj D).trace := by
    rw [tensorMapId_eq_nPositiveAmpliation T (omegaProj D),
      show tensorMapId (Matrix.traceAdjointMap T) ρ
          = nPositiveAmpliation D (Matrix.traceAdjointMap T) ρ from
        tensorMapId_eq_nPositiveAmpliation _ _,
      nPositiveAmpliation_traceAdjointMap,
      Matrix.trace_traceAdjointMap_mul (nPositiveAmpliation D T) ρ (omegaProj D),
      Matrix.trace_mul_comm]
  -- `tr(Y |Ω⟩⟨Ω|) = ⟨Ω| Y |Ω⟩`.
  rw [h1, h2, omegaProj, trace_mul_vecMulVec_eq_dotProduct]

end ChoiJamiolkowski

namespace Matrix

open ChoiJamiolkowski

/-- **Positive maps detect high Schmidt number** (Wolf §3.2, Proposition 3.4, if
direction).  A trace-one Hermitian bipartite state ρ on `ℂ^D ⊗ ℂ^D` of Schmidt number
larger than `n` is detected by an `n`-positive map `T`: the ampliation `(T ⊗ id)(ρ)` is not
positive semidefinite.

The entanglement witness `W` of Wolf Proposition 3.3 (`Matrix.exists_isHermitian_witness`)
is the Choi matrix of an `n`-positive map `P` (`exists_isNPositiveMap_choiMatrix_eq_of_witness`).
Its trace-pairing adjoint `T = P*` is again `n`-positive (`IsNPositiveMap.traceAdjointMap`),
and the trace identity
`trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap` turns the negative witness
expectation `Re tr(W ρ) < 0` into a negative real part of `⟨Ω| (T ⊗ id)(ρ) |Ω⟩`.  A
positive semidefinite matrix has nonnegative quadratic forms, so `(T ⊗ id)(ρ)` is not
positive semidefinite. -/
theorem exists_isNPositiveMap_tensorMapId_not_posSemidef [NeZero D] (n : ℕ)
    {ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hρH : ρ.IsHermitian) (hρtr : ρ.trace = 1) (hρ : ¬ HasSchmidtNumberLE n ρ) :
    ∃ T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      IsNPositiveMap n T ∧ ¬ (tensorMapId T ρ).PosSemidef := by
  -- The entanglement witness for ρ.
  obtain ⟨W, hWherm, hWρ, hWpos⟩ := exists_isHermitian_witness n hρH hρtr hρ
  -- `W` is the Choi matrix of an `n`-positive map `P`.
  obtain ⟨P, hPpos, hPchoi⟩ :=
    exists_isNPositiveMap_choiMatrix_eq_of_witness hWherm hWpos
  -- Its trace-pairing adjoint is the detecting `n`-positive map.
  refine ⟨Matrix.traceAdjointMap P, hPpos.traceAdjointMap, ?_⟩
  intro hPSD
  -- A positive semidefinite matrix has a nonnegative Choi-vector quadratic form.
  have hquad : 0 ≤ star (omegaVec D) ⬝ᵥ
      (tensorMapId (Matrix.traceAdjointMap P) ρ *ᵥ omegaVec D) :=
    hPSD.dotProduct_mulVec_nonneg (omegaVec D)
  -- But that quadratic form is `tr(W ρ)`, whose real part is negative.
  have hid := trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap P ρ
  rw [hPchoi] at hid
  rw [← hid] at hquad
  exact absurd ((Complex.nonneg_iff.mp hquad).1) (not_le.mpr hWρ)

end Matrix
