/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.OrthogonalProjection
import TNLean.Algebra.TracePairing
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.KrausCPTP
import TNLean.Channel.MaximalOverlap
import TNLean.Channel.POVM
import TNLean.Channel.SingleKraus
import TNLean.Channel.TensorMap

/-!
# Quantum steering via instruments (Wolf Chapter 1, Proposition 1.2)

This file proves Wolf's quantum-steering proposition: for a density operator
`ρ` with purification `ψ`, every convex decomposition `ρ = Σᵢ λᵢ ρᵢ` is
realized by an instrument acting on the purifying system.

Local source: `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`,
lines 348--357 (statement) and 359--370 (proof sketch).

## Main definitions

* `Matrix.IsPurification`: `ψ` purifies `ρ` if tracing out the second factor
  of `|ψ⟩⟨ψ|` gives `ρ` (line 348).
* `Matrix.IsConvexDecomposition`: the standard unpacking of "convex
  decomposition" — nonnegative weights summing to one, density-operator
  summands, and the weighted sum equal to `ρ`.

## Main results

* `Matrix.partialTraceRight_idTensorMap_vecMulVec`: for any linear map `T`
  on Bob's system and any bipartite vector `ψ`, tracing out Bob's system
  after applying `id ⊗ T` to `|ψ⟩⟨ψ|` equals `C (T*(1))ᵀ Cᴴ`, where `C` is
  the coefficient matrix of `ψ` and `T*` is the trace-pairing adjoint. This
  is the general (purification-independent) form of the identity Wolf
  derives at line 364 for the canonical purification `ψ = (√ρ ⊗ 1)|Ω⟩`.
* `Matrix.exists_instrument_of_isConvexDecomposition`: **Wolf Proposition
  1.2 (Quantum steering)**. For every convex decomposition `ρ = Σᵢ λᵢ ρᵢ`
  there is an instrument `{Tᵢ}` on Bob's system with
  `λᵢ • ρᵢ = Tr_B[(id ⊗ Tᵢ)(|ψ⟩⟨ψ|)]` for every `i`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1,
  Proposition (Quantum steering)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

namespace Matrix

variable {dA dB : ℕ}

/-! ### Purifications and convex decompositions -/

/-- **Purification** (Wolf, line 348): a bipartite vector `ψ` purifies the
density operator `ρ` if tracing out the second factor of `|ψ⟩⟨ψ|` recovers
`ρ`. -/
def IsPurification (ρ : Matrix (Fin dA) (Fin dA) ℂ) (ψ : Fin dA × Fin dB → ℂ) : Prop :=
  Matrix.partialTraceRight (Matrix.vecMulVec ψ (star ψ)) = ρ

/-- **Convex decomposition**: the standard unpacking of Wolf's phrase
"convex decomposition `ρ = Σᵢ λᵢ ρᵢ`" — nonnegative weights summing to one,
each `ρᵢ` a density operator, and the weighted sum equal to `ρ`. -/
def IsConvexDecomposition {n : ℕ} (ρ : Matrix (Fin dA) (Fin dA) ℂ)
    (lam : Fin n → ℝ) (rho' : Fin n → Matrix (Fin dA) (Fin dA) ℂ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧ (∀ i, (rho' i).PosSemidef) ∧
    (∀ i, (rho' i).trace = 1) ∧ (∑ i, lam i • rho' i = ρ)

/-! ### The trace-pairing adjoint of a single-Kraus map -/

/-- The trace-pairing adjoint of a single-Kraus map `X ↦ V X Vᴴ` evaluated
at the identity is `Vᴴ V`. -/
theorem traceAdjointMap_singleKrausMap_one {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (V : Matrix β α ℂ) :
    Matrix.traceAdjointMap (singleKrausMap V) (1 : Matrix β β ℂ) = Vᴴ * V := by
  rw [Matrix.traceAdjointMap_singleKrausMap, singleKrausMap_apply, Matrix.mul_one,
    Matrix.conjTranspose_conjTranspose]

/-! ### The transpose-trick identity -/

/-- The `(i₁, j₁)`-block of `vecMulVec ψ (star ψ)` is the outer product of
the corresponding rows of the coefficient matrix. -/
private theorem bipartiteBlock_vecMulVec_eq (ψ : Fin dA × Fin dB → ℂ) (i₁ j₁ : Fin dA) :
    Matrix.bipartiteBlock (Matrix.vecMulVec ψ (star ψ)) i₁ j₁ =
      Matrix.vecMulVec (Matrix.schmidtCoeffMatrix ψ i₁)
        (star (Matrix.schmidtCoeffMatrix ψ j₁)) := by
  ext i₂ j₂
  simp only [Matrix.bipartiteBlock_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.schmidtCoeffMatrix_apply]

/-- **The transpose trick** (Wolf, line 364, in general purification-independent
form): for any linear map `T` on Bob's system and any bipartite vector `ψ`
with coefficient matrix `C`, tracing out Bob's system after applying
`id ⊗ T` to `|ψ⟩⟨ψ|` equals `C (T*(1))ᵀ Cᴴ`, where `T*` is the trace-pairing
adjoint of `T`.

Wolf derives this for the specific canonical purification `ψ = (√ρ ⊗ 1)|Ω⟩`;
the identity holds for an arbitrary purification since it only uses the
coefficient matrix of `ψ` and linearity, not the particular form of `C`. -/
theorem partialTraceRight_idTensorMap_vecMulVec {dB' : ℕ} (ψ : Fin dA × Fin dB → ℂ)
    (T : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin dB') (Fin dB') ℂ) :
    Matrix.partialTraceRight (Matrix.idTensorMap T (Matrix.vecMulVec ψ (star ψ))) =
      Matrix.schmidtCoeffMatrix ψ * (Matrix.traceAdjointMap T 1)ᵀ *
        (Matrix.schmidtCoeffMatrix ψ)ᴴ := by
  set C := Matrix.schmidtCoeffMatrix ψ with hC
  set M := Matrix.traceAdjointMap T (1 : Matrix (Fin dB') (Fin dB') ℂ) with hM
  ext i₁ j₁
  have hstep : Matrix.partialTraceRight (Matrix.idTensorMap T (Matrix.vecMulVec ψ (star ψ)))
      i₁ j₁ = Matrix.trace (T (Matrix.bipartiteBlock (Matrix.vecMulVec ψ (star ψ)) i₁ j₁)) := by
    simp only [Matrix.partialTraceRight_apply, Matrix.idTensorMap_apply, Matrix.trace]
    rfl
  rw [hstep, bipartiteBlock_vecMulVec_eq]
  have hadj : Matrix.trace (T (Matrix.vecMulVec (C i₁) (star (C j₁)))) =
      Matrix.trace (M * Matrix.vecMulVec (C i₁) (star (C j₁))) := by
    rw [Matrix.trace_traceAdjointMap_mul T 1 (Matrix.vecMulVec (C i₁) (star (C j₁))),
      Matrix.one_mul]
  rw [hadj, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  change (M *ᵥ C i₁) ⬝ᵥ (star (C j₁)) = (C * Mᵀ * Cᴴ) i₁ j₁
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-! ### The steering instrument construction -/

variable {n : ℕ} {ρ : Matrix (Fin dA) (Fin dA) ℂ}

/-- A real scalar multiple of a positive-semidefinite matrix is Hermitian. -/
private theorem isHermitian_smul_of_posSemidef {A : Matrix (Fin dA) (Fin dA) ℂ}
    (hA : A.PosSemidef) (c : ℝ) : (c • A).IsHermitian := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact hA.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))

/-- The support projection of `ρ` absorbs each weighted summand of a convex
decomposition of `ρ`, on both sides. -/
private theorem supportProj_mul_smul_mul_supportProj (hρ : ρ.PosSemidef) {n : ℕ}
    {lam : Fin n → ℝ} {rho' : Fin n → Matrix (Fin dA) (Fin dA) ℂ}
    (hlam0 : ∀ i, 0 ≤ lam i) (hrho' : ∀ i, (rho' i).PosSemidef)
    (hsum : ∑ i, lam i • rho' i = ρ) (i : Fin n) :
    hρ.supportProj * (lam i • rho' i) * hρ.supportProj = lam i • rho' i := by
  have hB : ∀ j, (lam j • rho' j).PosSemidef := fun j => (hrho' j).smul (hlam0 j)
  have hker : ∀ v : Fin dA → ℂ, ρ *ᵥ v = 0 → (lam i • rho' i) *ᵥ v = 0 := fun v hv =>
    Matrix.PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero hB (by rwa [hsum]) i
  have hright : (lam i • rho' i) * hρ.isHermitian.supportProj = lam i • rho' i :=
    hρ.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  have hleft : hρ.isHermitian.supportProj * (lam i • rho' i) = lam i • rho' i := by
    have h := congrArg Matrix.conjTranspose hright
    simpa only [Matrix.conjTranspose_mul, hρ.isHermitian.supportProj_isHermitian.eq,
      (isHermitian_smul_of_posSemidef (hrho' i) (lam i)).eq] using h
  change hρ.isHermitian.supportProj * (lam i • rho' i) * hρ.isHermitian.supportProj =
    lam i • rho' i
  rw [hleft, hright]

/-- A right pseudo-inverse of the coefficient matrix `C` of a purification of
`ρ`, built from the generalized inverse of `ρ` on its support:
`C⁺ := Cᴴ ρ⁺`. It satisfies `C C⁺ = ` the support projection of `ρ`
(`mul_purificationPinv`). -/
private noncomputable def purificationPinv (hρ : ρ.PosSemidef)
    (C : Matrix (Fin dA) (Fin dB) ℂ) : Matrix (Fin dB) (Fin dA) ℂ :=
  Cᴴ * hρ.supportInv

private theorem mul_purificationPinv (hρ : ρ.PosSemidef) {C : Matrix (Fin dA) (Fin dB) ℂ}
    (hCC : C * Cᴴ = ρ) :
    C * purificationPinv hρ C = hρ.supportProj := by
  change C * (Cᴴ * hρ.supportInv) = hρ.supportProj
  rw [← Matrix.mul_assoc, hCC]
  exact hρ.self_mul_supportInv

private theorem purificationPinv_conjTranspose (hρ : ρ.PosSemidef)
    (C : Matrix (Fin dA) (Fin dB) ℂ) :
    (purificationPinv hρ C)ᴴ = hρ.supportInv * C := by
  change (Cᴴ * hρ.supportInv)ᴴ = hρ.supportInv * C
  rw [Matrix.conjTranspose_mul, hρ.supportInv_isHermitian.eq, Matrix.conjTranspose_conjTranspose]

/-- `C⁺ C` is an orthogonal projection on Bob's system: the "leftover"
subspace of `H_B` not needed to purify `ρ` is its orthogonal complement. -/
private theorem isOrthogonalProjection_purificationPinv_mul (hρ : ρ.PosSemidef)
    {C : Matrix (Fin dA) (Fin dB) ℂ} (hCC : C * Cᴴ = ρ) :
    IsOrthogonalProjection (purificationPinv hρ C * C) := by
  have hCinvC : purificationPinv hρ C * hρ.supportProj = purificationPinv hρ C := by
    change (Cᴴ * hρ.supportInv) * hρ.supportProj = Cᴴ * hρ.supportInv
    rw [Matrix.mul_assoc, hρ.supportInv_mul_supportProj]
  refine ⟨?_, ?_⟩
  · change (purificationPinv hρ C * C)ᴴ = purificationPinv hρ C * C
    rw [Matrix.conjTranspose_mul, purificationPinv_conjTranspose, ← Matrix.mul_assoc]
    rfl
  · calc purificationPinv hρ C * C * (purificationPinv hρ C * C)
        = purificationPinv hρ C * (C * purificationPinv hρ C) * C := by
          simp only [Matrix.mul_assoc]
      _ = purificationPinv hρ C * hρ.supportProj * C := by rw [mul_purificationPinv hρ hCC]
      _ = purificationPinv hρ C * C := by rw [hCinvC]

/-- The "leftover" completion term: the transpose of the orthogonal
complement of `C⁺ C`, absorbed by `Cᴴ` on the right and `C` on the left with
zero contribution (`mul_purificationPinvComplement_mul`). -/
private noncomputable def purificationPinvComplement (hρ : ρ.PosSemidef)
    (C : Matrix (Fin dA) (Fin dB) ℂ) : Matrix (Fin dB) (Fin dB) ℂ :=
  (1 - purificationPinv hρ C * C)ᵀ

private theorem purificationPinvComplement_posSemidef (hρ : ρ.PosSemidef)
    {C : Matrix (Fin dA) (Fin dB) ℂ} (hCC : C * Cᴴ = ρ) :
    (purificationPinvComplement hρ C).PosSemidef :=
  (isOrthogonalProjection_posSemidef
    (isOrthogonalProjection_purificationPinv_mul hρ hCC).one_sub).transpose

/-- `C` sandwiches `C⁺ C` back to `ρ`. -/
private theorem mul_purificationPinv_mul_mul (hρ : ρ.PosSemidef)
    {C : Matrix (Fin dA) (Fin dB) ℂ} (hCC : C * Cᴴ = ρ) :
    C * (purificationPinv hρ C * C) * Cᴴ = ρ := by
  calc C * (purificationPinv hρ C * C) * Cᴴ
      = (C * purificationPinv hρ C) * (C * Cᴴ) := by simp only [Matrix.mul_assoc]
    _ = hρ.supportProj * ρ := by rw [mul_purificationPinv hρ hCC, hCC]
    _ = ρ := hρ.supportProj_mul_self

private theorem mul_purificationPinvComplement_mul (hρ : ρ.PosSemidef)
    {C : Matrix (Fin dA) (Fin dB) ℂ} (hCC : C * Cᴴ = ρ) :
    C * (purificationPinvComplement hρ C)ᵀ * Cᴴ = 0 := by
  change C * (1 - purificationPinv hρ C * C) * Cᴴ = 0
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hCC,
    mul_purificationPinv_mul_mul hρ hCC, sub_self]

/-- **Wolf Proposition (Quantum steering)**, Chapter 1, lines 348--357;
proof sketch lines 359--370. For a density operator `ρ` with purification
`ψ` and any convex decomposition `ρ = Σᵢ λᵢ ρᵢ`, there is an instrument
`{Tᵢ}` acting on Bob's system realizing the decomposition: tracing out
Bob's system after applying `id ⊗ Tᵢ` to `|ψ⟩⟨ψ|` recovers `λᵢ ρᵢ`.

The trace hypothesis on `ρ` is carried for fidelity to Wolf's "density
operator" hypothesis even though the proof below only needs `ρ.PosSemidef`;
the convex decomposition already forces `ρ.trace = 1` (it is a convex
combination of trace-one operators). -/
theorem exists_instrument_of_isConvexDecomposition (hρ : ρ.PosSemidef) (_hρtr : ρ.trace = 1)
    {ψ : Fin dA × Fin dB → ℂ} (hpsi : IsPurification ρ ψ)
    {lam : Fin n → ℝ} {rho' : Fin n → Matrix (Fin dA) (Fin dA) ℂ}
    (hdecomp : IsConvexDecomposition ρ lam rho') :
    ∃ T : Instrument dB n, ∀ i, lam i • rho' i =
      Matrix.partialTraceRight (Matrix.idTensorMap (T.maps i) (Matrix.vecMulVec ψ (star ψ))) := by
  classical
  obtain ⟨hlam0, hlamsum, hrho'psd, _hrho'tr, hsum⟩ := hdecomp
  set C := Matrix.schmidtCoeffMatrix ψ with hCdef
  have hCC : C * Cᴴ = ρ := by
    rw [hCdef, ← partialTraceRight_vecMulVec_eq]
    exact hpsi
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hlamsum
  set i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn0⟩ with hi0def
  set Cinv := purificationPinv hρ C with hCinvDef
  set X : Fin n → Matrix (Fin dB) (Fin dB) ℂ :=
    fun i => Cinv * (lam i • rho' i) * Cinvᴴ with hXdef
  have hXpsd : ∀ i, (X i).PosSemidef := fun i =>
    ((hrho'psd i).smul (hlam0 i)).mul_mul_conjTranspose_same Cinv
  have hCinvHCH : Cinvᴴ * Cᴴ = hρ.supportProj := by
    rw [hCinvDef, purificationPinv_conjTranspose, Matrix.mul_assoc, hCC]
    exact hρ.supportInv_mul_self
  have hCX : ∀ i, C * X i * Cᴴ = lam i • rho' i := by
    intro i
    have hstep : C * X i * Cᴴ = (C * Cinv) * (lam i • rho' i) * (Cinvᴴ * Cᴴ) := by
      simp only [hXdef, Matrix.mul_assoc]
    rw [hstep, mul_purificationPinv hρ hCC, hCinvHCH]
    exact supportProj_mul_smul_mul_supportProj hρ hlam0 hrho'psd hsum i
  have hCHCinvH : Cᴴ * Cinvᴴ = Cinv * C := by
    rw [hCinvDef, purificationPinv_conjTranspose, ← Matrix.mul_assoc]
    rfl
  have hXsum : ∑ i, X i = Cinv * C := by
    have hpull : ∑ i, X i = Cinv * (∑ i, lam i • rho' i) * Cinvᴴ := by
      simp only [hXdef, ← Matrix.mul_sum, ← Matrix.sum_mul]
    rw [hpull, hsum, ← hCC]
    calc Cinv * (C * Cᴴ) * Cinvᴴ = Cinv * (C * (Cᴴ * Cinvᴴ)) := by simp only [Matrix.mul_assoc]
      _ = Cinv * (C * (Cinv * C)) := by rw [hCHCinvH]
      _ = Cinv * C * (Cinv * C) := by simp only [Matrix.mul_assoc]
      _ = Cinv * C := (isOrthogonalProjection_purificationPinv_mul hρ hCC).2
  set L := purificationPinvComplement hρ C with hLdef
  have hLpsd : L.PosSemidef := purificationPinvComplement_posSemidef hρ hCC
  have hLtranspose : Lᵀ = 1 - Cinv * C := rfl
  set E : Fin n → Matrix (Fin dB) (Fin dB) ℂ :=
    fun i => (X i)ᵀ + (if i = i0 then L else 0) with hEdef
  have hEpsd : ∀ i, (E i).PosSemidef := by
    intro i
    refine Matrix.PosSemidef.add (hXpsd i).transpose ?_
    split
    · exact hLpsd
    · exact Matrix.PosSemidef.zero
  have hEsum : ∑ i, E i = 1 := by
    have hsum1 : ∑ i, E i = (∑ i, X i)ᵀ + L := by
      simp only [hEdef]
      rw [Finset.sum_add_distrib, Matrix.transpose_sum]
      congr 1
      rw [Finset.sum_ite_eq' Finset.univ i0 (fun _ => L)]
      simp
    rw [hsum1, hXsum, hLdef]
    change (Cinv * C)ᵀ + (1 - Cinv * C)ᵀ = 1
    rw [← Matrix.transpose_add]
    have : Cinv * C + (1 - Cinv * C) = (1 : Matrix (Fin dB) (Fin dB) ℂ) := by abel
    rw [this, Matrix.transpose_one]
  have hCE : ∀ i, C * (E i)ᵀ * Cᴴ = lam i • rho' i := by
    intro i
    by_cases hi : i = i0
    · subst hi
      have hEi0 : E i0 = (X i0)ᵀ + L := by rw [hEdef]; simp
      have hEi : (E i0)ᵀ = X i0 + (1 - Cinv * C) := by
        rw [hEi0, Matrix.transpose_add, Matrix.transpose_transpose, hLtranspose]
      have hzero : C * (1 - Cinv * C) * Cᴴ = 0 := mul_purificationPinvComplement_mul hρ hCC
      rw [hEi, Matrix.mul_add, Matrix.add_mul, hCX i0, hzero, add_zero]
    · have hEi : (E i)ᵀ = X i := by
        simp only [hEdef, if_neg hi]
        rw [Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_zero, add_zero]
      rw [hEi]
      exact hCX i
  set sqrtE : Fin n → Matrix (Fin dB) (Fin dB) ℂ :=
    fun i => (hEpsd i).isHermitian.cfc Real.sqrt with hsqrtEdef
  have hsqrtEherm : ∀ i, (sqrtE i).IsHermitian := fun i => (hEpsd i).cfc_sqrt_isHermitian
  have hsqrtEsq : ∀ i, sqrtE i * sqrtE i = E i := fun i => (hEpsd i).cfc_sqrt_mul_self
  set T : Fin n → Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin dB) (Fin dB) ℂ :=
    fun i => singleKrausMap (sqrtE i) with hTdef
  have hTcp : ∀ i, IsCPMap (T i) := fun i => isKrausCP_iff_isCPMap.mp (singleKrausMap_isKrausCP _)
  have hTadj : ∀ i, Matrix.traceAdjointMap (T i) 1 = E i := by
    intro i
    rw [hTdef, traceAdjointMap_singleKrausMap_one, (hsqrtEherm i).eq, hsqrtEsq]
  have hTtp : IsTracePreservingMap (∑ i, T i) := by
    intro X
    have hstep : ∀ i, Matrix.trace (T i X) = Matrix.trace (E i * X) := fun i => by
      rw [← hTadj i, Matrix.trace_traceAdjointMap_mul, Matrix.one_mul]
    simp only [LinearMap.sum_apply]
    calc Matrix.trace (∑ i, T i X) = ∑ i, Matrix.trace (T i X) := Matrix.trace_sum _ _
      _ = ∑ i, Matrix.trace (E i * X) := Finset.sum_congr rfl fun i _ => hstep i
      _ = Matrix.trace ((∑ i, E i) * X) := by rw [Matrix.sum_mul, Matrix.trace_sum]
      _ = Matrix.trace X := by rw [hEsum, Matrix.one_mul]
  refine ⟨⟨T, hTcp, hTtp⟩, fun i => ?_⟩
  change lam i • rho' i =
    Matrix.partialTraceRight (Matrix.idTensorMap (T i) (Matrix.vecMulVec ψ (star ψ)))
  rw [partialTraceRight_idTensorMap_vecMulVec, ← hCdef, hTadj i]
  exact (hCE i).symm

end Matrix
