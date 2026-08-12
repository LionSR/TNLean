/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.ChoiRectangular

/-!
# Decomposition of linear maps into completely positive maps

Every linear map `T : M_d(ℂ) → M_{d'}(ℂ)` is a complex linear combination of
four completely positive maps, and a Hermitian map — one satisfying
`T(B†) = T(B)†` for every `B` — is a real linear combination of two of them.
This is the proposition "Decomposition into completely positive maps" of
Wolf Chapter 2, `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 130–149.

The proof is Wolf's. Because the correspondence `T ↔ τ` of Proposition 2.1 is
one-to-one and linear, it suffices to decompose the Choi matrix. Wolf's display

  `τ = (τ + τ†)/2 + i (i τ† - i τ)/2`

writes `τ` as a complex linear combination of two Hermitian matrices, and the
spectral decomposition writes each Hermitian matrix as a real linear
combination of two positive semidefinite ones. Every positive semidefinite
operator on `ℂ^{d'} ⊗ ℂ^d` is the Choi matrix of a completely positive map, so
transporting the four positive semidefinite pieces back through the
correspondence produces the four completely positive maps.

## Main results

* `Matrix.IsHermitian.exists_eq_sub_posSemidef` — the Jordan decomposition of a
  Hermitian matrix into a difference of two positive semidefinite matrices.
* `Matrix.exists_isHermitian_eq_add_smul_I` — Wolf's display: every square
  matrix is `H₁ + i H₂` with `H₁` and `H₂` Hermitian.
* `ChoiRectangular.exists_four_isKrausCP_complexCombination` — every linear map
  `M_d(ℂ) → M_{d'}(ℂ)` is a complex linear combination of four completely
  positive maps.
* `ChoiRectangular.exists_two_isKrausCP_realCombination_of_hermiticityPreserving`
  — a Hermitian map is a real linear combination of two completely positive
  maps.

## Implementation notes

Complete positivity is the rectangular Kraus predicate `IsKrausCP`, the notion
used in the complete-positivity clause of Wolf Proposition 2.1 and in
Wolf Theorem 2.1. No hypothesis is placed on the dimensions: for `d = 0` the
input algebra has a single element, every linear map out of it vanishes, and
the empty combination already witnesses the statement.

The square sandwich polarization `WolfProps.cp_decomposition_of_sandwich_sum`
proves a different statement: it decomposes a map already presented in the
form `X ↦ ∑ᵢ Aᵢ X Bᵢ†` on a single matrix algebra.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2,
  Proposition "Decomposition into completely positive maps"][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset

namespace Matrix

variable {n : Type*}

/-- **Jordan decomposition**: a Hermitian matrix is the difference of two
positive semidefinite matrices, namely its positive and negative parts. This is
the spectral decomposition step of Wolf Chapter 2, proposition "Decomposition
into completely positive maps"; `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 146–148. -/
theorem IsHermitian.exists_eq_sub_posSemidef [Finite n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) :
    ∃ P N : Matrix n n ℂ, P.PosSemidef ∧ N.PosSemidef ∧ H = P - N := by
  classical
  cases nonempty_fintype n
  exact ⟨H⁺, H⁻, Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H),
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H),
    (CFC.posPart_sub_negPart H (isSelfAdjoint_iff.mpr hH)).symm⟩

/-- **Hermitian and anti-Hermitian parts**: every square complex matrix is
`H₁ + i H₂` with `H₁` and `H₂` Hermitian. The witnesses are Wolf's,
`H₁ = (τ + τ†)/2` and `H₂ = (i τ† - i τ)/2`;
`Notes/WolfNoteTexSource/ch02_representations.tex`, line 144. -/
theorem exists_isHermitian_eq_add_smul_I (τ : Matrix n n ℂ) :
    ∃ H₁ H₂ : Matrix n n ℂ, H₁.IsHermitian ∧ H₂.IsHermitian ∧
      τ = H₁ + Complex.I • H₂ := by
  refine ⟨(2 : ℂ)⁻¹ • (τ + τᴴ), (2 : ℂ)⁻¹ • (Complex.I • τᴴ - Complex.I • τ),
    ?_, ?_, ?_⟩
  · change ((2 : ℂ)⁻¹ • (τ + τᴴ))ᴴ = _
    rw [← star_eq_conjTranspose, ← star_eq_conjTranspose]
    simp [star_smul, add_comm]
  · change ((2 : ℂ)⁻¹ • (Complex.I • τᴴ - Complex.I • τ))ᴴ = _
    simp only [← star_eq_conjTranspose, star_smul, star_sub, star_star, RCLike.star_def,
      Complex.conj_I, map_inv₀, map_ofNat]
    module
  · have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    match_scalars
    · linear_combination ((1 : ℂ) / 2) * hI
    · linear_combination (-(1 : ℂ) / 2) * hI

end Matrix

namespace ChoiRectangular

variable {d d' : ℕ}

/-- The Choi assignment commutes with finite sums of maps. -/
theorem choiMatrix_sum {ι : Type*} (s : Finset ι)
    (T : ι → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)) :
    choiMatrix (∑ i ∈ s, T i) = ∑ i ∈ s, choiMatrix (T i) :=
  map_sum (choiMatrixLinearMap (d := d) (d' := d')) T s

/-- The zero map is completely positive: the empty Kraus family represents it. -/
private theorem isKrausCP_zero :
    IsKrausCP (0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :=
  ⟨0, Fin.elim0, by simp⟩

/-- Over the zero-dimensional input algebra there is only the zero map. -/
private theorem eq_zero_of_isEmpty
    (T : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) : T = 0 := by
  refine LinearMap.ext fun B => ?_
  have hB : B = 0 := by ext i; exact i.elim0
  rw [hB, map_zero, LinearMap.zero_apply]

/-- **Decomposition into completely positive maps** (Wolf, Chapter 2). Every
linear map `T : M_d(ℂ) → M_{d'}(ℂ)` is a complex linear combination of four
completely positive maps.

Wolf, Chapter 2, proposition "Decomposition into completely positive maps",
first sentence; `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 130–135. -/
theorem exists_four_isKrausCP_complexCombination
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    ∃ (c : Fin 4 → ℂ)
      (S : Fin 4 → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)),
      (∀ k, IsKrausCP (S k)) ∧ T = ∑ k, c k • S k := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, 0, fun _ => isKrausCP_zero, by simp [eq_zero_of_isEmpty T]⟩
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨H₁, H₂, hH₁, hH₂, hsplit⟩ :=
    Matrix.exists_isHermitian_eq_add_smul_I (choiMatrix T)
  obtain ⟨P₁, N₁, hP₁, hN₁, hH₁eq⟩ := hH₁.exists_eq_sub_posSemidef
  obtain ⟨P₂, N₂, hP₂, hN₂, hH₂eq⟩ := hH₂.exists_eq_sub_posSemidef
  obtain ⟨S₁, hS₁cp, hS₁⟩ := exists_isKrausCP_of_posSemidef hP₁
  obtain ⟨S₂, hS₂cp, hS₂⟩ := exists_isKrausCP_of_posSemidef hN₁
  obtain ⟨S₃, hS₃cp, hS₃⟩ := exists_isKrausCP_of_posSemidef hP₂
  obtain ⟨S₄, hS₄cp, hS₄⟩ := exists_isKrausCP_of_posSemidef hN₂
  refine ⟨![1, -1, Complex.I, -Complex.I], ![S₁, S₂, S₃, S₄], ?_,
    choiMatrix_injective ?_⟩
  · intro k
    fin_cases k
    exacts [hS₁cp, hS₂cp, hS₃cp, hS₄cp]
  · rw [choiMatrix_sum]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, choiMatrix_smul, hS₁, hS₂, hS₃, hS₄, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    rw [hsplit, hH₁eq, hH₂eq]
    module

/-- **Decomposition into completely positive maps**, Hermitian case (Wolf,
Chapter 2). A linear map `T : M_d(ℂ) → M_{d'}(ℂ)` that is Hermitian, that is,
`T(B†) = T(B)†` for every `B ∈ M_d(ℂ)`, is a real linear combination of two
completely positive maps.

Wolf, Chapter 2, proposition "Decomposition into completely positive maps",
second sentence; `Notes/WolfNoteTexSource/ch02_representations.tex`,
lines 132–134. -/
theorem exists_two_isKrausCP_realCombination_of_hermiticityPreserving
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : ∀ B : Matrix (Fin d) (Fin d) ℂ, T (Bᴴ) = (T B)ᴴ) :
    ∃ (c : Fin 2 → ℝ)
      (S : Fin 2 → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)),
      (∀ k, IsKrausCP (S k)) ∧ T = ∑ k, (c k : ℂ) • S k := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, 0, fun _ => isKrausCP_zero, by simp [eq_zero_of_isEmpty T]⟩
  haveI : NeZero d := ⟨hd.ne'⟩
  have hherm : (choiMatrix T).IsHermitian :=
    (choiMatrix_isHermitian_iff_hermiticityPreserving T).mpr hT
  obtain ⟨P, N, hP, hN, hsplit⟩ := hherm.exists_eq_sub_posSemidef
  obtain ⟨S₁, hS₁cp, hS₁⟩ := exists_isKrausCP_of_posSemidef hP
  obtain ⟨S₂, hS₂cp, hS₂⟩ := exists_isKrausCP_of_posSemidef hN
  refine ⟨![1, -1], ![S₁, S₂], ?_, choiMatrix_injective ?_⟩
  · intro k
    fin_cases k
    exacts [hS₁cp, hS₂cp]
  · rw [choiMatrix_sum]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, choiMatrix_smul, hS₁, hS₂]
    rw [hsplit]
    push_cast
    module

end ChoiRectangular
