/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Kraus.Injectivity
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.AssemblyLemmas
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.EisensteinRing

/-!
# Eisenstein-integral certificates for worked compression examples

A worked example of the multi-block asymmetric compression theorem (P5 note,
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) whose
tensors, gauges and targets have entries in the Eisenstein integers `ℤ[ω]` is verified by
deciding finitely many identities over `ℤ[ω]` and transporting them along the embedding
`eisensteinToComplex`. This file packages the three transports that every such example needs.

* `MPSTensor.MultiBlockCompression.ofEisenstein` builds the compression datum of
  Theorem 7.7 from an Eisenstein-integral gauge, its inverse, and the decided block-triangular,
  matched and unmatched clauses of the conjugated letters; its compression pair is then read off
  by `MPSTensor.MultiBlockCompression.left_gaugeOfMatrix` and
  `MPSTensor.MultiBlockCompression.right_gaugeOfMatrix`.
* `MPSTensor.isNBlkInjective_of_scaled_single` certifies injectivity at a fixed word length,
  and `MPSTensor.isNormal_of_scaled_single` normality, from finitely many words whose
  combinations are the matrix units scaled by a common nonzero Eisenstein integer.
* `MPSTensor.right_intertwiner_eq_zero_of_eisenstein` and
  `MPSTensor.left_intertwiner_eq_zero_of_eisenstein` transport the intertwiner certificates of
  `AssemblyLemmas.lean` from `ℤ[ω]` to the complex numbers.

## Main definitions

* `MPSTensor.MultiBlockCompression.ofEisenstein`: the compression datum attached to an
  Eisenstein-integral gauge.

## Main results

* `MPSTensor.isNBlkInjective_of_scaled_single`, `MPSTensor.isNormal_of_scaled_single`: the
  block-injectivity and normality certificates.
* `MPSTensor.right_intertwiner_eq_zero_of_eisenstein`,
  `MPSTensor.left_intertwiner_eq_zero_of_eisenstein`: the intertwiner certificates.
-/

open scoped Matrix

namespace MPSTensor

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι}

/-! ### Compression data from an Eisenstein-integral gauge -/

/-- The image of a pair of mutually inverse Eisenstein-integral matrices is a pair of mutually
inverse complex matrices. -/
theorem complexOfEisenstein_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {G Ginv : Matrix n n EisensteinInt} (hG : G * Ginv = 1) :
    complexOfEisenstein G * complexOfEisenstein Ginv = 1 := by
  rw [← complexOfEisenstein_mul, hG, complexOfEisenstein_one]

namespace MultiBlockCompression

variable {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-- **A multi-block compression datum from an Eisenstein-integral gauge** (P5 note,
Theorem 7.7, clauses (i)–(iii)). The source `B` and the targets `C s` are the images of the
Eisenstein-integral tensors `BE` and `CE s`, the gauge `G` with inverse `Ginv` is
Eisenstein-integral, and the three clauses are stated for the entries of the conjugated letters
`G * BE i * Ginv` at the coordinates labelled by the block space along `coord`. -/
noncomputable def ofEisenstein (BE : Fin d → Matrix (Fin DB) (Fin DB) EisensteinInt)
    (hB : ∀ i, B i = complexOfEisenstein (BE i))
    (CE : ∀ s, Fin d → Matrix (Fin (D s)) (Fin (D s)) EisensteinInt)
    (hC : ∀ s i, C s i = complexOfEisenstein (CE s i)) (z : ℕ)
    (ord : BlockIndex S z ≃ Fin (S.card + z)) (coord : BlockSpace D S z ≃ Fin DB)
    (G Ginv : Matrix (Fin DB) (Fin DB) EisensteinInt) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (htri : ∀ (i : Fin d) (x y : BlockSpace D S z), ord y.1 < ord x.1 →
      (G * BE i * Ginv) (coord x) (coord y) = 0)
    (hmatched : ∀ (i : Fin d) (s : {s // s ∈ S}) (p q : Fin (D s.1)),
      (G * BE i * Ginv) (coord ⟨Sum.inl s, p⟩) (coord ⟨Sum.inl s, q⟩) = CE s.1 i p q)
    (hunmatched : ∀ (i : Fin d) (t : Fin z) (p q : Fin 1),
      (G * BE i * Ginv) (coord ⟨Sum.inr t, p⟩) (coord ⟨Sum.inr t, q⟩) = 0) :
    MultiBlockCompression B S C where
  z := z
  ord := ord
  gauge := gaugeOfMatrix coord (complexOfEisenstein G) (complexOfEisenstein Ginv)
    (complexOfEisenstein_mul_eq_one hG) (complexOfEisenstein_mul_eq_one hG')
  triangular i x y h := by
    rw [conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hB, ← complexOfEisenstein_mul,
      ← complexOfEisenstein_mul, complexOfEisenstein_apply, htri i x y h, map_zero]
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hB,
      ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, complexOfEisenstein_apply,
      hmatched i s p q, hC, complexOfEisenstein_apply]
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hB,
      ← complexOfEisenstein_mul, ← complexOfEisenstein_mul, complexOfEisenstein_apply,
      hunmatched i t p q, map_zero, Matrix.zero_apply]

end MultiBlockCompression

/-! ### Normality from scaled matrix units -/

/-- **A block-injectivity certificate over the Eisenstein integers.** If for every matrix unit
`E_{ij}` finitely many words of a common length `N` combine, with Eisenstein-integral
coefficients, to `c • E_{ij}` for one nonzero Eisenstein integer `c`, then the words of length
`N` span the full matrix algebra. -/
theorem isNBlkInjective_of_scaled_single {D : ℕ} {A : MPSTensor d D}
    (AE : Fin d → Matrix (Fin D) (Fin D) EisensteinInt)
    (hA : ∀ a, A a = complexOfEisenstein (AE a)) {N K : ℕ}
    (word : Fin D → Fin D → Fin K → Fin N → Fin d) (coeff : Fin D → Fin D → Fin K → EisensteinInt)
    {c : EisensteinInt} (hc : c ≠ 0)
    (h : ∀ i j, ∑ k, coeff i j k • evalWordEisenstein AE (List.ofFn (word i j k)) =
      c • Matrix.single i j 1) :
    Kraus.IsNBlkInjective A N := by
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan]
  set T := Submodule.span ℂ
    (Set.range fun w : Fin N → Fin d => Kraus.evalWord A (List.ofFn w)) with hT
  have hA' : A = fun a => complexOfEisenstein (AE a) := funext hA
  have hc' : eisensteinToComplex c ≠ 0 := eisensteinToComplex_ne_zero hc
  have hunit : ∀ i j : Fin D, Matrix.single i j (1 : ℂ) ∈ T := by
    intro i j
    have h1 := congrArg complexOfEisenstein (h i j)
    rw [complexOfEisenstein_sum, complexOfEisenstein_smul, complexOfEisenstein_single] at h1
    have hmem : ∑ k, complexOfEisenstein
        (coeff i j k • evalWordEisenstein AE (List.ofFn (word i j k))) ∈ T := by
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [complexOfEisenstein_smul, ← evalWord_complexOfEisenstein, ← hA']
      exact T.smul_mem _ (Submodule.subset_span ⟨word i j k, rfl⟩)
    rw [h1] at hmem
    have h2 := T.smul_mem (eisensteinToComplex c)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at h2
  exact T.eq_top_of_forall_single_mem hunit

/-- **A normality certificate over the Eisenstein integers**: the certificate of
`isNBlkInjective_of_scaled_single` at a positive length `N` shows the tensor is normal at
blocking length `N`. -/
theorem isNormal_of_scaled_single {D : ℕ} {A : MPSTensor d D}
    (AE : Fin d → Matrix (Fin D) (Fin D) EisensteinInt)
    (hA : ∀ a, A a = complexOfEisenstein (AE a)) {N : ℕ} (hN : 0 < N) {K : ℕ}
    (word : Fin D → Fin D → Fin K → Fin N → Fin d) (coeff : Fin D → Fin D → Fin K → EisensteinInt)
    {c : EisensteinInt} (hc : c ≠ 0)
    (h : ∀ i j, ∑ k, coeff i j k • evalWordEisenstein AE (List.ofFn (word i j k)) =
      c • Matrix.single i j 1) :
    Kraus.IsNormal A :=
  ⟨N, hN, isNBlkInjective_of_scaled_single AE hA word coeff hc h⟩

/-! ### Intertwiner certificates over the Eisenstein integers -/

theorem sitewiseEqMatrix_complexOfEisenstein {m n : ℕ}
    (BE : Fin d → Matrix (Fin m) (Fin m) EisensteinInt)
    (CE : Fin d → Matrix (Fin n) (Fin n) EisensteinInt) :
    complexOfEisenstein (sitewiseEqMatrix BE CE) =
      sitewiseEqMatrix (fun i => complexOfEisenstein (BE i))
        (fun i => complexOfEisenstein (CE i)) :=
  sitewiseEqMatrix_map eisensteinToComplex BE CE

/-- **No nonzero right sitewise intertwiner, from an Eisenstein-integral certificate.** -/
theorem right_intertwiner_eq_zero_of_eisenstein {m n k : ℕ} {B : MPSTensor d m}
    (BE : Fin d → Matrix (Fin m) (Fin m) EisensteinInt) (hB : ∀ i, B i = complexOfEisenstein (BE i))
    {C : MPSTensor d n} (CE : Fin d → Matrix (Fin n) (Fin n) EisensteinInt)
    (hC : ∀ i, C i = complexOfEisenstein (CE i)) (rows : Fin k → Fin d × Fin m × Fin n)
    (N : Matrix (Fin m × Fin n) (Fin k) EisensteinInt) {c : EisensteinInt} (hc : c ≠ 0)
    (hN : N * (sitewiseEqMatrix BE CE).submatrix rows id = c • 1)
    (X : Matrix (Fin m) (Fin n) ℂ) (hX : ∀ i, B i * X = X * C i) : X = 0 := by
  have hB' : B = fun i => complexOfEisenstein (BE i) := funext hB
  have hC' : C = fun i => complexOfEisenstein (CE i) := funext hC
  have hN' := congrArg complexOfEisenstein hN
  rw [complexOfEisenstein_mul, complexOfEisenstein_submatrix, complexOfEisenstein_smul,
    complexOfEisenstein_one, sitewiseEqMatrix_complexOfEisenstein, ← hB', ← hC'] at hN'
  exact right_intertwiner_eq_zero_of_certificate B C rows (complexOfEisenstein N)
    (eisensteinToComplex_ne_zero hc) hN' X hX

/-- **No nonzero left sitewise intertwiner, from an Eisenstein-integral certificate** for the
transposed letters. -/
theorem left_intertwiner_eq_zero_of_eisenstein {m n k : ℕ} {B : MPSTensor d m}
    (BE : Fin d → Matrix (Fin m) (Fin m) EisensteinInt) (hB : ∀ i, B i = complexOfEisenstein (BE i))
    {C : MPSTensor d n} (CE : Fin d → Matrix (Fin n) (Fin n) EisensteinInt)
    (hC : ∀ i, C i = complexOfEisenstein (CE i)) (rows : Fin k → Fin d × Fin m × Fin n)
    (N : Matrix (Fin m × Fin n) (Fin k) EisensteinInt) {c : EisensteinInt} (hc : c ≠ 0)
    (hN : N * (sitewiseEqMatrix (fun i => (BE i)ᵀ) (fun i => (CE i)ᵀ)).submatrix rows id =
      c • 1)
    (Y : Matrix (Fin n) (Fin m) ℂ) (hY : ∀ i, Y * B i = C i * Y) : Y = 0 := by
  have hB' : (fun i => (B i)ᵀ) = fun i => complexOfEisenstein (BE i)ᵀ :=
    funext fun i => by rw [hB, complexOfEisenstein_transpose]
  have hC' : (fun i => (C i)ᵀ) = fun i => complexOfEisenstein (CE i)ᵀ :=
    funext fun i => by rw [hC, complexOfEisenstein_transpose]
  have hN' := congrArg complexOfEisenstein hN
  rw [complexOfEisenstein_mul, complexOfEisenstein_submatrix, complexOfEisenstein_smul,
    complexOfEisenstein_one, sitewiseEqMatrix_complexOfEisenstein, ← hB', ← hC'] at hN'
  exact left_intertwiner_eq_zero_of_certificate B C rows (complexOfEisenstein N)
    (eisensteinToComplex_ne_zero hc) hN' Y hY

end MPSTensor
