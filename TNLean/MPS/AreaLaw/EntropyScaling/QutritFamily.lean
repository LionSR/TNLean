/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.AreaLaw.OpenMPS
import QICLean.Channel.MaximalOverlap
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.Positivity

/-!
# The qutrit family for entropy scaling

For `N > 0` and `0 ≤ p ≤ 1`, the state on `2N` qutrits is
`√(1-p) |2⟩^{⊗2N} + √(p/2^N) ∑ x ∈ {0,1}^N, |x⟩|x⟩`.
Its squared Schmidt coefficients at the middle cut are `1-p` and `p/2^N`,
the latter repeated `2^N` times. The qutrit family in the source takes `p = 1/N`.

## References

Schuch, Wolf, Verstraete and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, equation `eq:magicstate`, lines 380–386.
-/

open Matrix
open scoped BigOperators InnerProductSpace

namespace TNLean.MPS.AreaLaw.EntropyScaling

/-- The flag label and the binary words indexing the terms of `eq:magicstate`
in arXiv:0705.0292v2, lines 382–386. -/
abbrev QutritLabel (N : ℕ) := Unit ⊕ (Fin N → Fin 2)

/-- The flag word is constantly `2`; binary words retain their original letters.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
def qutritWord (N : ℕ) : QutritLabel N → (Fin N → Fin 3)
  | .inl _ => fun _ ↦ 2
  | .inr x => fun i ↦ (x i).castLE (by decide)

/-- The squared Schmidt coefficient of each label in `eq:magicstate`.
Source: arXiv:0705.0292v2, lines 382–386. -/
noncomputable def qutritWeight (N : ℕ) (p : ℝ) : QutritLabel N → ℝ
  | .inl _ => 1 - p
  | .inr _ => p / (2 : ℝ) ^ N

/-- The explicit state in `eq:magicstate`, on the actual chain of `N + N` qutrits.
Source: arXiv:0705.0292v2, lines 382–386. -/
noncomputable def qutritState (N : ℕ) (p : ℝ) :
    EuclideanSpace ℂ (Fin (N + N) → Fin 3) :=
  ∑ i : QutritLabel N, (Real.sqrt (qutritWeight N p i) : ℂ) •
    EuclideanSpace.basisFun (Fin (N + N) → Fin 3) ℂ
      (Fin.append (qutritWord N i) (qutritWord N i))

/-- The choice `p_N = 1/N` in arXiv:0705.0292v2, following `eq:magicstate`,
lines 387–388 and 421–425. -/
noncomputable def qutritFamily (N : ℕ) : EuclideanSpace ℂ (Fin (N + N) → Fin 3) :=
  qutritState N ((N : ℝ)⁻¹)

/-- The two halves of a qutrit-chain configuration. -/
def qutritHalves (N : ℕ) :
    (Fin (N + N) → Fin 3) ≃ (Fin N → Fin 3) × (Fin N → Fin 3) :=
  (Equiv.arrowCongr (finSumFinEquiv.symm) (Equiv.refl (Fin 3))).trans
    (Equiv.sumArrowEquivProdArrow (Fin N) (Fin N) (Fin 3))

/-- Distinct labels in `eq:magicstate` give distinct half-chain words when `N > 0`.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem qutritWord_injective {N : ℕ} (hN : 0 < N) : Function.Injective (qutritWord N) := by
  intro i j h
  cases i <;> cases j
  case inl.inr u x =>
    have he := congrArg (fun f : Fin N → Fin 3 ↦ (f ⟨0, hN⟩).val) h
    change 2 = (x ⟨0, hN⟩).val at he
    omega
  case inl.inl u v => exact congrArg Sum.inl (Subsingleton.elim u v)
  case inr.inr x y =>
    exact congrArg Sum.inr (funext fun i ↦ Fin.castLE_injective (by decide) (congrFun h i))
  case inr.inl x u =>
    have he := congrArg (fun f : Fin N → Fin 3 ↦ (f ⟨0, hN⟩).val) h
    change (x ⟨0, hN⟩).val = 2 at he
    omega

/-- The half-chain vectors in the middle-cut Schmidt decomposition are orthonormal.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
theorem orthonormal_qutritWord {N : ℕ} (hN : 0 < N) :
    Orthonormal ℂ (fun i : QutritLabel N ↦
      EuclideanSpace.basisFun (Fin N → Fin 3) ℂ (qutritWord N i)) :=
  (EuclideanSpace.basisFun (Fin N → Fin 3) ℂ).orthonormal.comp _ (qutritWord_injective hN)

/-- The doubled words in `eq:magicstate` form an orthonormal family.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem orthonormal_qutritFullWord {N : ℕ} (hN : 0 < N) :
    Orthonormal ℂ (fun i : QutritLabel N ↦
      EuclideanSpace.basisFun (Fin (N + N) → Fin 3) ℂ
        (Fin.append (qutritWord N i) (qutritWord N i))) :=
  (EuclideanSpace.basisFun (Fin (N + N) → Fin 3) ℂ).orthonormal.comp _
    (fun i j h ↦ qutritWord_injective hN (funext fun k ↦ by
      simpa using congrFun h (Fin.castAdd N k)))

/-- The weights in `eq:magicstate` are nonnegative for `0 ≤ p ≤ 1`.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem qutritWeight_nonneg (N : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (i : QutritLabel N) : 0 ≤ qutritWeight N p i := by
  cases i with
  | inl _ => exact sub_nonneg.mpr hp'
  | inr _ => exact div_nonneg hp (by positivity)

/-- The squared Schmidt coefficients in `eq:magicstate` have total mass one.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem sum_qutritWeight (N : ℕ) (p : ℝ) : ∑ i, qutritWeight N p i = 1 := by
  simp [qutritWeight, Fintype.sum_sum_type, div_eq_mul_inv, mul_left_comm]

/-- The explicit state in `eq:magicstate` is normalized.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem norm_qutritState {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ‖qutritState N p‖ = 1 := by
  have hinner := (orthonormal_qutritFullWord hN).inner_sum
    (fun i ↦ (Real.sqrt (qutritWeight N p i) : ℂ))
    (fun i ↦ (Real.sqrt (qutritWeight N p i) : ℂ)) Finset.univ
  have hs (i : QutritLabel N) :
      (starRingEnd ℂ) (Real.sqrt (qutritWeight N p i) : ℂ) *
        (Real.sqrt (qutritWeight N p i) : ℂ) = (qutritWeight N p i : ℂ) := by
    simpa [← pow_two] using
      Complex.ofReal_sqrt_sq (qutritWeight N p i) (qutritWeight_nonneg N hp hp' i)
  simp only [hs, ← Complex.ofReal_sum, sum_qutritWeight, Complex.ofReal_one] at hinner
  simpa only [qutritState, hinner, RCLike.one_re, Real.sqrt_one] using
    norm_eq_sqrt_re_inner (𝕜 := ℂ) (qutritState N p)

/-- The source's choice `p_N = 1/N` gives a unit vector for every positive `N`.
Source: arXiv:0705.0292v2, `eq:magicstate` and lines 387–388. -/
theorem norm_qutritFamily {N : ℕ} (hN : 0 < N) : ‖qutritFamily N‖ = 1 := by
  exact norm_qutritState hN (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast hN))

/-- Splitting a concatenated configuration recovers its two halves. -/
@[simp] theorem qutritHalves_append (N : ℕ) (a b : Fin N → Fin 3) :
    qutritHalves N (Fin.append a b) = (a, b) := by
  exact Prod.ext (funext (Fin.append_left a b)) (funext (Fin.append_right a b))

/-- The state written in the two half-chain configuration coordinates. -/
noncomputable def qutritMiddleVector (N : ℕ) (p : ℝ) :
    EuclideanSpace ℂ ((Fin N → Fin 3) × (Fin N → Fin 3)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (qutritHalves N) (qutritState N p)

/-- The coefficient matrix of the explicit state across its middle cut.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
noncomputable def qutritMiddleMatrix (N : ℕ) (p : ℝ) :
    Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ :=
  schmidtCoeffMatrix (WithLp.ofLp (qutritMiddleVector N p))

/-- The columns are the flag and binary computational-basis vectors. -/
noncomputable def qutritBasisMatrix (N : ℕ) :
    Matrix (Fin N → Fin 3) (QutritLabel N) ℂ :=
  fun a i ↦ EuclideanSpace.basisFun (Fin N → Fin 3) ℂ (qutritWord N i) a

/-- Splitting the chain gives the literal product-basis expansion of `eq:magicstate`.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem qutritMiddleVector_eq (N : ℕ) (p : ℝ) :
    qutritMiddleVector N p =
      ∑ i : QutritLabel N, (Real.sqrt (qutritWeight N p i) : ℂ) •
        EuclideanSpace.basisFun ((Fin N → Fin 3) × (Fin N → Fin 3)) ℂ
          (qutritWord N i, qutritWord N i) := by
  simp only [qutritMiddleVector, qutritState, map_sum, map_smul,
    EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single, qutritHalves_append]

/-- The matrix of Schmidt vectors is an isometry for a nonempty half-chain.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
theorem qutritBasisMatrix_conjTranspose_mul_self {N : ℕ} (hN : 0 < N) :
    (qutritBasisMatrix N)ᴴ * qutritBasisMatrix N = 1 := by
  ext i j
  simpa [qutritBasisMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, PiLp.inner_apply,
    Matrix.one_apply, eq_comm]
    using (orthonormal_iff_ite.mp (orthonormal_qutritWord hN) i j)

/-- The Schmidt-vector matrix has real entries. -/
@[simp] theorem qutritBasisMatrix_conjTranspose (N : ℕ) :
    (qutritBasisMatrix N)ᴴ = (qutritBasisMatrix N)ᵀ := by
  ext i a
  simp [qutritBasisMatrix, Matrix.conjTranspose_apply, EuclideanSpace.basisFun_apply]

/-- The explicit middle-cut Schmidt factorization of `eq:magicstate`.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem qutritMiddleMatrix_factorization (N : ℕ) (p : ℝ) :
    qutritMiddleMatrix N p = qutritBasisMatrix N *
      diagonal (fun i ↦ (Real.sqrt (qutritWeight N p i) : ℂ)) *
        (qutritBasisMatrix N)ᴴ := by
  ext a b
  rw [Matrix.mul_apply]
  simp [qutritMiddleMatrix, qutritMiddleVector_eq, Matrix.mul_diagonal,
    qutritBasisMatrix, EuclideanSpace.basisFun_apply, Pi.single_apply,
    ← ite_and, and_comm, mul_comm]

/-- The left marginal of the state in the physical middle-cut coordinates. -/
noncomputable def qutritMiddleMarginal (N : ℕ) (p : ℝ) :
    Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ :=
  partialTraceRight (vecMulVec (WithLp.ofLp (qutritMiddleVector N p))
    (star (WithLp.ofLp (qutritMiddleVector N p))))

/-- The middle marginal has the explicit squared Schmidt coefficients of `eq:magicstate`.
Source: arXiv:0705.0292v2, lines 382–386. -/
theorem qutritMiddleMarginal_factorization {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    qutritMiddleMarginal N p = qutritBasisMatrix N *
      diagonal (fun i ↦ (qutritWeight N p i : ℂ)) * (qutritBasisMatrix N)ᴴ := by
  rw [qutritMiddleMarginal, partialTraceRight_vecMulVec_eq]
  change qutritMiddleMatrix N p * (qutritMiddleMatrix N p)ᴴ = _
  have hdiag :
      diagonal (fun i : QutritLabel N ↦ (Real.sqrt (qutritWeight N p i) : ℂ)) *
        (diagonal (fun i : QutritLabel N ↦ (Real.sqrt (qutritWeight N p i) : ℂ)))ᴴ =
      diagonal (fun i ↦ (qutritWeight N p i : ℂ)) := by
    simp (disch := exact qutritWeight_nonneg N hp hp' _) only
      [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Pi.star_apply,
        Complex.star_def, Complex.conj_ofReal, ← pow_two, Complex.ofReal_sqrt_sq]
  rw [qutritMiddleMatrix_factorization, ← hdiag]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (qutritBasisMatrix N)ᴴ (qutritBasisMatrix N),
    qutritBasisMatrix_conjTranspose_mul_self hN, Matrix.one_mul]

/-- The complete middle-cut squared Schmidt spectrum: the flag weight `1-p`,
`2^N` equal weights `p/2^N`, and the remaining zero eigenvalues. Zero weights are allowed.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
theorem charpoly_qutritMiddleMarginal {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (qutritMiddleMarginal N p).charpoly =
      Polynomial.X ^ (3 ^ N - (1 + 2 ^ N)) *
        ((Polynomial.X - Polynomial.C ((1 - p : ℝ) : ℂ)) *
          (Polynomial.X - Polynomial.C ((p / (2 : ℝ) ^ N : ℝ) : ℂ)) ^ (2 ^ N)) := by
  have hcard := Fintype.card_le_of_injective _ (qutritWord_injective hN)
  rw [qutritMiddleMarginal_factorization hN hp hp', Matrix.mul_assoc,
    Matrix.charpoly_mul_comm_of_le _ _ hcard]
  simp only [Matrix.mul_assoc, qutritBasisMatrix_conjTranspose_mul_self hN,
    Matrix.mul_one, Matrix.charpoly_diagonal]
  simp [QutritLabel, qutritWeight, Fintype.prod_sum_type]

/-- The middle-cut spectrum for the source's choice `p_N = 1/N`.
Source: arXiv:0705.0292v2, `eq:magicstate` and lines 387–388, 421–425. -/
theorem charpoly_qutritFamily_middle {N : ℕ} (hN : 0 < N) :
    (qutritMiddleMarginal N ((N : ℝ)⁻¹)).charpoly =
      Polynomial.X ^ (3 ^ N - (1 + 2 ^ N)) *
        ((Polynomial.X - Polynomial.C ((1 - (N : ℝ)⁻¹ : ℝ) : ℂ)) *
          (Polynomial.X - Polynomial.C (((N : ℝ)⁻¹ / (2 : ℝ) ^ N : ℝ) : ℂ)) ^ (2 ^ N)) := by
  exact charpoly_qutritMiddleMarginal hN (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast hN))

/-- The native left-block configurations at the middle cut, numbered from zero. -/
def qutritLeftConfigurationEquiv (N : ℕ) :
    Entropy.RegionConfig (fun _ : Fin (N + N) ↦ 3) (leftBlock (N + N) N) ≃
      (Fin N → Fin 3) where
  toFun a i := a ⟨Fin.castAdd N i, mem_leftBlock.mpr i.isLt⟩
  invFun a v := a ⟨v.1.val, mem_leftBlock.mp v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The native right-block configurations at the middle cut, numbered from zero. -/
def qutritRightConfigurationEquiv (N : ℕ) :
    ((v : {v : Fin (N + N) // v ∉ leftBlock (N + N) N}) → Fin 3) ≃
      (Fin N → Fin 3) where
  toFun a i := a ⟨Fin.natAdd N i, by
    simpa only [mem_leftBlock, Fin.val_natAdd, not_lt] using Nat.le_add_right N i.val⟩
  invFun a v := a ⟨v.1.val - N, by omega⟩
  left_inv a := funext fun v ↦ congrArg a (Subtype.ext (Fin.ext
    (Nat.add_sub_of_le (Nat.le_of_not_lt (mt mem_leftBlock.mpr v.2)))))
  right_inv a := funext fun i ↦ congrArg a (Fin.ext (Nat.add_sub_cancel_left N i.val))

/-- The numbered half-chain coordinates agree with the native middle-cut decomposition. -/
@[simp] theorem qutritConfigurations_cutEquiv (N : ℕ) (σ : Fin (N + N) → Fin 3) :
    ((qutritLeftConfigurationEquiv N).prodCongr (qutritRightConfigurationEquiv N))
      (Entropy.cutEquiv (fun _ : Fin (N + N) ↦ 3) (leftBlock (N + N) N) σ) =
        qutritHalves N σ := rfl

/-- The native chain cut matrix is the explicit middle coefficient matrix after relabelling.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
theorem cutMatrix_qutritState_reindex (N : ℕ) (p : ℝ) :
    (cutMatrix (qutritState N p) N).reindex
      (qutritLeftConfigurationEquiv N) (qutritRightConfigurationEquiv N) =
        qutritMiddleMatrix N p := by
  ext a b
  change qutritState N p
      ((Entropy.cutEquiv (fun _ : Fin (N + N) ↦ 3) (leftBlock (N + N) N)).symm
        ((qutritLeftConfigurationEquiv N).symm a, (qutritRightConfigurationEquiv N).symm b)) =
    qutritState N p ((qutritHalves N).symm (a, b))
  apply congrArg (qutritState N p)
  apply (qutritHalves N).injective
  rw [← qutritConfigurations_cutEquiv, Equiv.apply_symm_apply]
  simp

/-- The explicit middle marginal is the actual marginal of the first `N` sites,
with its configurations numbered from zero. No normalization hypothesis is needed.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
theorem regionState_qutritState_reindex (N : ℕ) (p : ℝ) :
    (Entropy.regionState (n := fun _ : Fin (N + N) ↦ 3)
      (leftBlock (N + N) N) (qutritState N p)).reindex
        (qutritLeftConfigurationEquiv N) (qutritLeftConfigurationEquiv N) =
          qutritMiddleMarginal N p := by
  rw [Entropy.regionState, qutritMiddleMarginal,
    partialTraceRight_vecMulVec_eq, partialTraceRight_vecMulVec_eq]
  change (cutMatrix (qutritState N p) N * (cutMatrix (qutritState N p) N)ᴴ).reindex
      (qutritLeftConfigurationEquiv N) (qutritLeftConfigurationEquiv N) =
    qutritMiddleMatrix N p * (qutritMiddleMatrix N p)ᴴ
  have hmul := Matrix.reindexLinearEquiv_mul ℂ ℂ
    (qutritLeftConfigurationEquiv N) (qutritRightConfigurationEquiv N)
    (qutritLeftConfigurationEquiv N)
    (cutMatrix (qutritState N p) N) (cutMatrix (qutritState N p) N)ᴴ
  simpa only [Matrix.coe_reindexLinearEquiv, ← Matrix.conjTranspose_reindex,
    cutMatrix_qutritState_reindex] using hmul.symm

/-- The complete squared Schmidt spectrum for the actual first-`N`-site marginal.
Source: arXiv:0705.0292v2, `eq:magicstate`, lines 382–386. -/
theorem charpoly_regionState_qutritState {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (Entropy.regionState (n := fun _ : Fin (N + N) ↦ 3)
      (leftBlock (N + N) N) (qutritState N p)).charpoly =
      Polynomial.X ^ (3 ^ N - (1 + 2 ^ N)) *
        ((Polynomial.X - Polynomial.C ((1 - p : ℝ) : ℂ)) *
          (Polynomial.X - Polynomial.C ((p / (2 : ℝ) ^ N : ℝ) : ℂ)) ^ (2 ^ N)) := by
  simpa only [Matrix.charpoly_reindex] using
    (congrArg Matrix.charpoly (regionState_qutritState_reindex N p)).trans
      (charpoly_qutritMiddleMarginal hN hp hp')

end TNLean.MPS.AreaLaw.EntropyScaling
