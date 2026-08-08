/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixSpectralDecomp
import TNLean.Algebra.MatrixTracePairing
import TNLean.Channel.PartialTrace
import TNLean.Channel.MaximallyEntangled
import TNLean.Channel.TensorMap
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Rectangular Choi–Jamiolkowski representation of maps

This file defines the Choi matrix of a linear map `T : M_d(ℂ) → M_{d'}(ℂ)`
between matrix algebras of possibly different dimensions and proves the full
Choi–Jamiolkowski one-to-one correspondence with the characterization clauses
of Wolf Chapter 2, Proposition 2.1 (Choi–Jamiolkowski representation of maps),
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 60–126.

## Main definitions

* `ChoiRectangular.choiMatrix T`: the Choi matrix
  `τ = (T ⊗ id_d)(|Ω⟩⟨Ω|)` of `T : M_d(ℂ) → M_{d'}(ℂ)`, an operator on
  `ℂ^{d'} ⊗ ℂ^d` (output factor first, input factor second, as in Wolf);
  `|Ω⟩ = (1/√d) Σⱼ |j,j⟩` is the normalized maximally entangled vector on the
  input factor.
* `ChoiRectangular.mapOfChoiMatrix τ`: the inverse correspondence recovering
  `T` from `τ` (Wolf Eq. (2.4)).

## Main results (Wolf Proposition 2.1, Eq. (2.1))

* `ChoiRectangular.mapOfChoiMatrix_choiMatrix` /
  `ChoiRectangular.choiMatrix_mapOfChoiMatrix` — the two assignments are
  mutual inverses
* `ChoiRectangular.trace_pairing` — the trace-pairing formula
  `tr[A T(B)] = d · tr[τ (A ⊗ Bᵀ)]`
* `ChoiRectangular.choiMatrix_isHermitian_iff_hermiticityPreserving` —
  Hermiticity clause: `τ = τ†` iff `T(B†) = T(B)†` for all `B`
* `ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef` —
  complete-positivity clause: `T` is completely positive iff `τ ≥ 0`
* `ChoiRectangular.traceRight_choiMatrix` and
  `ChoiRectangular.unital_iff_traceRight_choiMatrix` — unitality clause:
  `T(𝟙) = 𝟙` iff `tr_B(τ) = 𝟙_{d'}/d`
* `ChoiRectangular.traceLeft_choiMatrix` and
  `ChoiRectangular.tracePreserving_iff_traceLeft_choiMatrix` —
  trace-preservation clause: `tr_A(τ) = (T*(𝟙))ᵀ/d`, hence `T*(𝟙) = 𝟙` iff
  `tr_A(τ) = 𝟙_d/d`
* `ChoiRectangular.trace_choiMatrix` — normalization clause:
  `tr(τ) = tr(T*(𝟙))/d`
* `ChoiRectangular.doublyStochastic_iff_partialTraces_proportional` —
  doubly-stochastic clause: `T(𝟙) ∝ 𝟙` and `T*(𝟙) ∝ 𝟙` iff `tr_A(τ) ∝ 𝟙`
  and `tr_B(τ) ∝ 𝟙`

## Design notes

The TNLean predicate `IsKrausCP` (existence of a rectangular Kraus
representation) is used as the complete-positivity notion, matching the
Kraus-form characterization used in Wolf Theorem 2.1 (Kraus representation).
The square development `ChoiJamiolkowski.choiMatrix` is the specialization
`d = d'`; see `ChoiRectangular.choiMatrix_eq_choiJamiolkowski`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2,
  Proposition 2.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

namespace ChoiRectangular

variable {d d' : ℕ}

/-! ### The rectangular Choi matrix and its inverse -/

/-- The **Choi matrix** of a linear map `T : M_d(ℂ) → M_{d'}(ℂ)`:

  `τ = (T ⊗ id_d)(|Ω⟩⟨Ω|)`

where `|Ω⟩ = (1/√d) Σⱼ |j,j⟩` is the normalized maximally entangled vector on
the input factor `ℂ^d ⊗ ℂ^d`. The result is an operator on `ℂ^{d'} ⊗ ℂ^d`,
indexed by `Fin d' × Fin d` (output factor first, input factor second).

Wolf, Chapter 2, Proposition 2.1, Equation (2.1);
`Notes/WolfNoteTexSource/ch02_representations.tex`, line 66. -/
noncomputable def choiMatrix
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ :=
  Matrix.tensorMapId T (Matrix.omegaProj d)

/-- Elementwise formula:
`τ (i₁,i₂) (j₁,j₂) = (T (bipartiteSlice (|Ω⟩⟨Ω|) i₂ j₂)) i₁ j₁`. -/
theorem choiMatrix_apply
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (i₁ j₁ : Fin d') (i₂ j₂ : Fin d) :
    choiMatrix T (i₁, i₂) (j₁, j₂) =
      (T (Matrix.bipartiteSlice (Matrix.omegaProj d) i₂ j₂)) i₁ j₁ := by
  simp [choiMatrix, Matrix.tensorMapId_apply]

/-- `choiMatrix` as a linear map in the superoperator argument. -/
noncomputable def choiMatrixLinearMap :
    (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) →ₗ[ℂ]
      Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ where
  toFun := choiMatrix
  map_add' T S := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [choiMatrix, Matrix.tensorMapId_apply]
  map_smul' c T := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [choiMatrix, Matrix.tensorMapId_apply]

@[simp] theorem choiMatrix_add
    (T S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    choiMatrix (T + S) = choiMatrix T + choiMatrix S :=
  (choiMatrixLinearMap (d := d) (d' := d')).map_add T S

@[simp] theorem choiMatrix_smul
    (c : ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    choiMatrix (c • T) = c • choiMatrix T :=
  (choiMatrixLinearMap (d := d) (d' := d')).map_smul c T

/-- The **inverse Choi assignment**: for an operator `τ` on `ℂ^{d'} ⊗ ℂ^d`,
the linear map `T : M_d(ℂ) → M_{d'}(ℂ)` with entries

  `T(B) i₁ j₁ = d · Σ_{i₂ j₂} τ (i₁,i₂) (j₁,j₂) · B i₂ j₂`.

This is Wolf, Chapter 2, Equation (2.4), the `τ ↦ T` direction of
Equation (2.1). -/
noncomputable def mapOfChoiMatrix
    (τ : Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ where
  toFun B i₁ j₁ := (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
    τ (i₁, i₂) (j₁, j₂) * B i₂ j₂
  map_add' X Y := by
    ext i₁ j₁
    change (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        τ (i₁, i₂) (j₁, j₂) * (X + Y) i₂ j₂ =
      (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d, τ (i₁, i₂) (j₁, j₂) * X i₂ j₂ +
        (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d, τ (i₁, i₂) (j₁, j₂) * Y i₂ j₂
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i₁ j₁
    change (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        τ (i₁, i₂) (j₁, j₂) * (c • X) i₂ j₂ =
      c • ((d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d, τ (i₁, i₂) (j₁, j₂) * X i₂ j₂)
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    ring

/-! ### The omega slice -/

/-- The `(i₂, j₂)`-slice of `|Ω⟩⟨Ω|` is `(1/d) · E_{i₂,j₂}` for `d > 0`:
the matrix unit scaled by `1/d`. This is the identity
`d |Ω⟩⟨Ω| = F^{T_B}` of Wolf, Example 1.2, used in the proof of
Proposition 2.1. -/
private theorem omegaSlice_eq_single (hd : 0 < d) (i₂ j₂ : Fin d) :
    Matrix.bipartiteSlice (Matrix.omegaProj d) i₂ j₂ =
      (1 / (d : ℂ)) • Matrix.single i₂ j₂ (1 : ℂ) := by
  rw [ChoiJamiolkowski.omegaSlice_eq_single (D := d) i₂ j₂,
    ChoiJamiolkowski.omegaCoeff_eq_inv hd, Matrix.smul_single, smul_eq_mul, mul_one]

/-! ### Mutual inverses -/

section MutualInverse

variable [NeZero d]

/-- The forward-inverse composition `T ↦ τ ↦ T` is the identity: every linear
map is recovered from its Choi matrix. This is the direction `T → τ → T` of
Wolf, Proposition 2.1, proof (Equations (2.2)–(2.3)). -/
theorem mapOfChoiMatrix_choiMatrix
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    mapOfChoiMatrix (choiMatrix T) = T := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext B i₁ j₁
  have hB : B = ∑ i₂ : Fin d, ∑ j₂ : Fin d,
      (B i₂ j₂) • Matrix.single i₂ j₂ (1 : ℂ) := by
    conv_lhs => rw [matrix_eq_sum_single B]
    refine Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hsum2 : (∑ i₂ : Fin d, ∑ j₂ : Fin d,
      (B i₂ j₂) • ((1 / (d : ℂ)) • Matrix.single i₂ j₂ (1 : ℂ))) =
        (1 / (d : ℂ)) • B := by
    conv_rhs => rw [hB]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i₂ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    rw [smul_comm]
  have hstep : ∑ i₂ : Fin d, ∑ j₂ : Fin d,
      choiMatrix T (i₁, i₂) (j₁, j₂) * B i₂ j₂ =
        T ((1 / (d : ℂ)) • B) i₁ j₁ := by
    calc
      ∑ i₂ : Fin d, ∑ j₂ : Fin d, choiMatrix T (i₁, i₂) (j₁, j₂) * B i₂ j₂
          = ∑ i₂ : Fin d, ∑ j₂ : Fin d,
              (T ((B i₂ j₂) • ((1 / (d : ℂ)) • Matrix.single i₂ j₂ (1 : ℂ)))) i₁ j₁ := by
            refine Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => ?_
            simp only [choiMatrix_apply, omegaSlice_eq_single hdpos, map_smul,
              Matrix.smul_apply, smul_eq_mul]
            ring
      _ = (T (∑ i₂ : Fin d, ∑ j₂ : Fin d,
          (B i₂ j₂) • ((1 / (d : ℂ)) • Matrix.single i₂ j₂ (1 : ℂ)))) i₁ j₁ := by
            simp [map_sum, Matrix.sum_apply]
      _ = T ((1 / (d : ℂ)) • B) i₁ j₁ := by
            rw [hsum2]
  change (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
      choiMatrix T (i₁, i₂) (j₁, j₂) * B i₂ j₂ = T B i₁ j₁
  rw [hstep, map_smul, Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- The inverse-forward composition `τ ↦ T ↦ τ` is the identity: every operator
on `ℂ^{d'} ⊗ ℂ^d` is the Choi matrix of the map it defines. This is the
surjectivity of `T ↦ τ` in Wolf, Proposition 2.1, proof. -/
theorem choiMatrix_mapOfChoiMatrix
    (τ : Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ) :
    choiMatrix (mapOfChoiMatrix τ) = τ := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [choiMatrix_apply, omegaSlice_eq_single hdpos, map_smul, Matrix.smul_apply]
  change (1 / (d : ℂ)) • ((d : ℂ) * ∑ a : Fin d, ∑ b : Fin d,
      τ (i₁, a) (j₁, b) * (Matrix.single i₂ j₂ (1 : ℂ)) a b) = τ (i₁, i₂) (j₁, j₂)
  have hsum : ∑ a : Fin d, ∑ b : Fin d,
      τ (i₁, a) (j₁, b) * (Matrix.single i₂ j₂ (1 : ℂ)) a b =
        τ (i₁, i₂) (j₁, j₂) := by
    rw [Finset.sum_eq_single i₂]
    · rw [Finset.sum_eq_single j₂]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · simp
    · intro a _ ha
      rw [Finset.sum_eq_zero]
      intro b _
      simp [ha.symm]
    · simp
  rw [hsum, smul_eq_mul]
  field_simp

/-- The Choi assignment is injective: equal Choi matrices imply equal maps
(Wolf, Proposition 2.1: the correspondence is one-to-one). -/
theorem choiMatrix_injective :
    Function.Injective (choiMatrix (d := d) (d' := d')) := by
  intro T S hTS
  have h := congrArg mapOfChoiMatrix hTS
  simpa [mapOfChoiMatrix_choiMatrix] using h

/-- Equality of Choi matrices implies equality of maps. -/
theorem eq_of_choiMatrix_eq
    {T S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hTS : choiMatrix T = choiMatrix S) : T = S :=
  choiMatrix_injective hTS

end MutualInverse

/-! ### The trace-pairing formula -/

/-- **Trace-pairing formula** (Wolf, Proposition 2.1, Equation (2.1), second
line): for all `A ∈ M_{d'}` and `B ∈ M_d`,

  `tr[A T(B)] = d · tr[τ (A ⊗ Bᵀ)]`. -/
theorem trace_pairing [NeZero d]
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (A : Matrix (Fin d') (Fin d') ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    (A * T B).trace = (d : ℂ) *
      ((choiMatrix T) * kroneckerMap (· * ·) A B.transpose).trace := by
  have hTB : ∀ i₁ j₁ : Fin d', (T B) j₁ i₁ = (d : ℂ) *
      ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        choiMatrix T (j₁, i₂) (i₁, j₂) * B i₂ j₂ := by
    intro i₁ j₁
    have h := congrFun (congrArg DFunLike.coe
      (mapOfChoiMatrix_choiMatrix (d := d) (d' := d') T)) B
    change T B j₁ i₁ = (mapOfChoiMatrix (choiMatrix T) B) j₁ i₁
    rw [h]
  have hswap : (∑ i₁ : Fin d', ∑ j₁ : Fin d', ∑ i₂ : Fin d, ∑ j₂ : Fin d,
      A i₁ j₁ * (choiMatrix T (j₁, i₂) (i₁, j₂) * B i₂ j₂)) =
    ∑ j₁ : Fin d', ∑ i₂ : Fin d, ∑ i₁ : Fin d', ∑ j₂ : Fin d,
      A i₁ j₁ * (choiMatrix T (j₁, i₂) (i₁, j₂) * B i₂ j₂) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_comm]
  calc
    (A * T B).trace = ∑ i₁ : Fin d', ∑ j₁ : Fin d', A i₁ j₁ * (T B) j₁ i₁ := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = (d : ℂ) * ∑ i₁ : Fin d', ∑ j₁ : Fin d', ∑ i₂ : Fin d, ∑ j₂ : Fin d,
          A i₁ j₁ * (choiMatrix T (j₁, i₂) (i₁, j₂) * B i₂ j₂) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j₁ _ => ?_
          rw [hTB i₁ j₁]
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₂ _ => ?_
          ring
    _ = (d : ℂ) * ∑ j₁ : Fin d', ∑ i₂ : Fin d, ∑ i₁ : Fin d', ∑ j₂ : Fin d,
          A i₁ j₁ * (choiMatrix T (j₁, i₂) (i₁, j₂) * B i₂ j₂) := by
          rw [hswap]
    _ = (d : ℂ) * ((choiMatrix T) *
          kroneckerMap (· * ·) A B.transpose).trace := by
          congr 1
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
            Matrix.transpose_apply]
          refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun i₂ _ =>
            Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
          ring

/-! ### Complete positivity correspondence -/

section CPCorrespondence

/-- **Easy direction of the complete-positivity clause** (Wolf, Proposition
2.1): the Choi matrix of a map in rectangular Kraus form
`T(X) = Σⱼ Kⱼ X Kⱼ†` is a sum of rank-one outer products, hence positive
semidefinite. -/
theorem choiMatrix_of_kraus_posSemidef {r : ℕ}
    (K : Fin r → Matrix (Fin d') (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    (choiMatrix T).PosSemidef := by
  classical
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hchoi : choiMatrix T = ∑ j : Fin r,
      Matrix.vecMulVec (fun p : Fin d' × Fin d => c * K j p.1 p.2)
        (star (fun p : Fin d' × Fin d => c * K j p.1 p.2)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rw [choiMatrix_apply, hT, ChoiJamiolkowski.omegaSlice_eq_single (D := d) i₂ j₂,
      Matrix.sum_apply i₁ j₁, Matrix.sum_apply (i₁, i₂) (j₁, j₂)]
    change ∑ x : Fin r,
        (K x * Matrix.single i₂ j₂ (c * star c) * (K x)ᴴ) i₁ j₁ =
      ∑ x : Fin r,
        Matrix.vecMulVec (fun p : Fin d' × Fin d => c * K x p.1 p.2)
          (star (fun p : Fin d' × Fin d => c * K x p.1 p.2)) (i₁, i₂) (j₁, j₂)
    refine Finset.sum_congr rfl ?_
    intro x _
    simpa [Matrix.vecMulVec_apply] using congrArg (fun M => M i₁ j₁)
      (Matrix.mul_single_mul_conjTranspose_eq_vecMulVec (K := K x) (c := c) i₂ j₂)
  rw [hchoi]
  refine Matrix.posSemidef_sum (s := Finset.univ)
    (x := fun i =>
      Matrix.vecMulVec (fun p : Fin d' × Fin d => c * K i p.1 p.2)
        (star (fun p : Fin d' × Fin d => c * K i p.1 p.2))) ?_
  intro i _
  simpa using Matrix.posSemidef_vecMulVec_self_star
    (fun p : Fin d' × Fin d => c * K i p.1 p.2)

/-- The Kraus family reconstructed from a Choi-matrix decomposition into
rank-one outer products: writing `τ = Σₘ |ψₘ⟩⟨ψₘ|`, Wolf's Equation (1.13)
`|ψ⟩ = (X ⊗ 𝟙)|Ω⟩` gives `Kₘ = reshape(ψₘ)/c` with `c = 1/√d` the
maximally-entangled normalization constant. -/
noncomputable def krausOfChoiDecomp {ι : Type*} [Fintype ι]
    (v : ι → (Fin d' × Fin d) → ℂ) : ι → Matrix (Fin d') (Fin d) ℂ :=
  fun m a b => v m (a, b) / ((1 : ℂ) / ((d : ℝ).sqrt : ℂ))

/-- The reconstructed family `krausOfChoiDecomp` is a Kraus representation of
the underlying map (Wolf, Proposition 2.1, proof: decompose `τ` into rank-one
operators `|ψ⟩⟨ψ'|` and use `|ψ⟩ = (X ⊗ 𝟙)|Ω⟩` from Wolf, Equation (1.13)). -/
theorem krausOfChoiDecomp_spec [NeZero d]
    {ι : Type*} [Fintype ι]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (v : ι → (Fin d' × Fin d) → ℂ)
    (hchoi : choiMatrix T = ∑ m : ι, Matrix.vecMulVec (v m) (star (v m))) :
    ∀ X, T X = ∑ m : ι,
      krausOfChoiDecomp (d := d) v m * X * (krausOfChoiDecomp (d := d) v m)ᴴ := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    have hsqrt : (((d : ℝ).sqrt : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.2 (by exact_mod_cast hdpos)
    simp [hsqrt]
  have hstarc : star c = c := by simp [c]
  have hαne : c * star c ≠ 0 := by
    simpa [hstarc] using mul_ne_zero hc hc
  let K : ι → Matrix (Fin d') (Fin d) ℂ := krausOfChoiDecomp (d := d) v
  intro X
  let S : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d') (Fin d') ℂ :=
    fun Y => ∑ m : ι, K m * Y * (K m)ᴴ
  let P : Matrix (Fin d) (Fin d) ℂ → Prop := fun Y => T Y = S Y
  change P X
  have hKeq : ∀ m a b, K m a b = v m (a, b) / c := fun m a b => rfl
  refine Matrix.induction_on X ?_ ?_
  · intro p q hp hq
    dsimp [P, S] at *
    simp [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq, Finset.sum_add_distrib]
  · intro i j z
    dsimp [P, S]
    have hbase : T (Matrix.single i j (1 : ℂ)) = S (Matrix.single i j (1 : ℂ)) := by
      ext a b
      have hentry : T (Matrix.single i j (c * star c)) a b =
          (∑ m : ι, Matrix.vecMulVec (v m) (star (v m))) (a, i) (b, j) := by
        have h := congrArg (fun M => M (a, i) (b, j)) hchoi
        rwa [choiMatrix_apply, ChoiJamiolkowski.omegaSlice_eq_single (D := d) i j] at h
      have hsmul : T (Matrix.single i j (c * star c)) a b =
          (c * star c) * T (Matrix.single i j (1 : ℂ)) a b := by
        simpa [Matrix.smul_single] using congrArg (fun M => M a b)
          (T.map_smul (c * star c) (Matrix.single i j (1 : ℂ)))
      have h1 : (c * star c) * T (Matrix.single i j (1 : ℂ)) a b =
          ∑ m : ι, v m (a, i) * star (v m (b, j)) := by
        exact hsmul.symm.trans <|
          by simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hentry
      have h2 : (c * star c) * S (Matrix.single i j (1 : ℂ)) a b =
          ∑ m : ι, v m (a, i) * star (v m (b, j)) := by
        calc
          (c * star c) * S (Matrix.single i j (1 : ℂ)) a b
              = (c * star c) *
                  ((∑ m : ι, K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b) := rfl
          _ = (c * star c) *
                ∑ m : ι, (K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b := by
                rw [Matrix.sum_apply]
          _ = ∑ m : ι,
                (c * star c) * ((K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b) := by
                rw [Finset.mul_sum]
          _ = ∑ m : ι, v m (a, i) * star (v m (b, j)) := by
                refine Finset.sum_congr rfl ?_
                intro m _
                have hterm : (K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b =
                    (v m (a, i) / c) * star (v m (b, j) / c) := by
                  have h := Matrix.mul_single_mul_conjTranspose_eq_vecMulVec
                    (K := K m) (c := (1 : ℂ)) i j
                  have h' := congrFun (congrFun h a) b
                  simp only [Matrix.vecMulVec_apply] at h'
                  simpa [hKeq] using h'
                rw [hterm]
                simp [div_eq_mul_inv, hstarc, hc, mul_assoc, mul_left_comm, mul_comm]
      exact (mul_left_cancel₀ hαne) (h1.trans h2.symm)
    have hSsmul (Y : Matrix (Fin d) (Fin d) ℂ) : S (z • Y) = z • S Y := by
      dsimp [S]
      simp [Finset.smul_sum]
    calc
      T (Matrix.single i j z) = z • T (Matrix.single i j (1 : ℂ)) := by
        simpa [Matrix.smul_single] using T.map_smul z (Matrix.single i j (1 : ℂ))
      _ = z • S (Matrix.single i j (1 : ℂ)) := by rw [hbase]
      _ = S (z • Matrix.single i j (1 : ℂ)) := by rw [hSsmul]
      _ = S (Matrix.single i j z) := by simp [Matrix.smul_single]

variable [NeZero d]

/-- A Choi-matrix decomposition into rank-one outer products yields a
rectangular Kraus family indexed by the same finite type (existential form of
`krausOfChoiDecomp_spec`). -/
theorem exists_kraus_of_choiMatrix_eq_sum_vecMulVec
    {ι : Type*} [Fintype ι]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (v : ι → (Fin d' × Fin d) → ℂ)
    (hchoi : choiMatrix T = ∑ m : ι, Matrix.vecMulVec (v m) (star (v m))) :
    ∃ K : ι → Matrix (Fin d') (Fin d) ℂ, ∀ X, T X = ∑ m : ι, K m * X * (K m)ᴴ :=
  ⟨krausOfChoiDecomp (d := d) v, krausOfChoiDecomp_spec (T := T) v hchoi⟩

/-- **Complete-positivity clause** (Wolf, Proposition 2.1): a linear map
`T : M_d(ℂ) → M_{d'}(ℂ)` is completely positive — here in the rectangular
Kraus form `IsKrausCP`, matching Wolf, Theorem 2.1 — if and only if its Choi
matrix is positive semidefinite. -/
theorem isKrausCP_iff_choiMatrix_posSemidef
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    IsKrausCP T ↔ (choiMatrix T).PosSemidef := by
  constructor
  · rintro ⟨r, K, hK⟩
    exact choiMatrix_of_kraus_posSemidef K T hK
  · intro hτ
    classical
    obtain ⟨r, v, hchoi⟩ := (Matrix.posSemidef_iff_eq_sum_vecMulVec).mp hτ
    obtain ⟨K, hK⟩ :=
      exists_kraus_of_choiMatrix_eq_sum_vecMulVec (T := T) (ι := Fin r) v hchoi
    exact ⟨r, K, hK⟩

/-- Surjectivity of the Choi assignment on positive semidefinite operators:
every PSD `τ` on `ℂ^{d'} ⊗ ℂ^d` is the Choi matrix of a completely positive
map (Wolf, Proposition 2.1, proof: surjectivity of `T ↦ τ`). -/
theorem exists_isKrausCP_of_posSemidef
    {τ : Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ}
    (hτ : τ.PosSemidef) :
    ∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
      IsKrausCP T ∧ choiMatrix T = τ := by
  refine ⟨mapOfChoiMatrix τ, ?_, choiMatrix_mapOfChoiMatrix τ⟩
  rw [isKrausCP_iff_choiMatrix_posSemidef, choiMatrix_mapOfChoiMatrix]
  exact hτ

end CPCorrespondence

/-! ### Hermiticity correspondence -/

/-- **Hermiticity clause** (Wolf, Proposition 2.1): the Choi matrix is
Hermitian if and only if `T(B†) = T(B)†` for all `B ∈ M_d`. -/
theorem choiMatrix_isHermitian_iff_hermiticityPreserving [NeZero d]
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    (choiMatrix T).IsHermitian ↔
      (∀ B : Matrix (Fin d) (Fin d) ℂ, T (Bᴴ) = (T B)ᴴ) := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h1dne : (1 / (d : ℂ)) ≠ 0 := one_div_ne_zero hdne
  have h1d : star (1 / (d : ℂ)) = 1 / (d : ℂ) := by
    rw [show (1 / (d : ℂ)) = (((1 / d : ℝ)) : ℂ) by push_cast; ring]
    simp
  have hstar1d (y : ℂ) : star ((1 / (d : ℂ)) * y) = (1 / (d : ℂ)) * star y := by
    rw [star_mul, h1d, mul_comm]
  constructor
  · intro hτ
    have hsingle : ∀ i j : Fin d,
        T (Matrix.single j i (1 : ℂ)) = (T (Matrix.single i j (1 : ℂ)))ᴴ := by
      intro i j
      ext a b
      have hentry : (1 / (d : ℂ)) * T (Matrix.single j i (1 : ℂ)) a b =
          star ((1 / (d : ℂ)) * T (Matrix.single i j (1 : ℂ)) b a) := by
        have h := congrArg (fun M => M (a, j) (b, i)) hτ.eq
        simp only [Matrix.conjTranspose_apply, choiMatrix_apply,
          omegaSlice_eq_single hdpos j i, omegaSlice_eq_single hdpos i j,
          map_smul, Matrix.smul_apply, smul_eq_mul] at h
        exact h.symm
      rw [hstar1d] at hentry
      have h := mul_left_cancel₀ h1dne hentry
      rwa [Matrix.conjTranspose_apply]
    intro B
    let P : Matrix (Fin d) (Fin d) ℂ → Prop := fun M => T (Mᴴ) = (T M)ᴴ
    change P B
    refine Matrix.induction_on B ?_ ?_
    · intro p q hp hq; dsimp [P] at *; simp [map_add, hp, hq]
    · intro i j z
      dsimp [P]
      calc
        T ((Matrix.single i j z)ᴴ) = T (Matrix.single j i (star z)) := by
          rw [Matrix.conjTranspose_single]
        _ = (star z) • T (Matrix.single j i (1 : ℂ)) := by
              simpa [Matrix.smul_single] using T.map_smul (star z) (Matrix.single j i (1 : ℂ))
        _ = (star z) • (T (Matrix.single i j (1 : ℂ)))ᴴ := by rw [hsingle]
        _ = (z • T (Matrix.single i j (1 : ℂ)))ᴴ := by simp [Matrix.conjTranspose_smul]
        _ = (T (Matrix.single i j z))ᴴ := by
              simpa [Matrix.smul_single] using
                congrArg Matrix.conjTranspose (T.map_smul z (Matrix.single i j (1 : ℂ))).symm
  · intro hT
    ext ⟨a, i⟩ ⟨b, j⟩
    have hsingle : T (Matrix.single j i (1 : ℂ)) =
        (T (Matrix.single i j (1 : ℂ)))ᴴ := by
      have h := hT (Matrix.single i j (1 : ℂ))
      rwa [Matrix.conjTranspose_single, star_one] at h
    have hentry : star ((1 / (d : ℂ)) * T (Matrix.single j i (1 : ℂ)) b a) =
        (1 / (d : ℂ)) * T (Matrix.single i j (1 : ℂ)) a b := by
      rw [hstar1d, hsingle, Matrix.conjTranspose_apply, star_star]
    simp only [Matrix.conjTranspose_apply, choiMatrix_apply,
      omegaSlice_eq_single hdpos i j, omegaSlice_eq_single hdpos j i,
      map_smul, Matrix.smul_apply, smul_eq_mul]
    exact hentry

/-! ### Partial traces of the Choi matrix -/

section PartialTraceClauses

/-- The diagonal slices of `|Ω⟩⟨Ω|` sum to `(1/d) · 𝟙`. -/
private theorem sum_omegaSlice_diag (hd : 0 < d) :
    ∑ k : Fin d, Matrix.bipartiteSlice (Matrix.omegaProj d) k k =
      (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have h1 : ∑ k : Fin d, Matrix.single k k (1 : ℂ) =
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [Matrix.sum_single_eq_diagonal]
    exact Matrix.diagonal_one
  rw [← h1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [omegaSlice_eq_single hd]

/-- The trace-pairing adjoint of `T` fixes the identity if and only if `T`
preserves the trace. -/
theorem traceAdjointMap_one_eq_one_iff_tracePreserving
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Matrix.traceAdjointMap T 1 = 1 ↔
      ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace := by
  constructor
  · intro h X
    have h1 : (T X).trace = ((Matrix.traceAdjointMap T 1) * X).trace := by
      rw [Matrix.trace_traceAdjointMap_mul, Matrix.one_mul]
    rw [h1, h, Matrix.one_mul]
  · intro h
    apply (Matrix.ext_iff_trace_mul_right).2
    intro N
    rw [Matrix.trace_traceAdjointMap_mul, Matrix.one_mul, h N, Matrix.one_mul]

/-- Cancellation of a nonzero scalar on a matrix equation. -/
private theorem smul_cancel {ι : Type*}
    {M N : Matrix ι ι ℂ} {c : ℂ} (hc : c ≠ 0) (h : c • M = c • N) : M = N := by
  calc M = (1 : ℂ) • M := (one_smul _ _).symm
    _ = (c⁻¹ * c) • M := by rw [inv_mul_cancel₀ hc]
    _ = c⁻¹ • (c • M) := (smul_smul _ _ _).symm
    _ = c⁻¹ • (c • N) := by rw [h]
    _ = (c⁻¹ * c) • N := smul_smul _ _ _
    _ = N := by rw [inv_mul_cancel₀ hc]; exact one_smul _ _

variable [NeZero d]

/-- **Right partial trace of the Choi matrix** (Wolf, Proposition 2.1,
unitality clause): tracing the input factor gives

  `tr_B(τ) = T(𝟙)/d`. -/
theorem traceRight_choiMatrix
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Matrix.traceRight (choiMatrix T) = (1 / (d : ℂ)) • T 1 := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  ext i j
  calc
    Matrix.traceRight (choiMatrix T) i j
        = ∑ k : Fin d, choiMatrix T (i, k) (j, k) := Matrix.traceRight_apply _ _ _
    _ = ∑ k : Fin d, (T (Matrix.bipartiteSlice (Matrix.omegaProj d) k k)) i j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [choiMatrix_apply]
    _ = (T (∑ k : Fin d, Matrix.bipartiteSlice (Matrix.omegaProj d) k k)) i j := by
          rw [map_sum, Matrix.sum_apply]
    _ = (T ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))) i j := by
          rw [sum_omegaSlice_diag hdpos]
    _ = ((1 / (d : ℂ)) • T 1) i j := by
          rw [map_smul]

/-- **Unitality clause** (Wolf, Proposition 2.1): `T(𝟙) = 𝟙` if and only if
`tr_B(τ) = 𝟙_{d'}/d`. -/
theorem unital_iff_traceRight_choiMatrix
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    T 1 = 1 ↔ Matrix.traceRight (choiMatrix T) =
      (1 / (d : ℂ)) • (1 : Matrix (Fin d') (Fin d') ℂ) := by
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [traceRight_choiMatrix]
  constructor
  · intro h; rw [h]
  · intro h
    exact smul_cancel (one_div_ne_zero hdne) h

/-- **Left partial trace of the Choi matrix** (Wolf, Proposition 2.1,
trace-preservation clause): tracing the output factor gives

  `tr_A(τ) = (T*(𝟙))ᵀ/d`

where `T*` is the trace-pairing adjoint. -/
theorem traceLeft_choiMatrix
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Matrix.traceLeft (choiMatrix T) =
      (1 / (d : ℂ)) • (Matrix.traceAdjointMap T 1).transpose := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  ext i j
  calc
    Matrix.traceLeft (choiMatrix T) i j
        = ∑ k : Fin d', choiMatrix T (k, i) (k, j) := Matrix.traceLeft_apply _ _ _
    _ = (T (Matrix.bipartiteSlice (Matrix.omegaProj d) i j)).trace := by
          simp only [choiMatrix_apply]
          simp [Matrix.trace, Matrix.diag]
    _ = (1 / (d : ℂ)) * (T (Matrix.single i j (1 : ℂ))).trace := by
          rw [omegaSlice_eq_single hdpos, map_smul, Matrix.trace_smul, smul_eq_mul]
    _ = (1 / (d : ℂ)) * (Matrix.traceAdjointMap T 1) j i := by
          have h : (Matrix.traceAdjointMap T 1) j i =
              (T (Matrix.single i j (1 : ℂ))).trace := by
            have h2 := Matrix.trace_traceAdjointMap_mul T 1 (Matrix.single i j (1 : ℂ))
            rwa [Matrix.trace_mul_single, Matrix.one_mul, MulOpposite.op_one,
              one_smul] at h2
          rw [h]
    _ = ((1 / (d : ℂ)) • (Matrix.traceAdjointMap T 1).transpose) i j := by
          simp [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]

/-- **Trace-preservation clause** (Wolf, Proposition 2.1): `T` preserves the
trace — equivalently `T*(𝟙) = 𝟙` — if and only if `tr_A(τ) = 𝟙_d/d`. -/
theorem tracePreserving_iff_traceLeft_choiMatrix
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) ↔
      Matrix.traceLeft (choiMatrix T) =
        (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [traceLeft_choiMatrix, ← traceAdjointMap_one_eq_one_iff_tracePreserving]
  constructor
  · intro h
    rw [h, Matrix.transpose_one]
  · intro h
    have hT := smul_cancel (one_div_ne_zero hdne) (N := (1 : Matrix (Fin d) (Fin d) ℂ)) h
    calc Matrix.traceAdjointMap T 1
        = ((1 : Matrix (Fin d) (Fin d) ℂ)).transpose := by
          rw [← Matrix.transpose_transpose (Matrix.traceAdjointMap T 1), hT]
      _ = 1 := Matrix.transpose_one

/-- **Normalization clause** (Wolf, Proposition 2.1):
`tr(τ) = tr(T*(𝟙))/d`. -/
theorem trace_choiMatrix
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    (choiMatrix T).trace = (1 / (d : ℂ)) * (Matrix.traceAdjointMap T 1).trace := by
  rw [Matrix.trace_eq_trace_traceLeft, traceLeft_choiMatrix, Matrix.trace_smul,
    Matrix.trace_transpose, smul_eq_mul]

/-- **Doubly-stochastic clause** (Wolf, Proposition 2.1): `T(𝟙) ∝ 𝟙` and
`T*(𝟙) ∝ 𝟙` if and only if `tr_A(τ) ∝ 𝟙` and `tr_B(τ) ∝ 𝟙`. -/
theorem doublyStochastic_iff_partialTraces_proportional
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    ((∃ c : ℂ, T 1 = c • (1 : Matrix (Fin d') (Fin d') ℂ)) ∧
      (∃ c : ℂ, Matrix.traceAdjointMap T 1 =
        c • (1 : Matrix (Fin d) (Fin d) ℂ))) ↔
    ((∃ c : ℂ, Matrix.traceRight (choiMatrix T) =
        c • (1 : Matrix (Fin d') (Fin d') ℂ)) ∧
      (∃ c : ℂ, Matrix.traceLeft (choiMatrix T) =
        c • (1 : Matrix (Fin d) (Fin d) ℂ))) := by
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h1d : (1 / (d : ℂ)) ≠ 0 := one_div_ne_zero hdne
  rw [traceRight_choiMatrix, traceLeft_choiMatrix]
  constructor
  · rintro ⟨⟨c, hc⟩, ⟨e, he⟩⟩
    refine ⟨⟨(1 / (d : ℂ)) * c, ?_⟩, ⟨(1 / (d : ℂ)) * e, ?_⟩⟩
    · rw [hc, smul_smul]
    · rw [he, Matrix.transpose_smul, Matrix.transpose_one, smul_smul]
  · rintro ⟨⟨c, hc⟩, ⟨e, he⟩⟩
    refine ⟨⟨(d : ℂ) * c, smul_cancel h1d ?_⟩, ⟨(d : ℂ) * e, ?_⟩⟩
    · rw [hc, smul_smul, show (1 / (d : ℂ)) * ((d : ℂ) * c) = c by field_simp]
    · have hT : (Matrix.traceAdjointMap T 1).transpose = ((d : ℂ) * e) • 1 :=
        smul_cancel h1d (by
          rw [he, smul_smul, show (1 / (d : ℂ)) * ((d : ℂ) * e) = e by field_simp])
      calc Matrix.traceAdjointMap T 1
          = (((d : ℂ) * e) • (1 : Matrix (Fin d) (Fin d) ℂ)).transpose := by
            rw [← Matrix.transpose_transpose (Matrix.traceAdjointMap T 1), hT]
        _ = ((d : ℂ) * e) • 1 := by rw [Matrix.transpose_smul, Matrix.transpose_one]

end PartialTraceClauses

/-! ### Specialization to equal dimensions -/

/-- The rectangular Choi matrix at `d = d' = D` is definitionally the square
Choi matrix `ChoiJamiolkowski.choiMatrix`: the existing square development is
the specialization of the present one. -/
theorem choiMatrix_eq_choiJamiolkowski {D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    choiMatrix (d := D) (d' := D) T = ChoiJamiolkowski.choiMatrix T := rfl

end ChoiRectangular
