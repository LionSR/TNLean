/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTwoWallTrial
import QICLean.Kraus.MixedMap
import QICLean.Kraus.MapIterate
import QICLean.Algebra.MatrixAux

/-!
# Finite Gram matrices of a moving domain wall

The single-wall sum has a rectangular correlation matrix and a positive
Gram matrix. Unital normalization of the right block gives exact recurrences;
a stationary Hermitian left density gives their weighted trace recurrence.
The resulting finite weighted mixed-transfer sum is the quantity entering
\(\Xi_R\) in arXiv:1210.6613, proof of Lemma lowenergystates,
lines 1230–1265. Neither asymptotic norm growth nor generic positivity is
assumed or concluded here.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d a b : ℕ}

/-- The rectangular correlation of the source single-wall sum with the
right-block word; arXiv:1210.6613, proof of Lemma lowenergystates. -/
noncomputable def uncleWallCorrelation (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ) :
    Matrix (Fin a) (Fin b) ℂ :=
  ∑ σ : Fin n → Fin d, uncleDomainWallWord A B R (List.ofFn σ) *
    (Kraus.evalWord B (List.ofFn σ))ᴴ

/-- The Gram matrix of the moving-wall coefficients;
arXiv:1210.6613, proof of Lemma lowenergystates. -/
noncomputable def uncleWallGram (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ) :
    Matrix (Fin a) (Fin a) ℂ :=
  ∑ σ : Fin n → Fin d, uncleDomainWallWord A B R (List.ofFn σ) *
    (uncleDomainWallWord A B R (List.ofFn σ))ᴴ

/-- The one-site correlation seed in the finite mixed-transfer expansion;
arXiv:1210.6613, the displayed formula for \(\Xi_R\). -/
noncomputable def uncleWallSeed (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) : Matrix (Fin a) (Fin b) ℂ :=
  ∑ i, R i * (B i)ᴴ

/-- Contracting a rectangular mixed correlation with the wall on its right;
arXiv:1210.6613, the displayed formula for \(\Xi_R\). -/
noncomputable def uncleWallCrossMap (A : MPSTensor d a)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) :
    Matrix (Fin a) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ :=
  ∑ i, (mulLeftLinearMap (n := Fin a) ℂ (A i)).comp
    (mulRightLinearMap (l := Fin a) ℂ ((R i)ᴴ))

@[simp] theorem uncleWallCrossMap_apply (A : MPSTensor d a)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (X : Matrix (Fin a) (Fin b) ℂ) :
    uncleWallCrossMap A R X = ∑ i, A i * X * (R i)ᴴ := by
  simp [uncleWallCrossMap, Matrix.mul_assoc]

@[simp] theorem uncleWallCorrelation_zero (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) : uncleWallCorrelation A B R 0 = 0 := by
  simp [uncleWallCorrelation, uncleDomainWallWord]

@[simp] theorem uncleWallGram_zero (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) : uncleWallGram A B R 0 = 0 := by
  simp [uncleWallGram, uncleDomainWallWord]

/-- Every finite moving-wall Gram matrix is positive semidefinite.
This uses its coefficient sum, not a norm-growth hypothesis. -/
theorem uncleWallGram_posSemidef (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ) :
    (uncleWallGram A B R n).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun σ _ ↦
    Matrix.posSemidef_self_mul_conjTranspose (uncleDomainWallWord A B R (List.ofFn σ))

private theorem sum_ofFn_cons {V : Type*} [AddCommMonoid V]
    (f : List (Fin d) → V) (n : ℕ) :
    ∑ σ : Fin (n + 1) → Fin d, f (List.ofFn σ) =
      ∑ i : Fin d, ∑ τ : Fin n → Fin d, f (i :: List.ofFn τ) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp]
  simp [Fintype.sum_prod_type]

private theorem sum_mul_pair {ι : Type*} [Fintype ι] {r s t u v : ℕ}
    (U : Matrix (Fin r) (Fin s) ℂ) (f : ι → Matrix (Fin s) (Fin t) ℂ)
    (g : ι → Matrix (Fin t) (Fin u) ℂ) (V : Matrix (Fin u) (Fin v) ℂ) :
    (∑ i, U * f i * g i * V) = U * (∑ i, f i * g i) * V := by
  simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

private theorem sum_evalWord_mul_conjTranspose (B : MPSTensor d b)
    (hB : Kraus.mapLM B 1 = 1) (n : ℕ) :
    ∑ σ : Fin n → Fin d, Kraus.evalWord B (List.ofFn σ) *
      (Kraus.evalWord B (List.ofFn σ))ᴴ = 1 := by
  have hpow : ∀ n : ℕ, ((Kraus.mapLM B) ^ n) 1 = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ']
        change Kraus.mapLM B (((Kraus.mapLM B) ^ n) 1) = 1
        rw [ih, hB]
  simpa only [Kraus.mapLM_pow_apply, Matrix.mul_one] using hpow n

/-- The correlation obeys an affine mixed-transfer recurrence under
source unital normalization of the right block; arXiv:1210.6613,
proof of Lemma lowenergystates, formula for \(\Xi_R\). -/
theorem uncleWallCorrelation_succ (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (n : ℕ) :
    uncleWallCorrelation A B R (n + 1) =
      Kraus.mixedMapLM A B (uncleWallCorrelation A B R n) + uncleWallSeed B R := by
  classical
  rw [uncleWallCorrelation, sum_ofFn_cons
    (fun w ↦ uncleDomainWallWord A B R w * (Kraus.evalWord B w)ᴴ) n]
  simp only [uncleDomainWallWord, Kraus.evalWord_cons, Matrix.conjTranspose_mul,
    Matrix.add_mul]
  simp_rw [← Matrix.mul_assoc]
  simp only [Finset.sum_add_distrib, sum_mul_pair]
  rw [sum_evalWord_mul_conjTranspose B hB]
  have hswap :
      (∑ i : Fin d, ∑ σ : Fin n → Fin d,
        A i * uncleDomainWallWord A B R (List.ofFn σ) *
          (Kraus.evalWord B (List.ofFn σ))ᴴ * (B i)ᴴ) =
      ∑ σ : Fin n → Fin d, ∑ i : Fin d,
        A i * uncleDomainWallWord A B R (List.ofFn σ) *
          (Kraus.evalWord B (List.ofFn σ))ᴴ * (B i)ᴴ := Finset.sum_comm
  simpa [uncleWallCorrelation, uncleWallSeed, Kraus.mixedMapLM_apply,
    Matrix.mul_assoc, Matrix.mul_sum, Matrix.sum_mul] using hswap

/-- The finite Gram recurrence separates propagation, both cross terms,
and the one-site wall Gram matrix; arXiv:1210.6613, proof of Lemma
lowenergystates, formula for \(\Xi_R\). -/
theorem uncleWallGram_succ (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (n : ℕ) :
    uncleWallGram A B R (n + 1) =
      Kraus.mapLM A (uncleWallGram A B R n) +
      uncleWallCrossMap A R (uncleWallCorrelation A B R n) +
      (uncleWallCrossMap A R (uncleWallCorrelation A B R n))ᴴ +
      ∑ i, R i * (R i)ᴴ := by
  classical
  let W (σ : Fin n → Fin d) := uncleDomainWallWord A B R (List.ofFn σ)
  let V (σ : Fin n → Fin d) := Kraus.evalWord B (List.ofFn σ)
  have hdiag (i : Fin d) :
      ∑ σ, (A i * W σ) * (A i * W σ)ᴴ =
        A i * uncleWallGram A B R n * (A i)ᴴ := by
    simpa only [uncleWallGram, W, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      sum_mul_pair (A i) W (fun σ ↦ (W σ)ᴴ) (A i)ᴴ
  have hcross (i : Fin d) :
      ∑ σ, (A i * W σ) * (R i * V σ)ᴴ =
        A i * uncleWallCorrelation A B R n * (R i)ᴴ := by
    simpa only [uncleWallCorrelation, W, V, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      sum_mul_pair (A i) W (fun σ ↦ (V σ)ᴴ) (R i)ᴴ
  have hcrossStar (i : Fin d) :
      ∑ σ, (R i * V σ) * (A i * W σ)ᴴ =
        (A i * uncleWallCorrelation A B R n * (R i)ᴴ)ᴴ := by
    simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose (hcross i)
  have hwall (i : Fin d) :
      ∑ σ, (R i * V σ) * (R i * V σ)ᴴ = R i * (R i)ᴴ := by
    have h := sum_mul_pair (R i) V (fun σ ↦ (V σ)ᴴ) (R i)ᴴ
    rw [show (∑ σ, V σ * (V σ)ᴴ) = 1 from
      sum_evalWord_mul_conjTranspose B hB n, Matrix.mul_one] at h
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h
  rw [uncleWallGram, sum_ofFn_cons
    (fun w ↦ uncleDomainWallWord A B R w * (uncleDomainWallWord A B R w)ᴴ) n]
  change (∑ i, ∑ σ, (A i * W σ + R i * V σ) *
    (A i * W σ + R i * V σ)ᴴ) = _
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Finset.sum_add_distrib]
  simp_rw [hdiag, hcross, hcrossStar, hwall]
  simp only [Kraus.mapLM_apply, Kraus.map_apply, uncleWallCrossMap_apply,
    Matrix.conjTranspose_sum]
  abel

/-- Exact finite geometric expansion of the wall correlation;
arXiv:1210.6613, the mixed-transfer sum in \(\Xi_R\). -/
theorem uncleWallCorrelation_eq_sum (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (hB : Kraus.mapLM B 1 = 1) (n : ℕ) :
    uncleWallCorrelation A B R n =
      ∑ k ∈ Finset.range n, ((Kraus.mixedMapLM A B) ^ k) (uncleWallSeed B R) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [uncleWallCorrelation_succ A B R hB, ih]
      simp only [map_sum]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Module.End.one_apply, pow_succ', Module.End.mul_apply]

/-- The weighted Gram coefficient with the canonical left density;
arXiv:1210.6613, the quantity \(\Xi_R\). -/
noncomputable def uncleWallGramWeight (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (n : ℕ) : ℂ :=
  Matrix.trace (ρ * uncleWallGram A B R n)

/-- The finite Gram weight is nonnegative for a positive left density.
This is finite positivity, not strict positivity of the asymptotic coefficient
in arXiv:1210.6613, Lemma lowenergystates. -/
theorem uncleWallGramWeight_nonneg (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosSemidef) (n : ℕ) :
    0 ≤ uncleWallGramWeight A B R ρ n := by
  exact hρ.trace_mul_nonneg (uncleWallGram_posSemidef A B R n)

/-- The scalar cross contraction appearing in the norm calculation;
arXiv:1210.6613, the displayed formula for \(\Xi_R\). -/
noncomputable def uncleWallCrossWeight (A : MPSTensor d a)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) :
    Matrix (Fin a) (Fin b) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin a) ℂ ℂ).comp
    ((mulLeftLinearMap (n := Fin a) ℂ ρ).comp (uncleWallCrossMap A R))

@[simp] theorem uncleWallCrossWeight_apply (A : MPSTensor d a)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (X : Matrix (Fin a) (Fin b) ℂ) :
    uncleWallCrossWeight A R ρ X = Matrix.trace (ρ * uncleWallCrossMap A R X) := rfl

private theorem trace_mul_conjTranspose_eq_star {ρ X : Matrix (Fin a) (Fin a) ℂ}
    (hρ : ρ.IsHermitian) : Matrix.trace (ρ * Xᴴ) = star (Matrix.trace (ρ * X)) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hρ.eq,
    Matrix.trace_mul_comm]

/-- The exact weighted scalar recurrence uses only the source stationary
left density and the unital right block. Hermiticity pairs the cross terms;
arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleWallGramWeight_succ (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.IsHermitian)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1) (n : ℕ) :
    uncleWallGramWeight A B R ρ (n + 1) = uncleWallGramWeight A B R ρ n +
      Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ) +
      (uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R n) +
        star (uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R n))) := by
  rw [uncleWallGramWeight, uncleWallGram_succ A B R hB]
  simp only [Matrix.mul_add, Matrix.trace_add]
  rw [Kraus.mapLM_apply, Kraus.trace_mul_map_eq_trace_adjointMap_mul, hA,
    trace_mul_conjTranspose_eq_star hρ]
  simp only [uncleWallGramWeight, uncleWallCrossWeight_apply]
  ring

private theorem weighted_prefix_succ (g : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((n + 1 - k : ℕ) : ℂ) * g k) =
      (∑ k ∈ Finset.range n, ((n - k : ℕ) : ℂ) * g k) +
        ∑ k ∈ Finset.range (n + 1), g k := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
  rw [← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hsub : n + 1 - k = n - k + 1 := by
    have := Finset.mem_range.mp hk
    omega
  rw [hsub, Nat.cast_add, Nat.cast_one]
  ring

/-- Exact finite weighted mixed-transfer formula for the moving-wall
Gram coefficient. At length two it reads twice the one-site Gram weight
plus twice the real part of the seed cross contraction. This is the finite
sum in \(\Xi_R\), arXiv:1210.6613, proof of Lemma lowenergystates,
lines 1230–1265; asymptotic growth and generic positivity remain separate. -/
theorem uncleWallGramWeight_eq_weighted_sum (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.IsHermitian)
    (hA : Kraus.adjointMap A ρ = ρ) (hB : Kraus.mapLM B 1 = 1) (n : ℕ) :
    uncleWallGramWeight A B R ρ (n + 1) =
      (n + 1 : ℂ) * Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ) +
        ∑ k ∈ Finset.range n, ((n - k : ℕ) : ℂ) *
          (uncleWallCrossWeight A R ρ
              (((Kraus.mixedMapLM A B) ^ k) (uncleWallSeed B R)) +
            star (uncleWallCrossWeight A R ρ
              (((Kraus.mixedMapLM A B) ^ k) (uncleWallSeed B R)))) := by
  classical
  let g : ℕ → ℂ := fun k ↦ uncleWallCrossWeight A R ρ
      (((Kraus.mixedMapLM A B) ^ k) (uncleWallSeed B R)) +
    star (uncleWallCrossWeight A R ρ
      (((Kraus.mixedMapLM A B) ^ k) (uncleWallSeed B R)))
  have hcross (m : ℕ) :
      uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R m) +
          star (uncleWallCrossWeight A R ρ (uncleWallCorrelation A B R m)) =
        ∑ k ∈ Finset.range m, g k := by
    rw [uncleWallCorrelation_eq_sum A B R hB]
    simp only [map_sum, star_sum, g, Finset.sum_add_distrib]
  change uncleWallGramWeight A B R ρ (n + 1) =
    (n + 1 : ℂ) * Matrix.trace (ρ * ∑ i, R i * (R i)ᴴ) +
      ∑ k ∈ Finset.range n, ((n - k : ℕ) : ℂ) * g k
  induction n with
  | zero =>
      rw [uncleWallGramWeight_succ A B R ρ hρ hA hB]
      simp [uncleWallGramWeight]
  | succ n ih =>
      rw [uncleWallGramWeight_succ A B R ρ hρ hA hB, ih, hcross,
        weighted_prefix_succ]
      push_cast
      ring

end MPSTensor
