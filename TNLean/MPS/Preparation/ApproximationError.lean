/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import TNLean.MPS.Core.Correlations
import TNLean.MPS.Preparation.ApproximatingState
import TNLean.Spectral.MPVOverlapTrace
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# The approximation error of the log-depth preparation, normal case

Let `A` be a normal tensor in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`
(arXiv:2307.01696, eq. (5)), and let `λ₂` bound the moduli of the eigenvalues of `E_A` other
than `1`, with correlation length `ξ = -1/log|λ₂|`. Block `q` sites, write `B_q = V P_q` for the
polar decomposition of the blocked tensor, and let `P_∞` be the fixed-point tensor. For `N = qM`
this file proves, for every `0 < γ < 1/2`, explicit forms of

* the overlap estimate of Piroli, Styliaris, and Cirac (arXiv:2103.13367, Supplemental Material,
  "Proof of Theorem MPS_classification", eq. (S29)), quoted as eq. (S9) of arXiv:2307.01696:
  `|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| = O((N/q) e^{-γ q/ξ})`;
* the approximation error of arXiv:2307.01696, Lemma 1 and Lemma 1'(i):
  `ε(φ̃_N, φ_N) = 1 - |⟨φ̃_N|φ_N⟩| = O((N/q) e^{-γ q/ξ})`.

Both are stated as `≤ C y e^{C y}` with `y = (N/q) e^{-γ q/ξ}` and a constant `C` depending only
on `A`, `σ`, `λ₂`, and `γ`, for all `q` and all `M ≥ 1`. This is the form in which the source's
iteration closes (arXiv:2103.13367, eq. `finished`: `ε_q + ε_q² (1 + ε_q/M)^{M-2}`), and it gives
the `O`-bound whenever `y` stays bounded. The variants ending in `_mul` state the `O`-bound
itself, `≤ C (N/q) e^{-γ q/ξ}` for all `q` and all `M ≥ 1`: for `y > 1` it follows from `ε ≤ 1`
and from the boundedness of the norms `‖φ_N(A)‖`.

## Proof outline (following arXiv:2103.13367)

1. **Transfer-map gap.** `‖E_A^n(X) - Tr(X) σ‖ ≤ C r^n ‖X‖` with `r = e^{-2γ/ξ}`, which exceeds
   the spectral radius of `E_A - |σ⟩⟨1|` because `2γ < 1` (the bound `‖R‖ ≤ Λ(q) e^{-αq}`, eq.
   `difference`).
2. **Positive parts.** `P_q² - P_∞²` is a rearrangement of `E_A^q - |σ⟩⟨1|`, and
   `‖√X - √Y‖ ≤ √‖X - Y‖` (eq. `intermediate`) gives `‖P_q - P_∞‖ ≤ C e^{-γ q/ξ}`.
3. **Telescoping.** For an idempotent `T_∞` and `‖T - T_∞‖ ≤ δ`,
   `‖T^M - T_∞^M‖ ≤ c((1 + cδ)^M - 1)` (eqs. `final_eq` to `finished`), applied to the mixed
   transfer matrices `τ_{AB}` and `τ_{BB}` of `P_q` against `P_∞`.
4. **Normalization.** `c_N² = Tr E_A^N` differs from `1` by `O(e^{-2γN/ξ})`, and the triangle
   inequality of arXiv:2307.01696, proof of Lemma 1'(i), combines the two errors. Since `N ≥ q`
   the normalization term is dominated by the overlap term; no condition `q = o(N)` is needed.

## Main declarations

* `norm_pow_sub_pow_le_of_isIdempotentElem` — the telescoping bound of step 3.
* `CFC.norm_sqrt_sub_sqrt_le` — `‖√a - √b‖ ≤ √‖a - b‖` in a C⋆-algebra.
* `MPSTensor.exists_norm_transferMap_pow_sub_le` — the transfer-map gap of step 1.
* `MPSTensor.exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le` and its `O`-form
  `MPSTensor.exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le_mul` — the overlap estimate
  (S29) of arXiv:2103.13367.
* `MPSTensor.normalizedMPVState`, `MPSTensor.approximatingMPVState` — the normalized states
  `φ_N` and `φ̃_N`.
* `MPSTensor.exists_approximationError_le` and its `O`-form
  `MPSTensor.exists_approximationError_le_mul` — the approximation error, Lemma 1'(i).

## References

* arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification" (eqs.
  `difference`, `final_eq`, `intermediate`, `inequality`, `almost_done`, `finished`).
* arXiv:2307.01696, Lemma 1 (`lm:1`), eq. (17) (`eq:fid_err`), and Supplemental Material,
  "Proof of Lemma 1 and extension to non-normal tensors", eq. (S9) (`eq:app_error`) and
  Lemma 1'(i) (`eq:fid_err_gen_normal`).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal InnerProductSpace
open Filter Topology

/-! ### Telescoping in a normed ring -/

/-- The telescoping identity `X^n - E^n = ∑_{k<n} X^k (X - E) E^{n-1-k}` in a ring.

arXiv:2103.13367, eq. `final_eq` (second line). -/
theorem pow_sub_pow_eq_sum_mul_sub_mul {R : Type*} [Ring R] (X E : R) (n : ℕ) :
    X ^ n - E ^ n = ∑ k ∈ Finset.range n, X ^ k * (X - E) * E ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    have h : ∑ k ∈ Finset.range n, X ^ k * (X - E) * E ^ (n - k) = (X ^ n - E ^ n) * E := by
      rw [ih, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.1 hk
      rw [mul_assoc (X ^ k * (X - E)), ← pow_succ, show n - 1 - k + 1 = n - k by omega]
    rw [h, pow_succ X n, pow_succ E n]
    noncomm_ring

/-- **Telescoping bound for a perturbed idempotent.** In a normed ring, let `E` be idempotent
with `‖E‖ ≤ c` and `‖1‖ ≤ c`, and let `‖X - E‖ ≤ δ`. Then
`‖X^M - E^M‖ ≤ c ((1 + cδ)^M - 1)`.

This is the iteration of arXiv:2103.13367, eqs. `final_eq`, `inequality`, `almost_done`, and
`finished`: `E^k = E` for `k ≥ 1` bounds every factor `E^k` by `c`, and
`‖X^k‖ ≤ c + ‖X^k - E^k‖` feeds the bound back into the telescoping sum. -/
theorem norm_pow_sub_pow_le_of_isIdempotentElem {R : Type*} [NormedRing R] {E X : R}
    (hE : IsIdempotentElem E) {c δ : ℝ} (hEc : ‖E‖ ≤ c) (h1c : ‖(1 : R)‖ ≤ c)
    (hδ : ‖X - E‖ ≤ δ) (M : ℕ) :
    ‖X ^ M - E ^ M‖ ≤ c * ((1 + c * δ) ^ M - 1) := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hEc
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hEpow : ∀ k : ℕ, ‖E ^ k‖ ≤ c := fun k => by
    rcases k with _ | k
    · simpa using h1c
    · rw [hE.pow_succ_eq]; exact hEc
  -- The closed form `b n = c ((1 + cδ)^n - 1)` solves `b n = ∑_{k<n} (c + b k) c δ`.
  have hclosed : ∀ n : ℕ, ∑ k ∈ Finset.range n, (c + c * ((1 + c * δ) ^ k - 1)) * δ * c =
      c * ((1 + c * δ) ^ n - 1) := fun n => by
    have hg := geom_sum_mul (1 + c * δ) n
    simp only [add_sub_cancel_left] at hg
    calc ∑ k ∈ Finset.range n, (c + c * ((1 + c * δ) ^ k - 1)) * δ * c
        = c * ((∑ k ∈ Finset.range n, (1 + c * δ) ^ k) * (c * δ)) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = c * ((1 + c * δ) ^ n - 1) := by rw [hg]
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rw [pow_sub_pow_eq_sum_mul_sub_mul, ← hclosed M]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk := Finset.mem_range.1 hk
    have hXk : ‖X ^ k‖ ≤ c + c * ((1 + c * δ) ^ k - 1) := by
      calc ‖X ^ k‖ = ‖E ^ k + (X ^ k - E ^ k)‖ := by rw [add_sub_cancel]
        _ ≤ ‖E ^ k‖ + ‖X ^ k - E ^ k‖ := norm_add_le _ _
        _ ≤ c + c * ((1 + c * δ) ^ k - 1) := add_le_add (hEpow k) (ih k hk)
    calc ‖X ^ k * (X - E) * E ^ (M - 1 - k)‖
        ≤ ‖X ^ k‖ * ‖X - E‖ * ‖E ^ (M - 1 - k)‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ (c + c * ((1 + c * δ) ^ k - 1)) * δ * c :=
          mul_le_mul (mul_le_mul hXk hδ (norm_nonneg _) ((norm_nonneg _).trans hXk)) (hEpow _)
            (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hXk) hδ0)

/-- `(1 + y)^M - 1 ≤ M y e^{M y}` for `y ≥ 0`: the last step of arXiv:2103.13367, eq.
`finished`, `ε_q + ε_q² (1 + ε_q/M)^{M-2} = ε_q + ε_q² e^{ε_q} (1 + O(ε_q/M))`. -/
theorem one_add_pow_sub_one_le_mul_exp {y : ℝ} (hy : 0 ≤ y) (M : ℕ) :
    (1 + y) ^ M - 1 ≤ M * y * Real.exp (M * y) := by
  have ht : 0 ≤ (M : ℝ) * y := mul_nonneg M.cast_nonneg hy
  have h1 : (1 + y) ^ M ≤ Real.exp (M * y) := by
    calc (1 + y) ^ M ≤ Real.exp y ^ M := by
          gcongr
          linarith [Real.add_one_le_exp y]
      _ = Real.exp (M * y) := (Real.exp_nat_mul y M).symm
  have h2 : Real.exp (M * y) - 1 ≤ M * y * Real.exp (M * y) := by
    have := Real.add_one_le_exp (-((M : ℝ) * y))
    have hprod : Real.exp (M * y) * Real.exp (-(M * y)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos ((M : ℝ) * y)]
  linarith

/-! ### Square roots in a C⋆-algebra -/

/-- A selfadjoint element with `-r ≤ a ≤ r` has norm at most `r`. -/
theorem IsSelfAdjoint.norm_le_of_le_algebraMap {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : a ≤ algebraMap ℝ A r) (h₂ : -algebraMap ℝ A r ≤ a) : ‖a‖ ≤ r := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim a 0, norm_zero]; exact hr
  have hup := (le_algebraMap_iff_spectrum_le (R := ℝ) ha).1 h₁
  have hlo := (algebraMap_le_iff_le_spectrum (R := ℝ) ha).1 (by rwa [map_neg])
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
  · exact hup _ h
  · linarith [hlo _ h]

/-- Upper half of `CFC.norm_sqrt_sub_sqrt_le`: `√a - √b ≤ √‖a - b‖`. -/
theorem CFC.sqrt_sub_sqrt_le_algebraMap {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    CFC.sqrt a - CFC.sqrt b ≤ algebraMap ℝ A (Real.sqrt ‖a - b‖) := by
  set ε := ‖a - b‖
  set S := CFC.sqrt b
  set c := algebraMap ℝ A (Real.sqrt ε)
  have h₁ : a ≤ b + algebraMap ℝ A ε :=
    sub_le_iff_le_add'.1 (IsSelfAdjoint.le_algebraMap_norm_self (ha.isSelfAdjoint.sub hb.isSelfAdjoint))
  have hS : 0 ≤ S := CFC.sqrt_nonneg b
  have hcS : c * S = Real.sqrt ε • S := (Algebra.smul_def _ _).symm
  have hSc : S * c = Real.sqrt ε • S := by rw [← Algebra.commutes, hcS]
  have hcc : c * c = algebraMap ℝ A ε := by
    rw [← map_mul, Real.mul_self_sqrt (norm_nonneg _)]
  have hc : 0 ≤ c := by
    simp only [c, Algebra.algebraMap_eq_smul_one]; exact smul_nonneg (Real.sqrt_nonneg _) zero_le_one
  have hsq : b + algebraMap ℝ A ε ≤ (S + c) ^ 2 := by
    have hexp : (S + c) ^ 2 = b + algebraMap ℝ A ε + (Real.sqrt ε • S + Real.sqrt ε • S) := by
      rw [sq, add_mul, mul_add, mul_add, CFC.sqrt_mul_sqrt_self b hb, hcS, hSc, hcc]
      abel
    rw [hexp]
    exact le_add_of_nonneg_right
      (add_nonneg (smul_nonneg (Real.sqrt_nonneg _) hS) (smul_nonneg (Real.sqrt_nonneg _) hS))
  have h₂ : CFC.sqrt a ≤ S + c :=
    calc CFC.sqrt a ≤ CFC.sqrt (b + algebraMap ℝ A ε) := CFC.sqrt_le_sqrt _ _ h₁
      _ ≤ CFC.sqrt ((S + c) ^ 2) := CFC.sqrt_le_sqrt _ _ hsq
      _ = S + c := CFC.sqrt_sq (S + c) (add_nonneg hS hc)
  exact sub_le_iff_le_add'.2 h₂

/-- **Square roots are `1/2`-Hölder**: for `a, b ≥ 0` in a C⋆-algebra,
`‖√a - √b‖ ≤ √‖a - b‖`.

arXiv:2103.13367, eq. `intermediate` (the bound `‖√X - √Y‖_∞ ≤ √‖X - Y‖_∞` for `X, Y ≥ 0`,
quoted there from Bhatia). -/
theorem CFC.norm_sqrt_sub_sqrt_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖CFC.sqrt a - CFC.sqrt b‖ ≤ Real.sqrt ‖a - b‖ := by
  refine IsSelfAdjoint.norm_le_of_le_algebraMap
    ((CFC.sqrt_nonneg a).isSelfAdjoint.sub (CFC.sqrt_nonneg b).isSelfAdjoint)
    (Real.sqrt_nonneg _) (CFC.sqrt_sub_sqrt_le_algebraMap ha hb) ?_
  have h := CFC.sqrt_sub_sqrt_le_algebraMap hb ha
  rw [norm_sub_rev] at h
  rw [neg_le, neg_sub]
  exact h

/-! ### Isometries on every site preserve inner products -/

/-- An isometry `W : ℂ^κ → ℂ^n` applied on every site preserves inner products of vectors on
`M` sites: `⟨W^{⊗M} ψ, W^{⊗M} φ⟩ = ⟨ψ, φ⟩`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): `⟨φ̃_N|φ_N⟩` reduces to
`⟨Ω|φ_pos⟩` because `V^{⊗N/q}` acts isometrically. -/
theorem Matrix.IsIsometry.sum_star_mul_tensorPower {n κ : Type*} [Fintype n] [Fintype κ]
    [DecidableEq κ] {W : Matrix n κ ℂ} (hW : W.IsIsometry) {M : ℕ}
    (ψ φ : (Fin M → κ) → ℂ) :
    ∑ s : Fin M → n, star (∑ τ, (∏ j, W (s j) (τ j)) * ψ τ) * ∑ τ, (∏ j, W (s j) (τ j)) * φ τ =
      ∑ τ, star (ψ τ) * φ τ := by
  classical
  have hcol : ∀ a b : κ, ∑ i, star (W i a) * W i b = if a = b then 1 else 0 := fun a b => by
    have h := congrFun (congrFun hW a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.conjTranspose_apply] using h
  have hprod : ∀ τ τ' : Fin M → κ,
      ∑ s : Fin M → n, ∏ j, (star (W (s j) (τ j)) * W (s j) (τ' j)) =
        if τ = τ' then 1 else 0 := fun τ τ' => by
    rw [← Fintype.prod_sum (fun j i => star (W i (τ j)) * W i (τ' j))]
    simp only [hcol]
    by_cases h : τ = τ'
    · subst h; simp
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
      rw [ite_eq_right_iff.2 fun h' => absurd h' h]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right_iff.2 fun h' => absurd h' hj)
  calc ∑ s : Fin M → n, star (∑ τ, (∏ j, W (s j) (τ j)) * ψ τ) *
        ∑ τ, (∏ j, W (s j) (τ j)) * φ τ
      = ∑ s : Fin M → n, ∑ τ, ∑ τ', (∏ j, (star (W (s j) (τ j)) * W (s j) (τ' j))) *
          (star (ψ τ) * φ τ') := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [star_sum, star_mul, star_prod, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun τ' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ τ, ∑ τ', (∑ s : Fin M → n, ∏ j, (star (W (s j) (τ j)) * W (s j) (τ' j))) *
          (star (ψ τ) * φ τ') := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    _ = ∑ τ, star (ψ τ) * φ τ := by
        simp only [hprod, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]

/-! ### Entries and norms of matrices -/

section MatrixEntries

open scoped Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The operator norm of a matrix is at most the sum of its entries weighted by the norms of the
matrix units. -/
theorem Matrix.l2_opNorm_le_sum_norm_entry (M : Matrix m n ℂ) :
    ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖(Matrix.single i j 1 : Matrix m n ℂ)‖ := by
  conv_lhs => rw [M.matrix_eq_sum_single]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], norm_smul]

omit [DecidableEq m] in
/-- The entries of a matrix are bounded by a fixed multiple of its operator norm. -/
theorem Matrix.exists_norm_entry_le_mul_l2_opNorm :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : Matrix m n ℂ) (i : m) (j : n), ‖Y i j‖ ≤ K * ‖Y‖ := by
  let f : m → n → (Matrix m n ℂ →L[ℂ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  refine ⟨∑ i, ∑ j, ‖f i j‖, by positivity, fun Y i j => ?_⟩
  calc ‖Y i j‖ = ‖f i j Y‖ := rfl
    _ ≤ ‖f i j‖ * ‖Y‖ := (f i j).le_opNorm Y
    _ ≤ (∑ i, ∑ j, ‖f i j‖) * ‖Y‖ := by
        gcongr
        exact (Finset.single_le_sum (f := fun j => ‖f i j‖) (fun _ _ => by positivity)
          (Finset.mem_univ j)).trans (Finset.single_le_sum
            (f := fun i => ∑ j, ‖f i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))

/-- A linear map between finite-dimensional normed spaces is bounded. -/
theorem LinearMap.exists_norm_apply_le_mul {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E →ₗ[ℂ] F) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖f x‖ ≤ K * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap f‖, norm_nonneg _,
    fun x => (LinearMap.toContinuousLinearMap f).le_opNorm x⟩

end MatrixEntries

namespace MPSTensor

variable {d D : ℕ}

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ### The transfer-map gap at rate `e^{-2γ/ξ}` -/

/-- `-γ/ξ = γ log|λ₂|` for the correlation length `ξ = -1/log|λ₂|` (the value `ξ = 0` at
`λ₂ = 0`, or at `|λ₂| = 1`, gives `0` on both sides). -/
theorem neg_div_correlationLength (γ : ℝ) (lam₂ : ℂ) :
    -γ / correlationLength lam₂ = γ * Real.log ‖lam₂‖ := by
  unfold correlationLength
  rcases eq_or_ne (Real.log ‖lam₂‖) 0 with h | h
  · simp [h]
  · field_simp

/-- For `0 < γ < 1/2`, the rate `e^{-2γ/ξ} = |λ₂|^{2γ}` strictly exceeds every `a < 1` with
`a ≤ |λ₂|`. This is where `γ < 1/2` enters: `|λ₂|^{2γ} > |λ₂|` for `|λ₂| < 1`.

arXiv:2307.01696, eq. (S9) (`0 < γ < 1/2`), and arXiv:2103.13367, the choice `β < α/2` after
eq. `finished`. -/
theorem lt_exp_neg_div_correlationLength_sq {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2)
    {lam₂ : ℂ} {a : ℝ} (ha1 : a < 1) (ha : a ≤ ‖lam₂‖) :
    a < Real.exp (-γ / correlationLength lam₂) ^ 2 := by
  rw [neg_div_correlationLength, ← Real.exp_nat_mul]
  push_cast
  rcases le_or_gt 0 (Real.log ‖lam₂‖) with hl | hl
  · have : 1 ≤ Real.exp (2 * (γ * Real.log ‖lam₂‖)) := Real.one_le_exp (by positivity)
    linarith
  · have ht : 0 < ‖lam₂‖ := by
      rcases (norm_nonneg lam₂).lt_or_eq with h | h
      · exact h
      · rw [← h, Real.log_zero] at hl; exact absurd hl (lt_irrefl 0)
    calc a ≤ ‖lam₂‖ := ha
      _ = Real.exp (Real.log ‖lam₂‖) := (Real.exp_log ht).symm
      _ < Real.exp (2 * (γ * Real.log ‖lam₂‖)) := Real.exp_lt_exp.2 (by nlinarith)

/-- The eigenvalues of `E_A - |σ⟩⟨1|` for a normal tensor: each has modulus `< 1` and at most
`|λ₂|` when `λ₂` bounds the moduli of the eigenvalues of `E_A` other than `1`.

arXiv:2103.13367, the decomposition `τ_AA = τ_BB + R` before eq. `difference`: `R` carries the
Jordan blocks of the subleading eigenvalues. -/
theorem norm_le_of_hasEigenvalue_transferMap_sub_fixedPointProj [NeZero D] (A : MPSTensor d D)
    (hN : IsNormalTensor A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace ≠ 0) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {z : ℂ} (hz : Module.End.HasEigenvalue (Kraus.transferMap A - fixedPointProj σ htr) z) :
    ‖z‖ < 1 ∧ ‖z‖ ≤ ‖lam₂‖ := by
  classical
  have hCh := Kraus.isChannel_mapLM A hA
  have hIrr := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hN.no_invariant_proj
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at htr
  refine ⟨compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel _ hCh hIrr σ hfix hσ0
    htr hN.primitive_transfer z hz, ?_⟩
  obtain ⟨X, hX⟩ := hz.exists_hasEigenvector
  have hNX := Module.End.mem_eigenspace_iff.mp hX.1
  have hEX : Kraus.transferMap A X = z • X + fixedPointProj σ htr X := by
    rw [← sub_eq_iff_eq_add]; exact hNX
  by_cases htrX : X.trace = 0
  · have hPX : fixedPointProj σ htr X = 0 := by simp [fixedPointProj, htrX]
    rw [hPX, add_zero] at hEX
    refine hlam z (hasEigenvalue_of_eigenvector_eq _ z X hEX hX.2) fun hz1 => hX.2 ?_
    rw [hz1, one_smul] at hEX
    exact fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel hCh hIrr X hEX htrX
  · have htp := hCh.tp X
    rw [hEX, Matrix.trace_add, Matrix.trace_smul] at htp
    have hPtr : (fixedPointProj σ htr X).trace = X.trace := by
      change ((X.trace / σ.trace) • σ).trace = X.trace
      rw [Matrix.trace_smul, smul_eq_mul, div_mul_cancel₀ _ htr]
    rw [hPtr, smul_eq_mul, add_eq_right, mul_eq_zero] at htp
    rw [htp.resolve_right htrX, norm_zero]
    exact norm_nonneg _

open scoped Matrix.Norms.L2Operator in
/-- **Transfer-map gap.** Let `A` be normal in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`,
`σ > 0`, `Tr σ = 1`, let `λ₂` bound the moduli of the eigenvalues of `E_A` other than `1`, with
correlation length `ξ`, and let `0 < γ < 1/2`. Then there is `C > 0` with
`‖E_A^n(X) - Tr(X) σ‖ ≤ C e^{-2γ n/ξ} ‖X‖` for all `n` and `X`.

arXiv:2103.13367, eq. `difference`: `‖R^q‖ ≤ Λ(q) e^{-αq}` with `e^{-α} = |λ₁|`; the polynomial
prefactor `Λ(q)` is absorbed into the rate `e^{-2γ/ξ} > |λ₂|`. -/
theorem exists_norm_transferMap_pow_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
      ‖(Kraus.transferMap A ^ n) X - X.trace • σ‖ ≤
        C * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ n * ‖X‖ := by
  classical
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have hCh := Kraus.isChannel_mapLM A hA
  have htr' : σ.trace ≠ 0 := by simp [htr]
  let Φ : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ] _ :=
    Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
  let N := Kraus.transferMap A - fixedPointProj σ htr'
  set x := Real.exp (-γ / correlationLength lam₂)
  let r : ℝ≥0 := ⟨x ^ 2, by positivity⟩
  have hrad : spectralRadius ℂ (Φ N) < (r : ℝ≥0∞) := by
    refine spectrum.spectralRadius_lt_of_forall_lt _ fun z hz => ?_
    rw [AlgEquiv.spectrum_eq] at hz
    obtain ⟨h1, h2⟩ := norm_le_of_hasEigenvalue_transferMap_sub_fixedPointProj A hNT hA hσ htr'
      hfix hlam (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    exact lt_exp_neg_div_correlationLength_sq hγ0 hγ h1 h2
  obtain ⟨C₀, hC₀, hgeom⟩ := geometric_apply_bound_of_spectralRadius_lt (Φ N) r hrad
  let P' := Φ (fixedPointProj σ htr')
  refine ⟨C₀ + (1 + ‖P'‖), by positivity, fun n X => ?_⟩
  have hPX : fixedPointProj σ htr' X = X.trace • σ := by
    change (X.trace / σ.trace) • σ = X.trace • σ
    rw [htr, div_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_zero, mul_one, Module.End.one_apply, ← hPX]
    calc ‖X - fixedPointProj σ htr' X‖ ≤ ‖X‖ + ‖P' X‖ := norm_sub_le _ _
      _ ≤ ‖X‖ + ‖P'‖ * ‖X‖ := by gcongr; exact P'.le_opNorm X
      _ ≤ (C₀ + (1 + ‖P'‖)) * ‖X‖ := by nlinarith [norm_nonneg X]
  · have hpow := pow_eq_fixedPointProj_add_compl_pow (E := Kraus.transferMap A) htr' hCh.tp
      hfix hn
    calc ‖(Kraus.transferMap A ^ n) X - X.trace • σ‖ = ‖((Φ N) ^ n) X‖ := by
          rw [hpow, ← hPX, LinearMap.add_apply, add_sub_cancel_left, ← map_pow]; rfl
      _ ≤ C₀ * (r : ℝ) ^ n * ‖X‖ := hgeom n X
      _ ≤ (C₀ + (1 + ‖P'‖)) * (x ^ 2) ^ n * ‖X‖ := by
          have : 0 ≤ ‖P'‖ := norm_nonneg _
          have hr : (r : ℝ) = x ^ 2 := rfl
          rw [hr]
          gcongr
          linarith

/-! ### The positive part approaches the fixed point at rate `e^{-γ q/ξ}` -/

/-- The entries of `σᵀ ⊗ 1` are those of the rank-one map `X ↦ Tr(X) σ`, rearranged as in
`conjTranspose_physicalMatrix_mul_apply`. -/
theorem transpose_kronecker_one_apply (σ : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D × Fin D) :
    (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) a b =
      ((Matrix.single b.2 a.2 (1 : ℂ)).trace • σ) b.1 a.1 := by
  by_cases hab : a.2 = b.2
  · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hab, Matrix.trace_single_eq_same]
  · simp [Matrix.kroneckerMap_apply, hab, Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]

open scoped Matrix.Norms.L2Operator in
/-- **Gram matrices.** In the setting of `exists_norm_transferMap_pow_sub_le`, the Gram matrix
`B_q† B_q = P_q²` of the `q`-site blocked tensor is `e^{-2γ q/ξ}`-close to
`σᵀ ⊗ 1 = P_∞²`.

arXiv:2103.13367, eq. `difference` (`τ_AA = τ_BB + R`, read with the lower lines as input). -/
theorem exists_norm_gram_blockTensor_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖(physicalMatrix (blockTensor A q))ᴴ * physicalMatrix (blockTensor A q) -
          σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q := by
  obtain ⟨C, hC, hgap⟩ := exists_norm_transferMap_pow_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₂, hK₂, hent⟩ :=
    Matrix.exists_norm_entry_le_mul_l2_opNorm (m := Fin D) (n := Fin D)
  set r := Real.exp (-γ / correlationLength lam₂) ^ 2
  refine ⟨∑ a : Fin D × Fin D, ∑ b : Fin D × Fin D,
    K₂ * C * ‖(Matrix.single b.2 a.2 1 : Matrix (Fin D) (Fin D) ℂ)‖ *
      ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖,
    by positivity, fun q => ?_⟩
  refine (Matrix.l2_opNorm_le_sum_norm_entry _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  set Y : Matrix (Fin D) (Fin D) ℂ := Matrix.single b.2 a.2 1
  have hab : ((physicalMatrix (blockTensor A q))ᴴ * physicalMatrix (blockTensor A q) -
      σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) a b =
      ((Kraus.transferMap A ^ q) Y - Y.trace • σ) b.1 a.1 := by
    rw [Matrix.sub_apply, conjTranspose_physicalMatrix_mul_apply, transferMap_blockTensor,
      transpose_kronecker_one_apply, Matrix.sub_apply]
  rw [hab]
  have hr : 0 ≤ r := by positivity
  calc ‖((Kraus.transferMap A ^ q) Y - Y.trace • σ) b.1 a.1‖ *
        ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖
      ≤ (K₂ * (C * r ^ q * ‖Y‖)) *
          ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ := by
        gcongr
        exact (hent _ _ _).trans (by gcongr; exact hgap q Y)
    _ = K₂ * C * ‖Y‖ *
          ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ * r ^ q := by
        ring

/-- The fixed-point tensor `P_∞`, read as a `D² × D²` matrix, is the square root of
`σᵀ ⊗ 1`. -/
theorem sqrt_transpose_kronecker_one {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) :
    CFC.sqrt (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
      (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
  rw [(Matrix.posSemidef_transpose_iff.2 hσ).sqrt_kronecker Matrix.PosSemidef.one,
    CFC.sqrt_one, hσ.sqrt_transpose]

open scoped Matrix.Norms.L2Operator in
/-- **Positive parts.** In the setting of `exists_norm_transferMap_pow_sub_le`, the positive
part `P_q = (B_q† B_q)^{1/2}` of the `q`-site blocked tensor satisfies
`‖P_q - P_∞‖ ≤ K e^{-γ q/ξ}`, with `P_∞ = (√σ)ᵀ ⊗ 1`.

arXiv:2103.13367, eq. `intermediate`: `‖Ã - B̃‖_∞ ≤ √‖Ã†Ã - B̃†B̃‖`. -/
theorem exists_norm_polarPos_blockTensor_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖Matrix.polarPos (physicalMatrix (blockTensor A q)) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨K, hK, h⟩ := exists_norm_gram_blockTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun q => ?_⟩
  have h1 := CFC.norm_sqrt_sub_sqrt_le
    (Matrix.posSemidef_conjTranspose_mul_self (physicalMatrix (blockTensor A q))).nonneg
    ((Matrix.posSemidef_transpose_iff.2 hσ.posSemidef).kronecker Matrix.PosSemidef.one).nonneg
  rw [sqrt_transpose_kronecker_one hσ.posSemidef] at h1
  refine h1.trans ?_
  have hx : 0 ≤ Real.exp (-γ / correlationLength lam₂) ^ q := by positivity
  calc Real.sqrt ‖(physicalMatrix (blockTensor A q))ᴴ * physicalMatrix (blockTensor A q) -
        σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖
      ≤ Real.sqrt (K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) :=
        Real.sqrt_le_sqrt (h q)
    _ = Real.sqrt K * Real.exp (-γ / correlationLength lam₂) ^ q := by
        rw [Real.sqrt_mul hK, ← pow_mul, mul_comm 2 q, pow_mul, Real.sqrt_sq hx]

/-! ### Mixed transfer matrices -/

/-- The mixed map is additive in its left family. -/
theorem _root_.Kraus.mixedMapLM_add_left {n : ℕ} (A A' B : MPSTensor n D) :
    Kraus.mixedMapLM (A + A') B = Kraus.mixedMapLM A B + Kraus.mixedMapLM A' B :=
  LinearMap.ext fun X => by
    simp [Matrix.add_mul, Finset.sum_add_distrib]

/-- Reading a `D² × D²` matrix `G` as the tensor with physical dimension `D²` whose `k`-th matrix
is the `k`-th row of `G`, as a linear map. -/
noncomputable def ofPhysicalMatrixLM :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ] MPSTensor (D * D) D where
  toFun G := ofPhysicalMatrix (G.submatrix (virtualPairEquiv D) id)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The mixed map against a fixed right family, as a linear map in the left family. -/
noncomputable def mixedMapLMLeft {n : ℕ} (B : MPSTensor n D) :
    MPSTensor n D →ₗ[ℂ] Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) where
  toFun A := Kraus.mixedMapLM A B
  map_add' A A' := Kraus.mixedMapLM_add_left A A' B
  map_smul' c A := Kraus.mixedMapLM_smul_left c A B

/-- The linear map `G ↦ τ_{G,B}` sending a `D² × D²` matrix `G`, read as a tensor through
`ofPhysicalMatrixLM`, to the transfer matrix of its mixed transfer map against `B`.

arXiv:2103.13367, the mixed transfer matrix `τ_{AB} = A† B` after eq. `eq:a_tensor`, read as a
function of `A`. -/
noncomputable def mixedTransferMatrixLeft (B : MPSTensor (D * D) D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  transferMatrixLM ∘ₗ mixedMapLMLeft B ∘ₗ ofPhysicalMatrixLM

/-- The mixed transfer matrix of `P_∞` against itself is idempotent: `E_{P_∞}` is the rank-one
projection `X ↦ Tr(X) σ` (arXiv:2103.13367: `τ_BB² = τ_BB`). -/
theorem isIdempotentElem_transferMatrix_fixedPointTensor {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    IsIdempotentElem (transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ)
      (fixedPointTensor σ))) := by
  rw [IsIdempotentElem, ← sq, ← transferMatrix_pow, Kraus.mixedMapLM_self, sq,
    Module.End.mul_eq_comp]
  exact congrArg transferMatrix (isTransferIdempotent_fixedPointTensor hσ htr)

/-- The fixed-point state is normalized: `⟨φ_M(P_∞)|φ_M(P_∞)⟩ = 1` for `M ≥ 1`
(arXiv:2103.13367: `⟨ψ_M|ψ_M⟩ = Tr τ_BB^M = 1`). -/
theorem mpvOverlap_fixedPointTensor_self {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (M : ℕ) [NeZero M] :
    mpvOverlap (fixedPointTensor σ) (fixedPointTensor σ) M = 1 := by
  simp only [mpvOverlap, mpv_fixedPointTensor]
  rw [← pairProductState_fixedPointPair_norm_sq (N := M) hσ htr]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _ fun τ => ?_
  rw [mul_comm]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **Overlap of the positive part with the fixed point.** Let `A` be normal in the gauge
`∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (arXiv:2307.01696, eq. (5)), let `λ₂`
bound the moduli of the eigenvalues of `E_A` other than `1`, with correlation length `ξ`, and let
`0 < γ < 1/2`. Then there is `C > 0` such that for all `q` and all `M ≥ 1`, with `N = qM` and
`y = (N/q) e^{-γ q/ξ} = M e^{-γ q/ξ}`,
`|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| ≤ C y e^{C y}`, where `P_q` is the positive part of the `q`-site
blocked tensor and `P_∞` the fixed-point tensor.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished` (the estimate (S29)), quoted as arXiv:2307.01696, eq. (S9). The source
concludes `O(ε_q)` from `ε_q + ε_q² e^{ε_q}(1 + O(ε_q/M))`, which is the present bound in the
regime where `ε_q` stays bounded. -/
theorem exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      |1 - ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖| ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  obtain ⟨K₁, hK₁, hpos⟩ := exists_norm_polarPos_blockTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  set Ψ := mixedTransferMatrixLeft (fixedPointTensor σ)
  obtain ⟨K₃, hK₃, hΨ⟩ := LinearMap.exists_norm_apply_le_mul Ψ
  obtain ⟨K₄, hK₄, htrace⟩ :=
    LinearMap.exists_norm_apply_le_mul (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  set Tinf := transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))
  set c := ‖(1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ + ‖Tinf‖
  have hc : 0 ≤ c := by positivity
  set K := c * (K₃ * K₁)
  have hK : 0 ≤ K := by positivity
  refine ⟨K₄ * c * K + K + 1, by positivity, fun q M _ => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  set T := transferMatrix
    (Kraus.mixedMapLM (polarPosTensor (blockTensor A q)) (fixedPointTensor σ))
  -- `T - Tinf = Ψ(P_q - P_∞)`.
  have hTΨ : T - Tinf = Ψ (Matrix.polarPos (physicalMatrix (blockTensor A q)) -
      (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    rw [map_sub]
    congr 1
    change Tinf = transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrix
      (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix (virtualPairEquiv D) id))
      (fixedPointTensor σ))
    rw [ofPhysicalMatrix_sqrt_transpose_kronecker_one]
  have hδ : ‖T - Tinf‖ ≤ K₃ * K₁ * x ^ q := by
    rw [hTΨ]
    refine (hΨ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hpos q) hK₃
  have htel := norm_pow_sub_pow_le_of_isIdempotentElem
    (isIdempotentElem_transferMatrix_fixedPointTensor hσ.posSemidef htr)
    (c := c) (le_add_of_nonneg_left (norm_nonneg _)) (le_add_of_nonneg_right (norm_nonneg _))
    hδ M
  -- The overlap is `Tr T^M`, and `1 = Tr Tinf^M`.
  have hover : mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M - 1 =
      Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (T ^ M - Tinf ^ M) := by
    rw [map_sub, Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply,
      trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap,
      trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap,
      mpvOverlap_fixedPointTensor_self hσ.posSemidef htr]
  have hy : 0 ≤ c * (K₃ * K₁ * x ^ q) := by positivity
  have hgeom := one_add_pow_sub_one_le_mul_exp hy M
  calc |1 - ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖|
      = |‖(1 : ℂ)‖ - ‖mpvOverlap (polarPosTensor (blockTensor A q))
          (fixedPointTensor σ) M‖| := by rw [norm_one]
    _ ≤ ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M - 1‖ := by
        rw [norm_sub_rev]; exact abs_norm_sub_norm_le _ _
    _ ≤ K₄ * ‖T ^ M - Tinf ^ M‖ := by rw [hover]; exact htrace _
    _ ≤ K₄ * (c * ((1 + c * (K₃ * K₁ * x ^ q)) ^ M - 1)) := by gcongr
    _ ≤ K₄ * (c * (M * (c * (K₃ * K₁ * x ^ q)) *
          Real.exp (M * (c * (K₃ * K₁ * x ^ q))))) := by gcongr
    _ = K₄ * c * K * u * Real.exp (K * u) := by
        simp only [u, K]; ring_nf
    _ ≤ (K₄ * c * K + K + 1) * u * Real.exp ((K₄ * c * K + K + 1) * u) := by
        have hKC : K ≤ K₄ * c * K + K + 1 := by nlinarith [mul_nonneg (mul_nonneg hK₄ hc) hK]
        have hKC' : K₄ * c * K ≤ K₄ * c * K + K + 1 := by linarith
        gcongr

/-! ### The normalization `c_N` -/

open scoped Matrix.Norms.L2Operator in
/-- The transfer matrix of `E_A^n` is `e^{-2γ n/ξ}`-close to that of `X ↦ Tr(X) σ`, in the
setting of `exists_norm_transferMap_pow_sub_le`. -/
theorem exists_norm_transferMatrix_pow_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖transferMatrix (Kraus.transferMap A) ^ n -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
        K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ n := by
  obtain ⟨C, hC, hgap⟩ := exists_norm_transferMap_pow_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₂, hK₂, hent⟩ :=
    Matrix.exists_norm_entry_le_mul_l2_opNorm (m := Fin D) (n := Fin D)
  set r := Real.exp (-γ / correlationLength lam₂) ^ 2
  refine ⟨∑ a : Fin D × Fin D, ∑ b : Fin D × Fin D,
    K₂ * C * ‖(Matrix.single b.2 b.1 1 : Matrix (Fin D) (Fin D) ℂ)‖ *
      ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖,
    by positivity, fun n => ?_⟩
  rw [← transferMatrix_pow]
  refine (Matrix.l2_opNorm_le_sum_norm_entry _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  set Y : Matrix (Fin D) (Fin D) ℂ := Matrix.single b.2 b.1 1
  have hab : (transferMatrix (Kraus.transferMap A ^ n) -
      transferMatrix (Kraus.transferMap (fixedPointTensor σ))) a b =
      ((Kraus.transferMap A ^ n) Y - Y.trace • σ) a.2 a.1 := by
    rw [Matrix.sub_apply, Matrix.sub_apply, ← transferMap_fixedPointTensor_apply hσ.posSemidef]
    rfl
  rw [hab]
  have hr : 0 ≤ r := by positivity
  calc ‖((Kraus.transferMap A ^ n) Y - Y.trace • σ) a.2 a.1‖ *
        ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖
      ≤ (K₂ * (C * r ^ n * ‖Y‖)) *
          ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ := by
        gcongr
        exact (hent _ _ _).trans (by gcongr; exact hgap n Y)
    _ = K₂ * C * ‖Y‖ *
          ‖(Matrix.single a b 1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ * r ^ n := by
        ring

/-- The squared norm of the periodic state is the self-overlap: `‖φ_N(A)‖² = ⟨φ_N|φ_N⟩`. -/
theorem ofReal_norm_mpvState_sq (A : MPSTensor d D) (N : ℕ) :
    ((‖mpvState A N‖ ^ 2 : ℝ) : ℂ) = mpvOverlap A A N := by
  rw [EuclideanSpace.norm_sq_eq, mpvOverlap]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mpvState_apply, ← Complex.mul_conj']
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **Normalization.** In the setting of `exists_norm_transferMap_pow_sub_le`, the squared norm
`c_N² = Tr E_A^N` of the periodic state satisfies `|c_N² - 1| ≤ K e^{-2γ N/ξ}`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): `c_N = √(Tr E_A^N)` and
`|c_N - 1| = O(e^{-N/ξ})`. -/
theorem exists_abs_norm_mpvState_sq_sub_one_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      |‖mpvState A N‖ ^ 2 - 1| ≤ K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ N := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  obtain ⟨K₀, hK₀, hT⟩ := exists_norm_transferMatrix_pow_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₄, hK₄, htrace⟩ :=
    LinearMap.exists_norm_apply_le_mul (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  refine ⟨K₄ * K₀, by positivity, fun N => ?_⟩
  have hone : Matrix.trace (transferMatrix (Kraus.transferMap (fixedPointTensor σ))) = 1 := by
    have h := trace_transferMatrix_transferMap_pow_eq_mpvOverlap (fixedPointTensor σ) 1
    rwa [pow_one, mpvOverlap_fixedPointTensor_self hσ.posSemidef htr] at h
  have hc : (((‖mpvState A N‖ ^ 2 - 1 : ℝ)) : ℂ) =
      Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (transferMatrix (Kraus.transferMap A) ^ N -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))) := by
    rw [map_sub, Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply, hone,
      trace_transferMatrix_transferMap_pow_eq_mpvOverlap, ← ofReal_norm_mpvState_sq]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hc, mul_assoc]
  exact (htrace _).trans (mul_le_mul_of_nonneg_left (hT N) hK₄)

/-- The periodic states of a normal tensor in the gauge of `exists_norm_transferMap_pow_sub_le`
have bounded norms: `c_N² = Tr E_A^N ≤ B` for all `N`. -/
theorem exists_norm_mpvState_sq_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) :
    ∃ B : ℝ, ∀ N : ℕ, ‖mpvState A N‖ ^ 2 ≤ B := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have hCh := Kraus.isChannel_mapLM A hA
  obtain ⟨δ, hδ, hgap⟩ := uniform_eigenvalue_gap_of_finite_lt_one
    (Module.End.finite_hasEigenvalue (Kraus.transferMap A)) fun μ hμ hne =>
      lt_of_le_of_ne (hCh.eigenvalue_norm_le_one μ hμ)
        fun h => hne (hNT.primitive_transfer.unique_peripheral μ hμ h)
  set t := max (1 - δ) (1 / 2)
  have ht0 : 0 < t := lt_max_of_lt_right (by norm_num)
  have ht1 : t ≤ 1 := max_le (by linarith) (by norm_num)
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨K, hK, hc⟩ := exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => by rw [hnorm]; exact (hgap μ hμ hne).trans (le_max_left _ _))
    (γ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨1 + K, fun N => ?_⟩
  have hx : Real.exp (-(1 / 4) / correlationLength (t : ℂ)) ≤ 1 := by
    rw [neg_div_correlationLength, hnorm, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Real.log_nonpos ht0.le ht1)
  have hpow : (Real.exp (-(1 / 4) / correlationLength (t : ℂ)) ^ 2) ^ N ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ (by positivity) hx)
  have := (abs_le.1 ((hc N).trans (mul_le_of_le_one_right hK hpow))).2
  linarith

/-- The overlap of two periodic states is bounded by the product of their norms. -/
theorem norm_mpvOverlap_le {n D₁ D₂ : ℕ} (X : MPSTensor n D₁) (Y : MPSTensor n D₂) (M : ℕ) :
    ‖mpvOverlap X Y M‖ ≤ ‖mpvState X M‖ * ‖mpvState Y M‖ := by
  rw [mpvOverlap_eq_star_mpvInner, norm_star, mpvInner]
  exact norm_inner_le_norm _ _

/-- The positive part of the `q`-site blocked tensor generates, on `M` blocks, a state of the
same norm as the periodic state of `A` on `qM` sites: both squared norms are `Tr E_A^{qM}`
(arXiv:2307.01696, text after eq. (6): `E_P = E_B = E_A^q`). -/
theorem norm_mpvState_polarPosTensor_blockTensor [NeZero D] (A : MPSTensor d D) (q M : ℕ) :
    ‖mpvState (polarPosTensor (blockTensor A q)) M‖ = ‖mpvState A (q * M)‖ := by
  have h : ((‖mpvState (polarPosTensor (blockTensor A q)) M‖ ^ 2 : ℝ) : ℂ) =
      ((‖mpvState A (q * M)‖ ^ 2 : ℝ) : ℂ) := by
    rw [ofReal_norm_mpvState_sq, ofReal_norm_mpvState_sq,
      ← trace_transferMatrix_transferMap_pow_eq_mpvOverlap,
      ← trace_transferMatrix_transferMap_pow_eq_mpvOverlap,
      transferMap_polarPosTensor_blockTensor, transferMatrix_pow, ← pow_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (Complex.ofReal_injective h)

/-- **Overlap of the positive part with the fixed point**, `O`-form (arXiv:2103.13367,
Supplemental Material, eq. (S29), quoted as arXiv:2307.01696, eq. (S9)): in the setting of
`exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le`, there is `C` with
`|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| ≤ C (N/q) e^{-γ q/ξ}` for all `q` and all `M ≥ 1`, `N = qM`.

For `(N/q) e^{-γ q/ξ} ≤ 1` this is the explicit bound; otherwise both overlaps are bounded,
since `‖φ_M(P_q)‖ = ‖φ_N(A)‖` and the norms `‖φ_N(A)‖` are bounded. -/
theorem exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le_mul (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      |1 - ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖| ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  obtain ⟨C, hC, h⟩ :=
    exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨B, hB⟩ := exists_norm_mpvState_sq_le A hN hA hσ htr hfix
  have hB0 : 0 ≤ B := (sq_nonneg _).trans (hB 0)
  refine ⟨C * Real.exp C + (2 + B), by positivity, fun q M _ => ?_⟩
  set y := (M : ℝ) * Real.exp (-γ * q / correlationLength lam₂)
  have hy0 : 0 ≤ y := by positivity
  rcases le_or_gt y 1 with hy | hy
  · have hexp : Real.exp (C * y) ≤ Real.exp C := Real.exp_le_exp.2 (by nlinarith)
    calc _ ≤ C * y * Real.exp (C * y) := h q M
      _ ≤ C * y * Real.exp C := by gcongr
      _ ≤ (C * Real.exp C + (2 + B)) * y := by nlinarith [Real.exp_pos C]
  · have hz : ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖ ≤ 1 + B := by
      have hfp : ‖mpvState (fixedPointTensor σ) M‖ = 1 := by
        have h1 := ofReal_norm_mpvState_sq (fixedPointTensor σ) M
        rw [mpvOverlap_fixedPointTensor_self hσ.posSemidef htr] at h1
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
          (Complex.ofReal_injective (by rw [h1]; simp))
      refine (norm_mpvOverlap_le _ _ M).trans ?_
      rw [hfp, mul_one, norm_mpvState_polarPosTensor_blockTensor]
      nlinarith [hB (q * M), norm_nonneg (mpvState A (q * M))]
    calc _ ≤ 1 + ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖ := by
          rw [abs_le]; constructor <;> linarith [norm_nonneg
            (mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M)]
      _ ≤ 2 + B := by linarith
      _ ≤ (2 + B) * y := le_mul_of_one_le_right (by linarith) hy.le
      _ ≤ (C * Real.exp C + (2 + B)) * y := by
          have : 0 ≤ C * Real.exp C * y := by positivity
          nlinarith

/-! ### The approximation error -/

/-- The normalized periodic state `|φ_N⟩ = c_N⁻¹ |φ_N(A)⟩` with `c_N = ‖φ_N(A)‖`
(arXiv:2307.01696, Supplemental Material, eq. `eq:TI-MPS2`); it is `0` when `c_N = 0`. -/
noncomputable def normalizedMPVState (A : MPSTensor d D) (N : ℕ) : MPVSpace d N :=
  ((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N

/-- The periodic state of `B' = V P_∞` on `M` blocks of `q` sites, read on the `Mq` sites
through the regrouping of sites into blocks (arXiv:2307.01696, eqs. (9) and (10)). -/
noncomputable def approximatingMPVStateRaw (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ)
    (q M : ℕ) : MPVSpace d (M * q) :=
  (EuclideanSpace.equiv (ι := Cfg d (M * q)) (𝕜 := ℂ)).symm fun s =>
    mpv (approximatingTensor (blockTensor A q) σ) ((blockedConfigEquiv d M q).symm s)

/-- The **approximating state** `|φ̃_N⟩ = |φ_M(V P_∞)⟩ / ‖φ_M(V P_∞)‖` on `N = Mq` sites
(arXiv:2307.01696, eqs. (9) and (10)). -/
noncomputable def approximatingMPVState (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ)
    (q M : ℕ) : MPVSpace d (M * q) :=
  ((‖approximatingMPVStateRaw A σ q M‖ : ℂ)⁻¹) • approximatingMPVStateRaw A σ q M

@[simp] lemma approximatingMPVStateRaw_apply (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ) (q M : ℕ) (s : Cfg d (M * q)) :
    approximatingMPVStateRaw A σ q M s =
      mpv (approximatingTensor (blockTensor A q) σ) ((blockedConfigEquiv d M q).symm s) := by
  simp [approximatingMPVStateRaw, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- A vector divided by its norm has norm at most `1`. -/
theorem norm_inv_norm_smul_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : E) :
    ‖((‖v‖ : ℂ)⁻¹) • v‖ ≤ 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)

/-- For `B_q` injective, the approximating state is the periodic state of `V P_∞` itself
(its norm is `1`), and its overlap with the periodic state of `A` is the overlap of the
positive part with the fixed point: `⟨φ̃_N|φ_N(A)⟩ = ⟨φ_M(P_∞)|φ_M(P_q)⟩`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): `c_N ⟨φ̃_N|φ_N⟩ = ⟨Ω|v_pos⟩`. -/
theorem inner_approximatingMPVState_mpvState (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (M : ℕ) [NeZero M] :
    approximatingMPVState A σ q M = approximatingMPVStateRaw A σ q M ∧
      ⟪approximatingMPVState A σ q M, mpvState A (M * q)⟫_ℂ =
        mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M := by
  have hinner : ∀ w : MPVSpace d (M * q),
      ⟪approximatingMPVStateRaw A σ q M, w⟫_ℂ =
        ∑ τ : Fin M → Fin (blockPhysDim d q),
          star (mpv (approximatingTensor (blockTensor A q) σ) τ) *
            w (blockedConfigEquiv d M q τ) := fun w => by
    rw [PiLp.inner_apply, ← (blockedConfigEquiv d M q).sum_comp]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [RCLike.inner_apply, approximatingMPVStateRaw_apply, Equiv.symm_apply_apply, mul_comm]
    rfl
  have hnorm : ‖approximatingMPVStateRaw A σ q M‖ = 1 := by
    have h := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (approximatingMPVStateRaw A σ q M)).symm
    simp only [hinner, approximatingMPVStateRaw_apply, Equiv.symm_apply_apply,
      mpv_approximatingTensor_norm_sq hB hσ htr] at h
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
      (Complex.ofReal_injective ?_)
    push_cast
    exact h
  have heq : approximatingMPVState A σ q M = approximatingMPVStateRaw A σ q M := by
    rw [approximatingMPVState, hnorm]; simp
  refine ⟨heq, ?_⟩
  rw [heq, hinner]
  simp only [mpvState_apply, mpv_blockedConfigEquiv_eq_sum_polar, mpv_approximatingTensor]
  rw [(isIsometry_polarIsoMatrix_of_isInjective hB).sum_star_mul_tensorPower]
  simp only [mpvOverlap, mpv_fixedPointTensor]
  exact Finset.sum_congr rfl fun τ _ => mul_comm _ _

/-- **Approximation error, normal case** (arXiv:2307.01696, Lemma 1 and Lemma 1'(i)). Let `A`
be normal in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (eq. (5)), let
`λ₂` bound the moduli of the eigenvalues of `E_A` other than `1`, with correlation length
`ξ = -1/log|λ₂|`, and let `0 < γ < 1/2`. There is `C > 0` such that for every block length `q`
and every number of blocks `M ≥ 1`, with `N = Mq` and `y = (N/q) e^{-γ q/ξ} = M e^{-γ q/ξ}`,
the error `ε = 1 - |⟨φ̃_N|φ_N⟩|` of the approximating state satisfies `ε ≤ C y e^{C y}`.

In particular `ε = O((N/q) e^{-γ q/ξ})` whenever `(N/q) e^{-γ q/ξ}` stays bounded (eq. (17)
and eq. (S11)); see `exists_approximationError_le_mul` for the unconditional `O`-form.

The proof is the triangle inequality of the source,
`ε ≤ |1 - c_N |⟨φ̃_N|φ_N⟩|| + |c_N - 1| |⟨φ̃_N|φ_N⟩|`, with the first term bounded by
`exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le` (eq. (S9)) and the second by
`exists_abs_norm_mpvState_sq_sub_one_le`. The source drops the second term using `q = o(N)`;
here it is bounded by `e^{-2γN/ξ} ≤ e^{-γ q/ξ}` since `N ≥ q`, so no condition relating `q`
and `N` is needed. For the finitely many `q` below the injectivity length of `A` the bound
holds because `ε ≤ 1`. -/
theorem exists_approximationError_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C₁, hC₁, hover⟩ :=
    exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₅, hK₅, hc⟩ :=
    exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨L, hLpos, hL⟩ := hN
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx : 0 < x := Real.exp_pos _
  set C := C₁ + K₅ + (x ^ L)⁻¹ + 1
  have hC₁C : C₁ ≤ C := by have : 0 < (x ^ L)⁻¹ := by positivity
                           linarith
  refine ⟨C, by positivity, fun q M _ => ?_⟩
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hu : 0 ≤ u := by positivity
  have hexp : 1 ≤ Real.exp (C * u) := Real.one_le_exp (by positivity)
  set φt := approximatingMPVState A σ q M
  set φ := normalizedMPVState A (M * q)
  have hε1 : 1 - ‖⟪φt, φ⟫_ℂ‖ ≤ 1 := by linarith [norm_nonneg ⟪φt, φ⟫_ℂ]
  -- When `C u ≥ 1` the bound is trivial.
  have htriv : 1 ≤ C * u → 1 - ‖⟪φt, φ⟫_ℂ‖ ≤ C * u * Real.exp (C * u) := fun h =>
    hε1.trans (h.trans (le_mul_of_one_le_right (by positivity) hexp))
  by_cases hbig : 1 ≤ C * u
  · exact htriv hbig
  rw [not_le] at hbig
  have hx1 : x < 1 := by
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ u := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ h)
    have : 1 ≤ C := by have : 0 < (x ^ L)⁻¹ := by positivity
                       linarith
    nlinarith
  have hLq : L ≤ q := by
    by_contra h
    rw [not_le] at h
    have hxLq : x ^ L ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le h.le
    have : x ^ L ≤ u := hxLq.trans (le_mul_of_one_le_left (by positivity) hM)
    have : 1 ≤ (x ^ L)⁻¹ * u := by
      rw [← inv_mul_cancel₀ (by positivity : x ^ L ≠ 0)]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have : (x ^ L)⁻¹ * u ≤ C * u := by
      refine mul_le_mul_of_nonneg_right ?_ hu
      linarith
    linarith
  have hB : Kraus.IsInjective (blockTensor A q) :=
    (isNBlkInjective_iff_blockTensor_isInjective A q).1 (isNBlkInjective_of_le hLpos hL hLq)
  obtain ⟨-, hz⟩ := inner_approximatingMPVState_mpvState A hB hσ.posSemidef htr M
  set z := mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M
  set c := ‖mpvState A (M * q)‖
  -- The normalization term: `|c² - 1| ≤ K₅ e^{-2γN/ξ} ≤ K₅ u`.
  have hcu : |c ^ 2 - 1| ≤ K₅ * u := by
    refine (hc (M * q)).trans (mul_le_mul_of_nonneg_left ?_ hK₅)
    calc (x ^ 2) ^ (M * q) = x ^ (2 * (M * q)) := (pow_mul _ _ _).symm
      _ ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le (by
          have := Nat.one_le_iff_ne_zero.2 (NeZero.ne M); nlinarith)
      _ ≤ u := le_mul_of_one_le_left (by positivity) hM
  have hinner : ⟪φt, φ⟫_ℂ = (c : ℂ)⁻¹ * z := by
    rw [show φ = ((c : ℂ)⁻¹) • mpvState A (M * q) from rfl, inner_smul_right, hz]
  have hC' : C₁ * u * Real.exp (C₁ * u) + K₅ * u ≤ C * u * Real.exp (C * u) := by
    have h1 : C₁ * u * Real.exp (C₁ * u) ≤ C₁ * u * Real.exp (C * u) := by
      gcongr
    have h2 : K₅ * u ≤ K₅ * u * Real.exp (C * u) :=
      le_mul_of_one_le_right (by positivity) hexp
    have h3 : (C₁ + K₅) * u * Real.exp (C * u) ≤ C * u * Real.exp (C * u) := by
      gcongr
      have : 0 < (x ^ L)⁻¹ := by positivity
      linarith
    nlinarith
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- `c = 0`: then `|c² - 1| = 1 ≤ K₅ u`.
    have : 1 ≤ K₅ * u := by simpa [hc0] using hcu
    refine hε1.trans (this.trans ?_)
    nlinarith [Real.exp_pos (C₁ * u), mul_nonneg (mul_nonneg hC₁.le hu) (Real.exp_pos (C₁ * u)).le]
  · have hcpos : 0 < c := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc0)
    set w := ‖⟪φt, φ⟫_ℂ‖
    have hw1 : w ≤ 1 := by
      refine (norm_inner_le_norm (𝕜 := ℂ) φt φ).trans ?_
      calc ‖φt‖ * ‖φ‖ ≤ 1 * 1 := mul_le_mul (norm_inv_norm_smul_le_one _)
            (norm_inv_norm_smul_le_one _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hcw : c * w = ‖z‖ := by
      have hw : w = ‖(c : ℂ)⁻¹ * z‖ := by simp only [w, hinner]
      rw [hw, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hcpos, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hc1 : |c - 1| ≤ |c ^ 2 - 1| := by
      rw [show c ^ 2 - 1 = (c - 1) * (c + 1) by ring, abs_mul]
      exact le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_pos (by linarith)]; linarith)
    have hover' := hover q M
    rw [hxq] at hover'
    have : 1 - w ≤ |1 - ‖z‖| + |c - 1| := by
      have e : 1 - w = (1 - ‖z‖) + (c - 1) * w := by rw [← hcw]; ring
      rw [e]
      have : (c - 1) * w ≤ |c - 1| := by
        calc (c - 1) * w ≤ |c - 1| * w := mul_le_mul_of_nonneg_right (le_abs_self _)
              (norm_nonneg _)
          _ ≤ |c - 1| * 1 := mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)
          _ = |c - 1| := mul_one _
      linarith [le_abs_self (1 - ‖z‖)]
    linarith

/-- **Approximation error, normal case, `O`-form** (arXiv:2307.01696, Lemma 1, eq. (17), and
Lemma 1'(i), eq. (S11)): in the setting of `exists_approximationError_le`, there is `C` with
`ε(φ̃_N, φ_N) ≤ C (N/q) e^{-γ q/ξ}` for every block length `q` and every number of blocks
`M ≥ 1`, `N = Mq`.

For `(N/q) e^{-γ q/ξ} ≤ 1` this is the explicit bound; otherwise it holds because `ε ≤ 1`. -/
theorem exists_approximationError_le_mul (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ => ?_⟩
  set y := (M : ℝ) * Real.exp (-γ * q / correlationLength lam₂)
  have hy0 : 0 ≤ y := by positivity
  rcases le_or_gt y 1 with hy | hy
  · have hexp : Real.exp (C * y) ≤ Real.exp C := Real.exp_le_exp.2 (by nlinarith)
    calc _ ≤ C * y * Real.exp (C * y) := h q M
      _ ≤ C * y * Real.exp C := by gcongr
      _ ≤ (C * Real.exp C + 1) * y := by nlinarith [Real.exp_pos C]
  · have : 0 ≤ ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ :=
      norm_nonneg _
    nlinarith [Real.exp_pos C, mul_pos hC (Real.exp_pos C)]

end MPSTensor
