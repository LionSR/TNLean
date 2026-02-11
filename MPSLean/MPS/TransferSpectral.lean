/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.CPPrimitive

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Mixed transfer operator

The mixed (or cross) transfer operator for two MPS tensors `A` and `B`:
$$F_{AB}(X) = \sum_i A^i \, X \, (B^i)^\dagger$$

When `A = B`, this reduces to the standard transfer map `E_A`.
The mixed transfer operator encodes all cross-correlations between two
MPS tensors and is the key tool for proving block separation in the
multi-block fundamental theorem.
-/

section MixedTransfer

/-- The **mixed transfer operator** for MPS tensors `A` and `B`:
$$F_{AB}(X) = \sum_i A^i \, X \, (B^i)^\dagger.$$
This is a linear map on `D × D` complex matrices. When `A = B`, it
recovers the standard transfer map `transferMap A`. -/
noncomputable def mixedTransferMap (A B : MPSTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d,
    (LinearMap.mulLeft ℂ (A i)).comp (LinearMap.mulRight ℂ (B i)ᴴ)

/-- Explicit formula for the mixed transfer operator. -/
@[simp]
lemma mixedTransferMap_apply (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    mixedTransferMap A B X = ∑ i : Fin d, A i * X * (B i)ᴴ := by
  classical
  simp [mixedTransferMap, Matrix.mul_assoc]

/-- The mixed transfer operator with `A = B` is the standard transfer map. -/
theorem mixedTransferMap_self (A : MPSTensor d D) :
    mixedTransferMap A A = transferMap (d := d) (D := D) A := by
  ext X
  simp [mixedTransferMap_apply, transferMap_apply]

/-- Linearity of the mixed transfer operator in the first argument: if we
scale the first tensor, the map scales linearly. -/
lemma mixedTransferMap_smul_left (c : ℂ) (A B : MPSTensor d D) :
    mixedTransferMap (fun i => c • A i) B = c • mixedTransferMap A B := by
  ext X
  simp only [mixedTransferMap_apply, LinearMap.smul_apply, Matrix.smul_mul]
  rw [← Finset.smul_sum]

/-- Linearity of the mixed transfer operator in the second argument (with conjugation):
scaling B by c conjugates the scalar. -/
lemma mixedTransferMap_smul_right (c : ℂ) (A B : MPSTensor d D) :
    mixedTransferMap A (fun i => c • B i) = starRingEnd ℂ c • mixedTransferMap A B := by
  ext X : 1
  simp only [mixedTransferMap_apply, Matrix.conjTranspose_smul, LinearMap.smul_apply]
  -- Goal: ∑ i, A i * X * (star c • (B i)ᴴ) = starRingEnd ℂ c • ∑ i, A i * X * (B i)ᴴ
  -- Note: star c and (starRingEnd ℂ) c are definitionally equal for ℂ
  simp only [starRingEnd_apply]
  rw [Finset.smul_sum]; congr 1; ext i
  rw [Matrix.mul_smul]

end MixedTransfer

/-! ## Iterated mixed transfer and MPV cross-correlations

The key bridge: iterating the mixed transfer operator `N` times connects
to sums over all words of length `N` of products of word evaluations.
This is the operator-level encoding of the inner product structure
of the MPV spaces.
-/

section IteratedTransfer

/-- Iterating the mixed transfer operator `N` times gives:
$$F_{AB}^N(X) = \sum_{\sigma : \mathrm{Fin}\,N \to \mathrm{Fin}\,d}
  \mathrm{evalWord}(A, \sigma) \cdot X \cdot \mathrm{evalWord}(B, \sigma)^\dagger$$

This connects the spectral theory of the transfer operator to the
combinatorial structure of word evaluations, and hence to MPV coefficients.

**Proof sketch:** By induction on `N`.
- Base case: `F^0(X) = X` and the sum over `Fin 0 → Fin d` has one term
  (the empty word), with `evalWord A [] = 1`.
- Inductive step: Expanding `F^{N+1}(X) = F(F^N(X))`, substitute the
  inductive hypothesis and use that `evalWord A (i :: σ_list)` factors as
  `A i * evalWord A σ_list`. -/
private lemma sum_fin_succ_eq {n d : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (n + 1) → Fin d) → M) :
    ∑ σ : Fin (n + 1) → Fin d, f σ =
    ∑ i : Fin d, ∑ τ : Fin n → Fin d, f (Fin.cons i τ) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin d)).symm _ _
    (fun σ => by simp [Fin.consEquiv, Fin.cons_self_tail])

theorem mixedTransferMap_pow_apply (A B : MPSTensor d D) (N : ℕ) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ((mixedTransferMap A B) ^ N) X =
        ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ := by
  induction N with
  | zero =>
    intro X
    simp [evalWord, Finset.univ_unique]
  | succ n ih =>
    intro X
    -- F^{n+1}(X) = F(F^n(X))
    rw [pow_succ']
    change mixedTransferMap A B (((mixedTransferMap A B) ^ n) X) = _
    rw [ih]
    -- Distribute F over the sum, then swap summation order
    simp only [mixedTransferMap_apply, map_sum]
    rw [Finset.sum_comm]
    -- Re-index the RHS using Fin.cons decomposition
    rw [sum_fin_succ_eq]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro τ _
    simp only [List.ofFn_cons, evalWord, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Specialization to the diagonal case**: iterating the standard
transfer map gives the sum over word evaluations. This improves on
`transferMap_pow_eq_blocked` by providing it as a corollary. -/
theorem transferMap_pow_apply' (A : MPSTensor d D) (N : ℕ) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ((transferMap (d := d) (D := D) A) ^ N) X =
        ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) * X * (evalWord A (List.ofFn σ))ᴴ := by
  rw [← mixedTransferMap_self]
  exact mixedTransferMap_pow_apply A A N

/-- **Trace of iterated mixed transfer encodes MPV cross-correlations.**

For `X = 1`:
$$\mathrm{tr}(F_{AB}^N(1)) = \sum_\sigma \mathrm{tr}(\mathrm{evalWord}(A,\sigma)
  \cdot \mathrm{evalWord}(B,\sigma)^\dagger)$$

This is the key quantity for detecting whether two MPS tensors produce the
same (or different) physical states. -/
theorem trace_mixedTransferMap_pow_identity (A B : MPSTensor d D) (N : ℕ) :
    Matrix.trace (((mixedTransferMap A B) ^ N) (1 : Matrix (Fin D) (Fin D) ℂ)) =
      ∑ σ : Fin N → Fin d,
        Matrix.trace (evalWord A (List.ofFn σ) * (evalWord B (List.ofFn σ))ᴴ) := by
  rw [mixedTransferMap_pow_apply]
  simp

/-- **MPV inner product via trace**: when `D = 1` (or more generally when
the trace factors), the cross-correlation simplifies to the inner product
of MPV coefficients. For general `D`, the trace of the word product
doesn't factor, but the formula still captures the relevant overlap. -/
theorem mpv_inner_product_via_trace (A B : MPSTensor d D) (N : ℕ)
    (σ : Fin N → Fin d) :
    Matrix.trace (evalWord A (List.ofFn σ) * (evalWord B (List.ofFn σ))ᴴ) =
      ∑ j : Fin D, ∑ k : Fin D,
        (evalWord A (List.ofFn σ) j k) * starRingEnd ℂ (evalWord B (List.ofFn σ) j k) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]

end IteratedTransfer

/-! ## Spectral radius and convergence

The key analytic ingredient: if a linear operator on a finite-dimensional
space has spectral radius strictly less than 1, then its iterates converge
to zero. This is the mechanism by which the mixed transfer operator
`F_{AB}` for distinct blocks `A ≠ B` decays, enabling block separation.

### Approach

We work with `Matrix (Fin D) (Fin D) ℂ` equipped with the L∞-operator norm,
which makes it a complex Banach algebra. Then:

1. Mathlib provides the Gelfand formula:
   `‖a^n‖^{1/n} → spectralRadius ℂ a`
   (`pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`)

2. Mathlib provides:
   `‖x‖ < 1 → x^n → 0`
   (`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`)

3. Combining these: if `spectralRadius ℂ a < 1`, then for sufficiently
   large `n`, `‖a^n‖^{1/n} < 1`, hence `‖a^n‖ < 1`, and more precisely
   we get `a^n → 0`.

For our application, `a` is the mixed transfer operator `F_{AB}` viewed
as an element of the algebra `End(M_D(ℂ))`.
-/

section SpectralConvergence

/-! ### Normed algebra structure on matrices

We use the L∞-operator norm on matrices, which Mathlib provides as
`Matrix.linftyOpNormedRing` and `Matrix.linftyOpNormedAlgebra`.
These are not global instances, so we introduce them locally. -/

/-- Local instance: `Matrix (Fin D) (Fin D) ℂ` is a normed ring
under the L∞-operator norm. -/
noncomputable scoped instance : NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing

/-- Local instance: `Matrix (Fin D) (Fin D) ℂ` is a normed algebra over `ℂ`
under the L∞-operator norm. -/
noncomputable scoped instance : NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

/-! ### Transfer matrix (vectorized transfer operator)

The transfer matrix is the Kronecker-product representation of the
mixed transfer map, acting on vectorized matrices. -/

/-- The **transfer matrix** (vectorized transfer operator): the
`(D×D) × (D×D)` matrix representing the mixed transfer operator
under the vectorization isomorphism `M_D(ℂ) ≅ ℂ^{D²}`.

`T_AB = ∑_k A^k ⊗ conj(B^k)` where `⊗` is the Kronecker product. -/
noncomputable def transferMatrix (A B : MPSTensor d D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ k : Fin d, Matrix.kroneckerMap (· * ·) (A k) (star (B k))

/-- The transfer matrix for `A = B` is the standard self-transfer matrix. -/
theorem transferMatrix_self (A : MPSTensor d D) :
    transferMatrix A A = ∑ k : Fin d, Matrix.kroneckerMap (· * ·) (A k) (star (A k)) := by
  rfl

/-! ### Spectral radius of the mixed transfer operator -/

/-- The **spectral radius** of the mixed transfer operator,
defined as the spectral radius of the linear map `F_{AB}` viewed in
the normed algebra of continuous linear endomorphisms.

Mathematically this equals the spectral radius of the vectorized
transfer matrix; the connection is given by
`mixedTransferSpectralRadius_eq_transferMatrix_spectralRadius`. -/
noncomputable def mixedTransferSpectralRadius (A B : MPSTensor d D) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B))

/-- The spectral radius of the mixed transfer operator (as a linear map) equals
the spectral radius of the vectorized transfer matrix (Kronecker form).

This follows from the fact that vectorization gives an algebra isomorphism
between `Module.End ℂ (M_D(ℂ))` and `M_{D²}(ℂ)`. -/
theorem mixedTransferSpectralRadius_eq_transferMatrix
    (A B : MPSTensor d D) :
    mixedTransferSpectralRadius A B =
      (⨆ k ∈ spectrum ℂ (transferMatrix A B), (‖k‖₊ : ENNReal)) := by
  sorry

/-! ### Key spectral gap property

The crucial fact for block separation: when `A` and `B` come from
**different** irreducible blocks, the mixed transfer operator `F_{AB}`
has spectral radius strictly less than 1 (assuming both blocks are
individually normalized so their self-transfer maps have spectral
radius 1).

This is the content of the quantum Perron–Frobenius theorem applied
to the cross-channel. -/

/-- **Spectral gap for distinct blocks**: If `A` and `B` are injective
MPS tensors that are *not* gauge-phase equivalent, then the mixed
transfer operator `F_{AB}` has spectral radius strictly less than 1.

This is the quantum analogue of: for a primitive non-negative matrix,
off-diagonal blocks in the transfer matrix have spectral radius < 1.

**Mathematical proof sketch:** The transfer map `E_A` has a unique
fixed point `ρ_A` (by quantum PF). The adjoint `E_A†` has a unique
fixed point `σ_A`. The full channel decomposes as
`E_A^n(X) → tr(σ_A X) ρ_A` exponentially. For the mixed channel
`F_{AB}`, if A and B are not gauge-phase equivalent, there is no
rank-1 fixed point, so all eigenvalues have modulus < 1. -/
theorem spectralRadius_mixedTransfer_lt_one
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 := by
  -- This requires the full quantum Perron–Frobenius theory:
  -- 1. Both E_A and E_B are primitive CP maps (from injectivity)
  -- 2. F_{AB} has no eigenvalue of modulus 1 (from non-equivalence)
  -- 3. Therefore spectralRadius(F_{AB}) < 1
  -- Each step is beyond current Mathlib capabilities.
  sorry

/-! ### Power convergence from spectral radius bound

The following theorem gives the fundamental convergence result:
if the spectral radius of an element in a Banach algebra is < 1,
then its powers converge to zero.

This can be derived from the Gelfand formula (available in Mathlib)
combined with the norm convergence criterion. -/

/-- **Powers tend to zero when spectral radius < 1.** In a complex
Banach algebra, if `spectralRadius ℂ a < 1`, then `a ^ n → 0`.

This follows from the Gelfand formula: `‖a^n‖^{1/n} → ρ(a)`, so
for large `n`, `‖a^n‖^{1/n} < r` for some `r < 1`, giving
`‖a^n‖ < r^n → 0`.

**Mathlib ingredients:**
- `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand formula
- `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`: ‖x‖ < 1 ⟹ x^n → 0
- The connection requires showing that `spectralRadius < 1` implies
  `‖a^N‖ < 1` for some `N`, and then `(a^N)^n → 0` implies `a^n → 0`.

The full formal proof requires careful handling of the `ℝ≥0∞`-valued
spectral radius and the passage from the limit to a uniform bound. -/
theorem pow_tendsto_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (h : spectralRadius ℂ a < 1) :
    Filter.Tendsto (fun n => a ^ n) Filter.atTop (nhds 0) := by
  -- Step 1: Find r : NNReal with spectralRadius ℂ a < r < 1
  rw [ENNReal.lt_iff_exists_nnreal_btwn] at h
  obtain ⟨r, hr_above, hr_below⟩ := h
  -- hr_above : spectralRadius ℂ a < ↑r
  -- hr_below : ↑r < 1 (in ℝ≥0∞)
  have hr_lt_one : r < 1 := ENNReal.coe_lt_coe.mp (by rwa [ENNReal.coe_one])
  -- Step 2: From Gelfand's formula, eventually ‖a^n‖₊^(1/n) < r in ℝ≥0∞
  have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
  have hev := gelfand.eventually (eventually_lt_nhds hr_above)
  -- hev : ∀ᶠ n in atTop, (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / ↑n) < ↑r
  -- Step 3: Eventually ‖a^n‖₊ < r^n
  have hev2 : ∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < r ^ n := by
    filter_upwards [hev, Filter.eventually_gt_atTop 0] with n hn hn_pos
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff hn_pos_real] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  -- Step 4: ‖a^n‖ ≤ (r : ℝ)^n eventually, and (r:ℝ)^n → 0
  apply squeeze_zero_norm' (a := fun n => (r : ℝ) ^ n)
  · filter_upwards [hev2] with n hn
    rw [← coe_nnnorm, ← NNReal.coe_pow]
    exact_mod_cast hn.le
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg (by exact_mod_cast hr_lt_one)

/-! ### Application to mixed transfer convergence -/

/-- **Mixed transfer iterates decay for distinct blocks.**

If `A` and `B` are injective MPS tensors from different gauge
equivalence classes, then for any matrix `X`, the iterates
`F_{AB}^n(X)` converge to zero as `n → ∞`.

This is the engine of block separation: cross-terms between distinct
blocks vanish in the large-`N` limit. -/
theorem mixedTransfer_pow_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  -- Step 1: Convert to continuous linear map via algebra equivalence.
  -- Module.End.toContinuousLinearMap : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V)
  -- gives a NormedRing/NormedAlgebra structure needed for spectral theory.
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) :=
    Module.End.toContinuousLinearMap V
  let F := mixedTransferMap A B
  let F' : V →L[ℂ] V := Φ F
  -- Step 2: spectralRadius ℂ F' < 1.
  -- By AlgEquiv.spectrum_eq, spectrum ℂ F' = spectrum ℂ F.
  -- By vectorization, spectrum ℂ F = spectrum ℂ (transferMatrix A B).
  -- Thus spectralRadius ℂ F' = mixedTransferSpectralRadius A B < 1.
  have h_sr : spectralRadius ℂ F' < 1 := by
    -- `mixedTransferSpectralRadius A B` is *defined* as `spectralRadius ℂ F'`,
    -- so this is exactly `spectralRadius_mixedTransfer_lt_one`.
    exact spectralRadius_mixedTransfer_lt_one A B hA hB hAB
  -- Step 3: Powers converge to zero in CLM operator norm.
  have h_clm_tendsto :
      Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F' h_sr
  -- Step 4: Pointwise evaluation at X is continuous (via
  -- ContinuousLinearMap.apply), giving pointwise convergence.
  have h_eval_tendsto :
      Filter.Tendsto (fun n => (F' ^ n) X)
        Filter.atTop (nhds 0) := by
    have h_cont :=
      (ContinuousLinearMap.apply ℂ V X).continuous.tendsto
        (0 : V →L[ℂ] V)
    rw [map_zero] at h_cont
    exact h_cont.comp h_clm_tendsto
  -- Step 5: F^n(X) = F'^n(X) since Φ is an algebra equivalence
  -- that preserves the underlying function.
  suffices h_eq :
      ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X from by
    simp_rw [h_eq]; exact h_eval_tendsto
  intro n
  have h_pow : F' ^ n = Φ (F ^ n) := (map_pow Φ F n).symm
  simp only [h_pow]
  rfl

end SpectralConvergence

/-! ## Cross-correlation decay and block separation

Combining the iterated transfer formula with the spectral convergence,
we get the quantitative block separation statement: the MPV
cross-correlations between distinct blocks decay exponentially. -/

section BlockSeparation

/-- **Cross-correlation decay**: For injective MPS tensors `A` and `B`
that are not gauge-phase equivalent, the cross-correlation
$$\sum_\sigma \mathrm{tr}(\mathrm{evalWord}(A,\sigma) \cdot X \cdot
  \mathrm{evalWord}(B,\sigma)^\dagger)$$
converges to zero as the system size `N → ∞`.

This is the trace of `F_{AB}^N(X)`, which tends to zero since
`F_{AB}^N(X) → 0` by `mixedTransfer_pow_tendsto_zero`. -/
theorem cross_correlation_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto
      (fun N => Matrix.trace (((mixedTransferMap A B) ^ N) X))
      Filter.atTop (nhds 0) := by
  -- Compose: F^N(X) → 0 (by spectral gap) and trace is continuous.
  have h := mixedTransfer_pow_tendsto_zero A B hA hB hAB X
  have h_cont : Continuous (Matrix.traceLinearMap (Fin D) ℂ ℂ) :=
    LinearMap.continuous_of_finiteDimensional _
  have h2 : Filter.Tendsto
      (fun N => (Matrix.traceLinearMap (Fin D) ℂ ℂ) (((mixedTransferMap A B) ^ N) X))
      Filter.atTop (nhds 0) := by
    rw [← map_zero (Matrix.traceLinearMap (Fin D) ℂ ℂ)]
    exact h_cont.continuousAt.tendsto.comp h
  simpa [Matrix.traceLinearMap_apply] using h2

/-- **Self-correlation persists**: If `ρ` is a fixed point of `E_A`, then
`tr(E_A^N(ρ)) = tr(ρ)` for all `N`. This is the diagonal counterpart to
the off-diagonal decay: self-terms persist while cross-terms vanish. -/
theorem self_correlation_persists
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hfp : HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ) :
    ∀ N : ℕ,
      Matrix.trace (((transferMap (d := d) (D := D) A) ^ N) ρ) = Matrix.trace ρ := by
  intro N
  suffices hfix : ((transferMap (d := d) (D := D) A) ^ N) ρ = ρ by rw [hfix]
  induction N with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, hfp.fixed]

/-! ### Block separation

Combining the iterated transfer formula with spectral convergence:
the MPV cross-correlations between distinct blocks decay, while
self-correlations persist. -/

/-- **Block separation principle**: If the cross-correlation
`tr(F_{AB}^N(1))` vanishes for all `N`, then `F_{AB}(1) = 0`.

In fact the hypothesis at `N = 0` gives `tr(1) = D = 0`, so for `D ≥ 1`
this is vacuously true. The real content is in the *spectral gap* that
forces the cross-terms to vanish. -/
theorem block_separation_principle
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hAB : ¬ GaugePhaseEquiv A B)
    (h_cross : ∀ N : ℕ,
      Matrix.trace (((mixedTransferMap A B) ^ N) (1 : Matrix (Fin D) (Fin D) ℂ)) = 0) :
    mixedTransferMap A B (1 : Matrix (Fin D) (Fin D) ℂ) = 0 := by
  -- The hypothesis is vacuously false when D ≥ 1:
  -- h_cross 0 gives tr(F^0(I)) = tr(I) = D = 0, which contradicts D ≥ 1.
  -- When D = 0, all matrices over Fin 0 are trivially equal.
  by_cases hD : D = 0
  · -- D = 0: all matrices over empty index are equal
    subst hD; ext i; exact i.elim0
  · -- D ≥ 1: derive contradiction from h_cross 0
    exfalso
    have h0 := h_cross 0
    simp only [pow_zero, Module.End.one_apply, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_eq_zero] at h0
    exact hD h0

end BlockSeparation

end MPSTensor
