/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# A two-purity doubling criterion for a uniform spectral gap

This file formalizes the abstract part of the note *A thermal-MPO derivation of the spin-1 gap
bound* (dated October 7, 2026; cited below as *the thermal-MPO note*): a uniform lower bound on
the spectral gap of a family of finite-dimensional Hamiltonians, derived from two finite-size
purities, for any family whose partition functions are moment sums of a spatial transfer
operator.

## Setting

For each length `L`, the Hamiltonian is represented by its spectrum with multiplicity
`E L : ι L → ℝ`, over a finite nonempty index type. Then
* `partitionFunction E L β = ∑ₘ exp (-β Eₘ(L))` is `Z_L(β) = Tr e^{-β H_L}` (note, eq. (2));
* `thermalPurity E L β = Z_L(2β) / Z_L(β)²` is `P_τ(L, β)` (note, eq. (3));
* `spatialPurity E n β = Z_{2n}(β) / Z_n(β)²` is `P_s(n, β)` (note, eq. (6));
* `HasSpatialMomentForm E n₀` is the moment form `Z_L(β) = ∑ᵢ |λᵢ(β)|^L` (note, eq. (5)) for
  every even `L ≥ n₀`;
* `GapGT e c` says that the spectrum `e` has a nondegenerate lowest level with every other level
  more than `c` above it, which for ordered eigenvalues `E₀ ≤ E₁ ≤ ⋯` is `E₁ - E₀ > c`
  (`GapGT.lt_sub_of_monotone`).

## Main results

* `one_sub_squaredPurity_le_squaringDefect`: Lemma 1 (Squaring) of the note.
* `spatialPurity_two_mul`, `thermalPurity_four_mul`: Lemma 2 (Coupling), eqs. (9) and (10).
* `exp_neg_mul_sub_le_of_isMin`: the purity-to-gap bound, eq. (4).
* `doubling`: Lemma 3 (Doubling).
* `gapGT_of_purities`: Proposition 1 (Two-purity criterion).

## Scope

Theorem 1 of the note (the spin-one Heisenberg chain) is not formalized here. It rests on two
inputs outside this file: the continuous-time thermal MPO giving the moment form (5) for the
Heisenberg chain (the note's Appendix, citing Proposition 3.1 of its Ref. [1]), and the certified
numerical estimates `P_s(2304, 784), P_τ(4608, 784) ≥ 0.99` (Proposition 5.5 of Ref. [1]).
Given these as hypotheses, Theorem 1 is `gapGT_of_purities` with `n₀ = 2304`, `β₀ = 784`.

The moment form is stated with the eigenvalue moduli `|λᵢ(β)|` indexed by `ℕ` (a finite spectrum
is padded by zeros) and only for even lengths `L ≥ n₀`, which is all that the proofs use; this is
implied by the note's eq. (5).
-/

open Filter Finset Real

namespace ThermalPurityGap

/-! ### Lemma 1: squaring -/

/-- Finite form of the squaring inequality, in homogeneous power sums: for nonnegative `pᵢ`, with
`S_k = ∑ pᵢ^k`, one has `S₂ ≤ S₁²` and `2 (S₂² - S₄) ≤ (S₁² - S₂)²`. -/
theorem sq_sub_sum_sq_finset {κ : Type*} (s : Finset κ) (p : κ → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, p i ^ 2 ≤ (∑ i ∈ s, p i) ^ 2 ∧
      2 * ((∑ i ∈ s, p i ^ 2) ^ 2 - ∑ i ∈ s, p i ^ 4) ≤
        ((∑ i ∈ s, p i) ^ 2 - ∑ i ∈ s, p i ^ 2) ^ 2 := by
  classical
  suffices h : 0 ≤ ∑ i ∈ s, p i ∧ ∑ i ∈ s, p i ^ 2 ≤ (∑ i ∈ s, p i) ^ 2 ∧
      2 * ((∑ i ∈ s, p i ^ 2) ^ 2 - ∑ i ∈ s, p i ^ 4) ≤
        ((∑ i ∈ s, p i) ^ 2 - ∑ i ∈ s, p i ^ 2) ^ 2 from h.2
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2, h3⟩ := ih fun i hi ↦ hp i (mem_insert_of_mem hi)
    have hq := hp a (mem_insert_self a s)
    rw [sum_insert ha, sum_insert ha, sum_insert ha]
    have hT : 0 ≤ (∑ i ∈ s, p i) ^ 2 - ∑ i ∈ s, p i ^ 2 := by linarith
    refine ⟨by positivity, by nlinarith [mul_nonneg hq h1], ?_⟩
    nlinarith [mul_nonneg (mul_nonneg hq h1) hT, mul_nonneg (sq_nonneg (p a)) hT]

/-- The squaring inequality for summable nonnegative families, in homogeneous power sums. -/
theorem sq_sub_sum_sq_of_hasSum {κ : Type*} {p : κ → ℝ} (hp : ∀ i, 0 ≤ p i) {s₁ s₂ s₄ : ℝ}
    (h₁ : HasSum p s₁) (h₂ : HasSum (fun i ↦ p i ^ 2) s₂) (h₄ : HasSum (fun i ↦ p i ^ 4) s₄) :
    s₂ ≤ s₁ ^ 2 ∧ 2 * (s₂ ^ 2 - s₄) ≤ (s₁ ^ 2 - s₂) ^ 2 := by
  have hfin := fun s : Finset κ ↦ sq_sub_sum_sq_finset s p fun i _ ↦ hp i
  constructor
  · refine le_of_tendsto_of_tendsto' h₂ (h₁.pow 2) fun s ↦ (hfin s).1
  · refine le_of_tendsto_of_tendsto' ((((h₂.pow 2).sub h₄).const_mul 2))
      (((h₁.pow 2).sub h₂).pow 2) fun s ↦ (hfin s).2

/-- The function `f(z) = z² / (2 (1 - z)²)` of the note's Lemma 1, eq. (8), which bounds the
purity defect after squaring a spectrum. -/
noncomputable def squaringDefect (z : ℝ) : ℝ := z ^ 2 / (2 * (1 - z) ^ 2)

/-- `f` is increasing on `[0, 1)` (the thermal-MPO note, after Lemma 1). -/
theorem squaringDefect_mono {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w < 1) :
    squaringDefect z ≤ squaringDefect w := by
  unfold squaringDefect
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  have h1 : z * (1 - w) ≤ w * (1 - z) := by nlinarith
  have h2 : 0 ≤ z * (1 - w) := mul_nonneg hz (by linarith)
  nlinarith [mul_le_mul h1 h1 h2 (by nlinarith)]

/-- Homogeneous form of Lemma 1: `1 - S₄/S₂² ≤ f(1 - S₂/S₁²)`. -/
theorem one_sub_div_le_squaringDefect {s₁ s₂ s₄ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (h : 2 * (s₂ ^ 2 - s₄) ≤ (s₁ ^ 2 - s₂) ^ 2) :
    1 - s₄ / s₂ ^ 2 ≤ squaringDefect (1 - s₂ / s₁ ^ 2) := by
  unfold squaringDefect
  rw [sub_sub_cancel]
  have e1 : (1 - s₂ / s₁ ^ 2) ^ 2 / (2 * (s₂ / s₁ ^ 2) ^ 2) = (s₁ ^ 2 - s₂) ^ 2 / (2 * s₂ ^ 2) := by
    field_simp
  have e2 : 1 - s₄ / s₂ ^ 2 = (s₂ ^ 2 - s₄) / s₂ ^ 2 := by field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg s₂)]

/-- **Lemma 1 (Squaring)** of the thermal-MPO note, eq. (8). Let `pᵢ ≥ 0` with `∑ pᵢ = 1` and
purity `P = ∑ pᵢ²`. The squared spectrum `pᵢ² / P` has purity `P'` with `1 - P' ≤ f(1 - P)`. -/
theorem one_sub_squaredPurity_le_squaringDefect {κ : Type*} {p : κ → ℝ} (hp : ∀ i, 0 ≤ p i)
    (h₁ : HasSum p 1) :
    1 - ∑' i, (p i ^ 2 / ∑' j, p j ^ 2) ^ 2 ≤ squaringDefect (1 - ∑' i, p i ^ 2) := by
  have hle : ∀ i, p i ≤ 1 := fun i ↦ le_hasSum h₁ i fun j _ ↦ hp j
  have hs₂ : Summable fun i ↦ p i ^ 2 :=
    h₁.summable.of_nonneg_of_le (fun i ↦ by positivity) fun i ↦ by
      nlinarith [hp i, hle i]
  have hs₄ : Summable fun i ↦ p i ^ 4 :=
    h₁.summable.of_nonneg_of_le (fun i ↦ by positivity) fun i ↦ by
      have := pow_le_one₀ (n := 3) (hp i) (hle i)
      nlinarith [hp i, pow_nonneg (hp i) 3]
  set P := ∑' i, p i ^ 2
  have hP : 0 < P := by
    refine lt_of_le_of_ne (tsum_nonneg fun i ↦ by positivity) fun h ↦ ?_
    have hz : (fun i ↦ p i ^ 2) = 0 :=
      (hasSum_zero_iff_of_nonneg fun i ↦ by positivity).1 (by rw [h]; exact hs₂.hasSum)
    have hp0 : p = fun _ ↦ 0 := funext fun i ↦
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (congrFun hz i)
    have : (1 : ℝ) = 0 := h₁.unique (by rw [hp0]; exact hasSum_zero)
    norm_num at this
  have e : ∑' i, (p i ^ 2 / P) ^ 2 = (∑' i, p i ^ 4) / P ^ 2 := by
    rw [← tsum_div_const]
    exact tsum_congr fun i ↦ by ring
  rw [e]
  have h := (sq_sub_sum_sq_of_hasSum hp h₁ hs₂.hasSum hs₄.hasSum).2
  simpa using one_sub_div_le_squaringDefect one_pos hP h

/-- The numerical step in eq. (12) of the note: `f(1 - (1 - ε)³) ≤ 5 ε²` for `0 ≤ ε ≤ 1/100`. -/
theorem squaringDefect_le {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 100) :
    squaringDefect (1 - (1 - ε) ^ 3) ≤ 5 * ε ^ 2 := by
  unfold squaringDefect
  have hu1 : (1 - ε) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hu0 : 1 - 3 * ε ≤ (1 - ε) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (by linarith : (0 : ℝ) ≤ 3 - ε)]
  rw [sub_sub_cancel, div_le_iff₀ (by nlinarith)]
  generalize (1 - ε) ^ 3 = u at hu0 hu1 ⊢
  have h1 : (1 - u) ^ 2 ≤ (3 * ε) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : 9 ≤ 10 * u ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ε)]

/-- The squaring step used twice in Lemma 3: if a nonnegative summable family `p` has purity
`S₂/S₁² ≥ (1 - ε)³`, then its square has purity `S₄/S₂² ≥ 1 - 5ε²`. -/
theorem squaring_step {κ : Type*} {p : κ → ℝ} (hp : ∀ i, 0 ≤ p i) {s₁ s₂ s₄ : ℝ}
    (h₁ : HasSum p s₁) (h₂ : HasSum (fun i ↦ p i ^ 2) s₂) (h₄ : HasSum (fun i ↦ p i ^ 4) s₄)
    (hs₂ : 0 < s₂) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 100) (h : (1 - ε) ^ 3 ≤ s₂ / s₁ ^ 2) :
    1 - 5 * ε ^ 2 ≤ s₄ / s₂ ^ 2 := by
  obtain ⟨h21, hmain⟩ := sq_sub_sum_sq_of_hasSum hp h₁ h₂ h₄
  have hs₁ : 0 < s₁ := by
    have := hasSum_le (fun i ↦ hp i) hasSum_zero h₁
    rcases this.lt_or_eq with h' | h'
    · exact h'
    · subst h'; nlinarith
  have hP1 : s₂ / s₁ ^ 2 ≤ 1 := (div_le_one (by positivity)).2 h21
  have hstep := one_sub_div_le_squaringDefect hs₁ hs₂ hmain
  have hu : 0 < (1 - ε) ^ 3 := pow_pos (by linarith) 3
  have hmono : squaringDefect (1 - s₂ / s₁ ^ 2) ≤ squaringDefect (1 - (1 - ε) ^ 3) :=
    squaringDefect_mono (by linarith) (by linarith) (by linarith)
  linarith [squaringDefect_le hε₀ hε₁]

/-! ### Thermal and spatial purities -/

variable {ι : ℕ → Type*} [∀ L, Fintype (ι L)] [∀ L, Nonempty (ι L)]

/-- The partition function `Z_L(β) = Tr e^{-β H_L} = ∑ₘ e^{-β Eₘ(L)}` of a Hamiltonian with
spectrum (with multiplicity) `E L` (the thermal-MPO note, eq. (2)). -/
noncomputable def partitionFunction (E : (L : ℕ) → ι L → ℝ) (L : ℕ) (β : ℝ) : ℝ :=
  ∑ m, exp (-(β * E L m))

/-- The thermal purity `P_τ(L, β) = Tr ρ_L(β)² = Z_L(2β) / Z_L(β)²` (the thermal-MPO note,
eq. (3)). -/
noncomputable def thermalPurity (E : (L : ℕ) → ι L → ℝ) (L : ℕ) (β : ℝ) : ℝ :=
  partitionFunction E L (2 * β) / partitionFunction E L β ^ 2

/-- The spatial purity `P_s(n, β) = Z_{2n}(β) / Z_n(β)²` (the thermal-MPO note, eq. (6)). -/
noncomputable def spatialPurity (E : (L : ℕ) → ι L → ℝ) (n : ℕ) (β : ℝ) : ℝ :=
  partitionFunction E (2 * n) β / partitionFunction E n β ^ 2

/-- The moment form of the thermal-MPO note, eq. (5): for every `β > 0` there are nonnegative
numbers `μᵢ = |λᵢ(β)|`, the moduli of the eigenvalues of the spatial transfer operator `X_β`,
with `Z_L(β) = ∑ᵢ μᵢ^L` for every even length `L ≥ n₀`. -/
def HasSpatialMomentForm (E : (L : ℕ) → ι L → ℝ) (n₀ : ℕ) : Prop :=
  ∀ β : ℝ, 0 < β → ∃ μ : ℕ → ℝ, (∀ i, 0 ≤ μ i) ∧
    ∀ L : ℕ, n₀ ≤ L → Even L → HasSum (fun i ↦ μ i ^ L) (partitionFunction E L β)

/-- The spectrum `e` has a nondegenerate lowest level `e m₀` and every other level lies more than
`c` above it. For ordered eigenvalues `E₀ ≤ E₁ ≤ ⋯` this is the gap bound `E₁ - E₀ > c`. -/
def GapGT {κ : Type*} (e : κ → ℝ) (c : ℝ) : Prop :=
  ∃ m₀, ∀ m, m ≠ m₀ → e m₀ + c < e m

/-- For an ordered spectrum `E₀ ≤ E₁ ≤ ⋯`, `GapGT` gives `Δ = E₁ - E₀ > c`. -/
theorem GapGT.lt_sub_of_monotone {N : ℕ} {e : Fin (N + 2) → ℝ} (he : Monotone e) {c : ℝ}
    (h : GapGT e c) : c < e 1 - e 0 := by
  obtain ⟨m₀, hm₀⟩ := h
  by_cases h0 : m₀ = 0
  · subst h0; linarith [hm₀ 1 (by simp)]
  · have := hm₀ 0 (Ne.symm h0)
    have := he (Fin.zero_le m₀)
    have := he (Fin.zero_le (1 : Fin (N + 2)))
    linarith

section Basic

variable (E : (L : ℕ) → ι L → ℝ)

theorem partitionFunction_pos (L : ℕ) (β : ℝ) : 0 < partitionFunction E L β :=
  Finset.sum_pos (fun _ _ ↦ exp_pos _) univ_nonempty

theorem exp_neg_mul_two_mul (β e : ℝ) : exp (-(2 * β * e)) = exp (-(β * e)) ^ 2 := by
  rw [← exp_nat_mul]; ring_nf

omit [∀ L, Nonempty (ι L)] in
theorem partitionFunction_two_mul (L : ℕ) (β : ℝ) :
    partitionFunction E L (2 * β) = ∑ m, exp (-(β * E L m)) ^ 2 := by
  simp only [partitionFunction, exp_neg_mul_two_mul]

omit [∀ L, Nonempty (ι L)] in
theorem partitionFunction_four_mul (L : ℕ) (β : ℝ) :
    partitionFunction E L (2 * (2 * β)) = ∑ m, exp (-(β * E L m)) ^ 4 := by
  simp only [partitionFunction, exp_neg_mul_two_mul, ← pow_mul]

theorem thermalPurity_pos (L : ℕ) (β : ℝ) : 0 < thermalPurity E L β :=
  div_pos (partitionFunction_pos E _ _) (pow_pos (partitionFunction_pos E _ _) 2)

theorem spatialPurity_pos (n : ℕ) (β : ℝ) : 0 < spatialPurity E n β :=
  div_pos (partitionFunction_pos E _ _) (pow_pos (partitionFunction_pos E _ _) 2)

/-- `P_τ(L, β) ≤ 1`. -/
theorem thermalPurity_le_one (L : ℕ) (β : ℝ) : thermalPurity E L β ≤ 1 := by
  rw [thermalPurity, div_le_one (pow_pos (partitionFunction_pos E _ _) 2),
    partitionFunction_two_mul]
  exact (sq_sub_sum_sq_finset univ _ fun m _ ↦ (exp_pos _).le).1

/-- Lemma 1 applied to the Gibbs spectrum: squaring `ρ_L(β)` gives `ρ_L(2β)`. -/
theorem thermalPurity_two_mul_ge (L : ℕ) (β : ℝ) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 100)
    (h : (1 - ε) ^ 3 ≤ thermalPurity E L β) : 1 - 5 * ε ^ 2 ≤ thermalPurity E L (2 * β) := by
  have hp : ∀ m, 0 ≤ exp (-(β * E L m)) := fun m ↦ (exp_pos _).le
  have h₁ := hasSum_fintype fun m ↦ exp (-(β * E L m))
  have h₂ := hasSum_fintype fun m ↦ exp (-(β * E L m)) ^ 2
  have h₄ := hasSum_fintype fun m ↦ exp (-(β * E L m)) ^ 4
  rw [← partitionFunction_two_mul] at h₂
  rw [← partitionFunction_four_mul] at h₄
  exact squaring_step hp h₁ h₂ h₄ (partitionFunction_pos E _ _) hε₀ hε₁ h

/-- **Lemma 2 (Coupling)** of the thermal-MPO note, eq. (9):
`P_s(n, 2β) = P_s(n, β)² P_τ(2n, β) / P_τ(n, β)²`. -/
theorem spatialPurity_two_mul (n : ℕ) (β : ℝ) :
    spatialPurity E n (2 * β) =
      spatialPurity E n β ^ 2 * thermalPurity E (2 * n) β / thermalPurity E n β ^ 2 := by
  have := partitionFunction_pos E n β
  have := partitionFunction_pos E n (2 * β)
  have := partitionFunction_pos E (2 * n) β
  simp only [spatialPurity, thermalPurity]
  field_simp

/-- **Lemma 2 (Coupling)** of the thermal-MPO note, eq. (10):
`P_τ(4n, β) = P_τ(2n, β)² P_s(2n, 2β) / P_s(2n, β)²`. -/
theorem thermalPurity_four_mul (n : ℕ) (β : ℝ) :
    thermalPurity E (4 * n) β =
      thermalPurity E (2 * n) β ^ 2 * spatialPurity E (2 * n) (2 * β) /
        spatialPurity E (2 * n) β ^ 2 := by
  have e : 4 * n = 2 * (2 * n) := by ring
  have := partitionFunction_pos E (2 * n) β
  have := partitionFunction_pos E (2 * n) (2 * β)
  have := partitionFunction_pos E (2 * (2 * n)) β
  simp only [spatialPurity, thermalPurity, e]
  field_simp

/-- Under the moment form, `P_s(n, β) ≤ 1` and, at three successive doublings of `n`, the squared
spatial spectrum satisfies Lemma 1. -/
theorem spatialPurity_le_one {n₀ : ℕ} (hZ : HasSpatialMomentForm E n₀) {n : ℕ} (hn : n₀ ≤ n)
    (hne : Even n) {β : ℝ} (hβ : 0 < β) : spatialPurity E n β ≤ 1 := by
  obtain ⟨μ, hμ, hsum⟩ := hZ β hβ
  have h₁ := hsum n hn hne
  have h₂ := hsum (2 * n) (by omega) (by simp)
  have h₄ := hsum (2 * (2 * n)) (by omega) (by simp)
  simp only [pow_mul'] at h₂ h₄
  have h₄' : HasSum (fun i ↦ (μ i ^ n) ^ 4) (partitionFunction E (2 * (2 * n)) β) := by
    convert h₄ using 1; ext i; ring
  rw [spatialPurity, div_le_one (pow_pos (partitionFunction_pos E _ _) 2)]
  exact (sq_sub_sum_sq_of_hasSum (fun i ↦ pow_nonneg (hμ i) n) h₁ h₂ h₄').1

/-- Lemma 1 applied to the spatial spectrum: squaring `σ_n(β)` gives `σ_{2n}(β)`. -/
theorem spatialPurity_two_mul_ge {n₀ : ℕ} (hZ : HasSpatialMomentForm E n₀) {n : ℕ} (hn : n₀ ≤ n)
    (hne : Even n) {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 100)
    (h : (1 - ε) ^ 3 ≤ spatialPurity E n β) : 1 - 5 * ε ^ 2 ≤ spatialPurity E (2 * n) β := by
  obtain ⟨μ, hμ, hsum⟩ := hZ β hβ
  have h₁ := hsum n hn hne
  have h₂ := hsum (2 * n) (by omega) (by simp)
  have h₄ := hsum (2 * (2 * n)) (by omega) (by simp)
  simp only [pow_mul'] at h₂ h₄
  have h₄' : HasSum (fun i ↦ (μ i ^ n) ^ 4) (partitionFunction E (2 * (2 * n)) β) := by
    convert h₄ using 1; ext i; ring
  exact squaring_step (fun i ↦ pow_nonneg (hμ i) n) h₁ h₂ h₄'
    (partitionFunction_pos E _ _) hε₀ hε₁ h

/-- The purity-to-gap bound, eq. (4) of the thermal-MPO note: if `m₀` is a lowest level and
`m ≠ m₀`, then `e^{-β (E_m - E_{m₀})} ≤ (1 - P_τ) / P_τ`. -/
theorem exp_neg_mul_sub_le_of_isMin (L : ℕ) {β : ℝ} (hβ : 0 ≤ β) {m₀ m : ι L}
    (hmin : ∀ m', E L m₀ ≤ E L m') (hne : m ≠ m₀) :
    exp (-(β * (E L m - E L m₀))) ≤ (1 - thermalPurity E L β) / thermalPurity E L β := by
  classical
  set a : ι L → ℝ := fun m ↦ exp (-(β * E L m))
  have ha : ∀ m, 0 < a m := fun m ↦ exp_pos _
  set Z := ∑ m, a m
  set S := ∑ m, a m ^ 2
  have hZ : Z = partitionFunction E L β := rfl
  have hS : S = partitionFunction E L (2 * β) := (partitionFunction_two_mul E L β).symm
  have hZpos : 0 < Z := partitionFunction_pos E L β
  have hSpos : 0 < S := hS ▸ partitionFunction_pos E L (2 * β)
  have hmax : ∀ m', a m' ≤ a m₀ := fun m' ↦
    exp_le_exp.2 (by nlinarith [hmin m'])
  have hSle : S ≤ a m₀ * Z := by
    rw [mul_sum]
    exact sum_le_sum fun m' _ ↦ by nlinarith [hmax m', ha m']
  have hpair : a m + a m₀ ≤ Z := by
    rw [← sum_pair hne]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ (ha i).le
  have hexp : exp (-(β * (E L m - E L m₀))) = a m / a m₀ := by
    simp only [a, ← exp_sub]; ring_nf
  have hP : thermalPurity E L β = S / Z ^ 2 := by rw [thermalPurity, hS, hZ]
  rw [hexp, hP, show (1 - S / Z ^ 2) / (S / Z ^ 2) = (Z ^ 2 - S) / S by field_simp,
    div_le_div_iff₀ (ha m₀) hSpos]
  nlinarith [mul_le_mul_of_nonneg_right hpair hSpos.le, mul_le_mul_of_nonneg_left hSle hZpos.le]

end Basic

/-! ### Lemma 3 and Proposition 1 -/

/-- **Lemma 3 (Doubling)** of the thermal-MPO note. Assume the moment form (5), let `n` be even
and `0 ≤ ε ≤ 1/100`. If `P_s(n, β), P_τ(2n, β) ≥ 1 - ε`, then
`P_s(2n, 2β), P_τ(4n, 2β) ≥ 1 - 5ε²`. -/
theorem doubling (E : (L : ℕ) → ι L → ℝ) {n₀ : ℕ} (hZ : HasSpatialMomentForm E n₀) {n : ℕ}
    (hn : n₀ ≤ n) (hne : Even n) {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε₁ : ε ≤ 1 / 100) (hs : 1 - ε ≤ spatialPurity E n β)
    (ht : 1 - ε ≤ thermalPurity E (2 * n) β) :
    1 - 5 * ε ^ 2 ≤ spatialPurity E (2 * n) (2 * β) ∧
      1 - 5 * ε ^ 2 ≤ thermalPurity E (4 * n) (2 * β) := by
  have h1ε : 0 ≤ 1 - ε := by linarith
  have h5 : 5 * ε ^ 2 ≤ ε := by nlinarith
  -- Spatial purity: eq. (9) and `P_τ(n, β) ≤ 1` give `P_s(n, 2β) ≥ (1 - ε)³`.
  have hτn := thermalPurity_le_one E n β
  have hτn0 := thermalPurity_pos E n β
  have hs2 : (1 - ε) ^ 3 ≤ spatialPurity E n (2 * β) := by
    rw [spatialPurity_two_mul, le_div_iff₀ (by positivity)]
    have hsq : (1 - ε) ^ 2 ≤ spatialPurity E n β ^ 2 := pow_le_pow_left₀ h1ε hs 2
    have hτsq : thermalPurity E n β ^ 2 ≤ 1 := pow_le_one₀ hτn0.le hτn
    have hspos := spatialPurity_pos E n (2 * β)
    nlinarith [mul_le_mul hsq ht h1ε (by positivity), pow_nonneg h1ε 3,
      mul_le_mul_of_nonneg_left hτsq hspos.le]
  have hsp := spatialPurity_two_mul_ge E hZ hn hne (by positivity) hε₀ hε₁ hs2
  refine ⟨hsp, ?_⟩
  -- Thermal purity: eq. (10) and `P_s(2n, β) ≤ 1` give `P_τ(4n, β) ≥ (1 - ε)³`.
  have hτ4 : (1 - ε) ^ 3 ≤ thermalPurity E (4 * n) β := by
    rw [thermalPurity_four_mul, le_div_iff₀ (pow_pos (spatialPurity_pos E _ _) 2)]
    have h2n := spatialPurity_le_one E hZ (by omega : n₀ ≤ 2 * n) (by simp) hβ
    have : spatialPurity E (2 * n) β ^ 2 ≤ 1 :=
      pow_le_one₀ (spatialPurity_pos E _ _).le h2n
    have : (1 - ε) ^ 2 ≤ thermalPurity E (2 * n) β ^ 2 := pow_le_pow_left₀ h1ε ht 2
    have hprod : (1 - ε) ^ 2 * (1 - ε) ≤
        thermalPurity E (2 * n) β ^ 2 * spatialPurity E (2 * n) (2 * β) :=
      mul_le_mul this (by linarith) h1ε (by positivity)
    nlinarith [pow_nonneg h1ε 3]
  exact thermalPurity_two_mul_ge E (4 * n) β hε₀ hε₁ hτ4

/-- The defect sequence `ε_j = 20^{-2^j} / 5` of the thermal-MPO note, eq. (13). -/
noncomputable def defect (j : ℕ) : ℝ := (1 / 5) * (1 / 20) ^ 2 ^ j

theorem defect_succ (j : ℕ) : defect (j + 1) = 5 * defect j ^ 2 := by
  simp only [defect, pow_succ 2 j, pow_mul]; ring

theorem defect_pos (j : ℕ) : 0 < defect j := by unfold defect; positivity

theorem defect_le (j : ℕ) : defect j ≤ 1 / 100 := by
  have : (1 / 20 : ℝ) ^ 2 ^ j ≤ 1 / 20 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (pow_pos two_pos j).ne'
  unfold defect; linarith

/-- The induction on scale in the proof of Proposition 1: with `n_j = n₀ 2^j`, `β_j = β₀ 2^j`,
`P_s(n_j, β_j), P_τ(2n_j, β_j) ≥ 1 - ε_j`. -/
theorem purities_ge_defect (E : (L : ℕ) → ι L → ℝ) {n₀ : ℕ} (hn₀ : Even n₀) {β₀ : ℝ}
    (hβ₀ : 0 < β₀) (hZ : HasSpatialMomentForm E n₀)
    (hs : 99 / 100 ≤ spatialPurity E n₀ β₀) (ht : 99 / 100 ≤ thermalPurity E (2 * n₀) β₀)
    (j : ℕ) :
    1 - defect j ≤ spatialPurity E (n₀ * 2 ^ j) (β₀ * 2 ^ j) ∧
      1 - defect j ≤ thermalPurity E (2 * (n₀ * 2 ^ j)) (β₀ * 2 ^ j) := by
  induction j with
  | zero => norm_num [defect] at hs ht ⊢; exact ⟨hs, ht⟩
  | succ j ih =>
    have h := doubling E hZ (n := n₀ * 2 ^ j) (Nat.le_mul_of_pos_right _ (by positivity))
      (hn₀.mul_right _) (by positivity) (defect_pos j).le (defect_le j) ih.1 ih.2
    rw [defect_succ]
    have e1 : n₀ * 2 ^ (j + 1) = 2 * (n₀ * 2 ^ j) := by ring
    have e2 : 2 * (n₀ * 2 ^ (j + 1)) = 4 * (n₀ * 2 ^ j) := by ring
    have e3 : β₀ * 2 ^ (j + 1) = 2 * (β₀ * 2 ^ j) := by ring
    rw [e1, e3]; rw [e1] at e2; rw [e2]
    exact h

/-- Every even length `L ≥ n₀ > 0` lies in a dyadic window `n₀ 2^j ≤ L ≤ 2 n₀ 2^j`. -/
theorem exists_dyadic_window {n₀ L : ℕ} (hn₀ : 0 < n₀) (hL : n₀ ≤ L) :
    ∃ j, n₀ * 2 ^ j ≤ L ∧ L ≤ 2 * (n₀ * 2 ^ j) := by
  have hq : L / n₀ ≠ 0 := (Nat.div_pos hL hn₀).ne'
  refine ⟨Nat.log 2 (L / n₀), ?_, ?_⟩
  · calc n₀ * 2 ^ Nat.log 2 (L / n₀) ≤ n₀ * (L / n₀) :=
          Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hq)
      _ ≤ L := Nat.mul_div_le L n₀
  · have h1 := Nat.lt_pow_succ_log_self one_lt_two (L / n₀)
    have h2 : L < n₀ * (L / n₀ + 1) := by
      rw [mul_comm]; exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hn₀
    calc L ≤ n₀ * (L / n₀ + 1) := h2.le
      _ ≤ n₀ * 2 ^ (Nat.log 2 (L / n₀)).succ := Nat.mul_le_mul_left _ h1
      _ = 2 * (n₀ * 2 ^ Nat.log 2 (L / n₀)) := by rw [pow_succ]; ring

/-- Monotonicity of `ℓ^p` norms, as used in eq. (14): for nonnegative `μ` and `0 < p ≤ q`,
`∑ μᵢ^q ≤ (∑ μᵢ^p)^{q/p}`. -/
theorem hasSum_pow_le_rpow {μ : ℕ → ℝ} (hμ : ∀ i, 0 ≤ μ i) {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q)
    {Zp Zq : ℝ} (hZp : HasSum (fun i ↦ μ i ^ p) Zp) (hZq : HasSum (fun i ↦ μ i ^ q) Zq) :
    Zq ≤ Zp ^ ((q : ℝ) / p) := by
  have hZp0 : 0 ≤ Zp := hasSum_le (fun i ↦ pow_nonneg (hμ i) p) hasSum_zero hZp
  set r : ℝ := (q : ℝ) / p
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hr1 : 1 ≤ r := (one_le_div hp').2 (by exact_mod_cast hpq)
  have hterm : ∀ i, μ i ^ q = (μ i ^ p) ^ r := fun i ↦ by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hμ i)]
    congr 1; simp only [r]; field_simp
  have hle : ∀ i, μ i ^ q ≤ Zp ^ (r - 1) * μ i ^ p := fun i ↦ by
    have h0 : 0 ≤ μ i ^ p := pow_nonneg (hμ i) p
    rw [hterm, show r = (r - 1) + 1 by ring, Real.rpow_add' h0 (by linarith), Real.rpow_one,
      add_sub_cancel_right]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h0
      (le_hasSum hZp i fun j _ ↦ pow_nonneg (hμ j) p) (by linarith)) h0
  calc Zq ≤ Zp ^ (r - 1) * Zp := hasSum_le hle hZq (hZp.mul_left _)
    _ = Zp ^ r := by
      rcases hZp0.lt_or_eq with h | h
      · rw [← Real.rpow_add_one h.ne']; ring_nf
      · rw [← h, mul_zero, Real.zero_rpow (by linarith)]

/-- **Proposition 1 (Two-purity criterion)** of the thermal-MPO note. Assume the moment form (5).
Let `n₀` be even and `β₀ > 0`, with `P_s(n₀, β₀), P_τ(2n₀, β₀) ≥ 0.99`. Then the spectral gap
satisfies `Δ_L > (log 20) / β₀` for every even `L ≥ n₀`.

The note assumes `n₀ ≥ 4`; the proof uses only `n₀ > 0`. -/
theorem gapGT_of_purities (E : (L : ℕ) → ι L → ℝ) {n₀ : ℕ} (hn₀ : 0 < n₀) (hn₀e : Even n₀)
    {β₀ : ℝ} (hβ₀ : 0 < β₀) (hZ : HasSpatialMomentForm E n₀)
    (hs : 99 / 100 ≤ spatialPurity E n₀ β₀) (ht : 99 / 100 ≤ thermalPurity E (2 * n₀) β₀)
    {L : ℕ} (hL : n₀ ≤ L) (hLe : Even L) : GapGT (E L) (log 20 / β₀) := by
  obtain ⟨j, hjL, hLj⟩ := exists_dyadic_window hn₀ hL
  set n := n₀ * 2 ^ j with hn_def
  set β := β₀ * 2 ^ j with hβ_def
  set ε := defect j
  have hn0 : 0 < n := by positivity
  have hnn₀ : n₀ ≤ n := Nat.le_mul_of_pos_right _ (by positivity)
  have hne : Even n := hn₀e.mul_right _
  have hβ : 0 < β := by positivity
  obtain ⟨hsj, htj⟩ := purities_ge_defect E hn₀e hβ₀ hZ hs ht j
  have hε₀ := (defect_pos j).le
  have hε₁ := defect_le j
  -- Interpolation, eqs. (14) and (15): `P_τ(L, β_j) ≥ (1 - ε_j)³`.
  obtain ⟨μ, hμ, hsum⟩ := hZ β hβ
  obtain ⟨ν, hν, hsum₂⟩ := hZ (2 * β) (by positivity)
  set A := partitionFunction E L β
  set B := partitionFunction E n β
  set C := partitionFunction E L (2 * β)
  set D := partitionFunction E (2 * n) (2 * β)
  have hA := partitionFunction_pos E L β
  have hB := partitionFunction_pos E n β
  have hC := partitionFunction_pos E L (2 * β)
  have hD := partitionFunction_pos E (2 * n) (2 * β)
  set r : ℝ := (L : ℝ) / (2 * n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL' : (n : ℝ) ≤ L := by exact_mod_cast hjL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast lt_of_lt_of_le hn0 hjL
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := (div_le_one (by positivity)).2 (by exact_mod_cast hLj)
  have hAB : A ≤ B ^ (2 * r) := by
    have := hasSum_pow_le_rpow hμ hn0 hjL (hsum n hnn₀ hne) (hsum L hL hLe)
    convert this using 2; simp only [r]; field_simp
  have hDC : D ≤ C ^ r⁻¹ := by
    have := hasSum_pow_le_rpow hν (by omega) hLj (hsum₂ L hL hLe)
      (hsum₂ (2 * n) (by omega) (by simp))
    convert this using 2; simp [r]
  have hDr : D ^ r ≤ C := by
    calc D ^ r ≤ (C ^ r⁻¹) ^ r := Real.rpow_le_rpow hD.le hDC hr0.le
      _ = C := Real.rpow_inv_rpow hC.le hr0.ne'
  have hA2 : A ^ 2 ≤ (B ^ 4) ^ r := by
    calc A ^ 2 ≤ (B ^ (2 * r)) ^ 2 := pow_le_pow_left₀ hA.le hAB 2
      _ = (B ^ 4) ^ r := by
        rw [← Real.rpow_mul_natCast hB.le, ← Real.rpow_natCast_mul hB.le]; ring_nf
  set x := D / B ^ 4
  have hx : x = thermalPurity E (2 * n) β * spatialPurity E n β ^ 2 := by
    have := partitionFunction_pos E (2 * n) β
    simp only [x, D, B, thermalPurity, spatialPurity]
    field_simp
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx]
    have h1 := thermalPurity_le_one E (2 * n) β
    have h2 := spatialPurity_le_one E hZ hnn₀ hne hβ
    have h3 := thermalPurity_pos E (2 * n) β
    nlinarith [pow_le_one₀ (n := 2) (spatialPurity_pos E n β).le h2]
  have hxε : (1 - ε) ^ 3 ≤ x := by
    rw [hx]
    have h1ε : 0 ≤ 1 - ε := by linarith
    have : (1 - ε) ^ 2 ≤ spatialPurity E n β ^ 2 := pow_le_pow_left₀ h1ε hsj 2
    nlinarith [mul_le_mul htj this (by positivity) (thermalPurity_pos E (2 * n) β).le]
  have hτL : (1 - ε) ^ 3 ≤ thermalPurity E L β := by
    calc (1 - ε) ^ 3 ≤ x := hxε
      _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ r := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hr1
      _ = D ^ r / (B ^ 4) ^ r := Real.div_rpow hD.le (by positivity) r
      _ ≤ C / A ^ 2 := div_le_div₀ hC.le hDr (by positivity) hA2
      _ = thermalPurity E L β := rfl
  have hτL' : 1 - 3 * ε ≤ thermalPurity E L β := by
    nlinarith [sq_nonneg ε, mul_nonneg hε₀ (sq_nonneg ε)]
  -- From purity to a gap, eqs. (4) and (16).
  obtain ⟨m₀, -, hm₀⟩ := exists_min_image univ (E L) univ_nonempty
  refine ⟨m₀, fun m hm ↦ ?_⟩
  have h4 := exp_neg_mul_sub_le_of_isMin E L hβ.le (fun m' ↦ hm₀ m' (mem_univ _)) hm
  set y : ℝ := (1 / 20) ^ 2 ^ j
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 / 20 := pow_le_of_le_one (by norm_num) (by norm_num) (pow_pos two_pos j).ne'
  have hPpos := thermalPurity_pos E L β
  have h16 : (1 - thermalPurity E L β) / thermalPurity E L β < y := by
    rw [div_lt_iff₀ hPpos]
    have : ε = y / 5 := by simp only [ε, defect, y]; ring
    nlinarith
  have hlt : -(β * (E L m - E L m₀)) < log y :=
    (lt_log_iff_exp_lt hy0).2 (lt_of_le_of_lt h4 h16)
  have hlogy : log y = -(2 ^ j * log 20) := by
    simp only [y, log_pow, one_div, log_inv]; push_cast; ring
  rw [hlogy] at hlt
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have : log 20 < β₀ * (E L m - E L m₀) := by
    have : 2 ^ j * log 20 < 2 ^ j * (β₀ * (E L m - E L m₀)) := by
      simp only [hβ_def] at hlt; nlinarith
    exact lt_of_mul_lt_mul_left this h2j.le
  have : log 20 / β₀ < E L m - E L m₀ := by rwa [div_lt_iff₀ hβ₀, mul_comm]
  linarith

end ThermalPurityGap
