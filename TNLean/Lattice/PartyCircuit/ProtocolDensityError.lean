/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ProductReferenceDensityError

/-!
# Error and normalization of the distributed protocol

Section 8.1 of the polynomial-PEPS manuscript turns the protocol of Proposition 7.1 into a
density estimate. The protocol is described by a reference trajectory `r₀, r₁, …, rₙ`, whose
last vector is the product `Ω ⊗ Ξ` of the target with a private factor of norm in
`[1 - C L⁻⁵⁷, 1]` (`eq:reference-junk`), and by the selected contractions `S_t`, each taking
`r_t` within `C L⁻²⁰` of `r_{t+1}`. There are at most `C L³` changes. The actual vector
`Ψ = S_{n-1} ⋯ S₀ r₀` then satisfies

* `‖Ψ - Ω ⊗ Ξ‖ ≤ C L⁻¹⁷` and `‖Ψ‖ ≤ 1`, by telescoping a product of contractions;
* `‖Tr_private |Ψ⟩⟨Ψ| - |Ω⟩⟨Ω|‖₁ ≤ C L⁻¹⁰` (`eq:protocol-density`);
* `‖σ - |Ω⟩⟨Ω|‖₁ ≤ C L⁻⁵` for every operator `σ` within `C L⁻⁵` of the actual physical
  density, as supplied by the compression theorem with accuracy `L⁻⁵`
  (`eq:compressed-density`).

The spaces of the trajectory may change from step to step, as parties are born and private
registers are added. The reference trajectory, the step errors, the number of changes, the
private factor and the compressed operator are hypotheses: they are the outputs of
Proposition 7.1, the small-patch rewrite lemma `lem:small-rewrite` and Theorem 5.2, which are
not constructed here. Every final constant is an explicit expression in the supplied
constants.

## Main results

* `TNLean.Lattice.PartyCircuit.norm_trajectory_sub_reference_le`: the accumulated vector error
  of a chain of contractions is at most the sum of the step errors.
* `TNLean.Lattice.PartyCircuit.norm_trajectory_le`: a chain of contractions does not increase
  the norm.
* `TNLean.Lattice.PartyCircuit.norm_protocol_sub_reference_le`: the `C L⁻¹⁷` vector error.
* `TNLean.Lattice.PartyCircuit.rectangularTraceNorm_protocol_density_sub_le`:
  `eq:protocol-density`.
* `TNLean.Lattice.PartyCircuit.rectangularTraceNorm_compressed_density_sub_le`:
  `eq:compressed-density`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `07-assembly.tex:9–63`, immutable
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These are original proofs; no OpenAI
  Lean code is copied or adapted.
-/

open scoped Matrix

noncomputable section

namespace TNLean.Lattice.PartyCircuit

section Trajectory

variable {𝕜 : Type*} [Semiring 𝕜] {E : ℕ → Type*} [∀ t, SeminormedAddCommGroup (E t)]
  [∀ t, Module 𝕜 (E t)]

/-- **Telescoping a chain of contractions.** Let `x` be the trajectory of the maps `S_t`
started at `r₀`, each `S_t` contracting the norm. Its distance from the reference trajectory
`r` after `n` steps is at most the sum of the step errors `‖S_t r_t - r_{t+1}‖`. The spaces
`E t` may change from step to step.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, "Telescoping a product of
contractions bounds the accumulated vector error by the sum of the individual errors",
`07-assembly.tex:33–40`. -/
theorem norm_trajectory_sub_reference_le (S : (t : ℕ) → E t →ₗ[𝕜] E (t + 1))
    (x r : (t : ℕ) → E t) (n : ℕ) (hS : ∀ t < n, ∀ v, ‖S t v‖ ≤ ‖v‖)
    (hx₀ : x 0 = r 0) (hx : ∀ t < n, x (t + 1) = S t (x t)) :
    ‖x n - r n‖ ≤ ∑ t ∈ Finset.range n, ‖S t (r t) - r (t + 1)‖ := by
  induction n with
  | zero => simp [hx₀]
  | succ n ih =>
    have ih' := ih (fun t ht ↦ hS t (ht.trans n.lt_succ_self))
      (fun t ht ↦ hx t (ht.trans n.lt_succ_self))
    rw [Finset.sum_range_succ, hx n n.lt_succ_self]
    calc
      ‖S n (x n) - r (n + 1)‖ = ‖S n (x n - r n) + (S n (r n) - r (n + 1))‖ := by
        rw [map_sub]
        congr 1
        abel
      _ ≤ ‖S n (x n - r n)‖ + ‖S n (r n) - r (n + 1)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ((hS n n.lt_succ_self _).trans ih') le_rfl

/-- A chain of contractions does not increase the norm of its starting vector.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, the bound `‖Ψ‖ ≤ 1`,
`07-assembly.tex:38–41`. -/
theorem norm_trajectory_le (S : (t : ℕ) → E t →ₗ[𝕜] E (t + 1)) (x : (t : ℕ) → E t)
    (n : ℕ) (hS : ∀ t < n, ∀ v, ‖S t v‖ ≤ ‖v‖) (hx : ∀ t < n, x (t + 1) = S t (x t)) :
    ‖x n‖ ≤ ‖x 0‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hx n n.lt_succ_self]
    exact (hS n n.lt_succ_self _).trans
      (ih (fun t ht ↦ hS t (ht.trans n.lt_succ_self))
        (fun t ht ↦ hx t (ht.trans n.lt_succ_self)))

/-- **The accumulated protocol error.** On a square of side `L ≥ 1`, at most `C_ch L³`
changes, each taking its reference vector within `C_step L⁻²⁰` of the next one, leave the
actual vector within `C_ch C_step L⁻¹⁷` of the final reference vector.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, "Each selected change therefore
takes its reference vector within `O(L⁻²⁰)` of the next one" and the bound
`‖Ψ - Ω ⊗ Ξ‖ ≤ C L⁻¹⁷`, `07-assembly.tex:18–41`. -/
theorem norm_protocol_sub_reference_le (S : (t : ℕ) → E t →ₗ[𝕜] E (t + 1))
    (x r : (t : ℕ) → E t) {n L : ℕ} (hL : 1 ≤ L) {C_ch C_step : ℝ} (hC_step : 0 ≤ C_step)
    (hn : (n : ℝ) ≤ C_ch * (L : ℝ) ^ 3) (hS : ∀ t < n, ∀ v, ‖S t v‖ ≤ ‖v‖)
    (hx₀ : x 0 = r 0) (hx : ∀ t < n, x (t + 1) = S t (x t))
    (hstep : ∀ t < n, ‖S t (r t) - r (t + 1)‖ ≤ C_step / (L : ℝ) ^ 20) :
    ‖x n - r n‖ ≤ C_ch * C_step / (L : ℝ) ^ 17 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    ‖x n - r n‖ ≤ ∑ t ∈ Finset.range n, ‖S t (r t) - r (t + 1)‖ :=
      norm_trajectory_sub_reference_le S x r n hS hx₀ hx
    _ ≤ ∑ _t ∈ Finset.range n, C_step / (L : ℝ) ^ 20 :=
      Finset.sum_le_sum fun t ht ↦ hstep t (Finset.mem_range.mp ht)
    _ = n * (C_step / (L : ℝ) ^ 20) := by simp
    _ ≤ C_ch * (L : ℝ) ^ 3 * (C_step / (L : ℝ) ^ 20) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = C_ch * C_step / (L : ℝ) ^ 17 := by
      field_simp

end Trajectory

section Density

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
  {E : ℕ → Type*} [∀ t, SeminormedAddCommGroup (E t)] [∀ t, Module ℂ (E t)]

/-- For `L ≥ 1` and `c ≥ 0`, the bound `c / L ^ j` decreases in `j`. -/
private theorem div_pow_le_div_pow {c : ℝ} (hc : 0 ≤ c) {L : ℕ} (hL : 1 ≤ L) {i j : ℕ}
    (hij : i ≤ j) : c / (L : ℝ) ^ j ≤ c / (L : ℝ) ^ i := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact div_le_div_of_nonneg_left hc (by positivity) (pow_le_pow_right₀ hL' hij)

/-- **The protocol density estimate.** Let the reference trajectory start at a vector of norm
at most one and end, read in physical and private coordinates through the isometry `K`, at
`Ω ⊗ Ξ` with `‖Ω‖ = 1` and `1 - C_hole L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`. If at most `C_ch L³` contractions each
take their reference vector within `C_step L⁻²⁰` of the next one, then the actual final vector
`Ψ` has norm at most one, lies within `C_ch C_step L⁻¹⁷` of `Ω ⊗ Ξ`, and its physical density
satisfies `‖Tr_private |Ψ⟩⟨Ψ| - |Ω⟩⟨Ω|‖₁ ≤ (2 C_ch C_step + 2 C_hole) L⁻¹⁰`. No
renormalization occurs, and `Ξ` may vanish.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `eq:reference-junk` and
`eq:protocol-density`, `07-assembly.tex:18–51`. -/
theorem rectangularTraceNorm_protocol_density_sub_le (S : (t : ℕ) → E t →ₗ[ℂ] E (t + 1))
    (x r : (t : ℕ) → E t) {n L : ℕ} (hL : 1 ≤ L) {C_ch C_step C_hole : ℝ}
    (hC_step : 0 ≤ C_step) (hC_hole : 0 ≤ C_hole) (hn : (n : ℝ) ≤ C_ch * (L : ℝ) ^ 3)
    (hS : ∀ t < n, ∀ v, ‖S t v‖ ≤ ‖v‖) (hr₀ : ‖r 0‖ ≤ 1)
    (hx₀ : x 0 = r 0) (hx : ∀ t < n, x (t + 1) = S t (x t))
    (hstep : ∀ t < n, ‖S t (r t) - r (t + 1)‖ ≤ C_step / (L : ℝ) ^ 20)
    (K : E n →ₗᵢ[ℂ] EuclideanSpace ℂ (a × b)) (Ω : EuclideanSpace ℂ a)
    (Ξ : EuclideanSpace ℂ b) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1)
    (hlower : 1 - C_hole / (L : ℝ) ^ 57 ≤ ‖Ξ‖)
    (href : K (r n) = Matrix.euclideanTensorVector Ω Ξ) :
    ‖K (x n)‖ ≤ 1 ∧
      ‖K (x n) - Matrix.euclideanTensorVector Ω Ξ‖ ≤ C_ch * C_step / (L : ℝ) ^ 17 ∧
      Matrix.rectangularTraceNorm
        (Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (x n)) (K (x n))) -
          Matrix.euclideanOuterProduct Ω Ω) ≤
        (2 * (C_ch * C_step) + 2 * C_hole) / (L : ℝ) ^ 10 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hC_ch : 0 ≤ C_ch := by
    have h0 : (0 : ℝ) ≤ C_ch * (L : ℝ) ^ 3 := (Nat.cast_nonneg n).trans hn
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have hΨ : ‖K (x n)‖ ≤ 1 := by
    rw [K.norm_map]
    exact (norm_trajectory_le S x n hS hx).trans (hx₀ ▸ hr₀)
  have herror : ‖K (x n) - Matrix.euclideanTensorVector Ω Ξ‖ ≤
      C_ch * C_step / (L : ℝ) ^ 17 := by
    rw [← href, ← map_sub, K.norm_map]
    exact norm_protocol_sub_reference_le S x r hL hC_step hn hS hx₀ hx hstep
  refine ⟨hΨ, herror, ?_⟩
  have hdensity :=
    Matrix.rectangularTraceNorm_partialTraceRight_sub_product_reference_le_of_norm_sub_le
      (K (x n)) Ω Ξ hΨ hΩ hΞ herror hlower
  have h17 := div_pow_le_div_pow (mul_nonneg hC_ch hC_step) hL (by norm_num : 10 ≤ 17)
  have h57 := div_pow_le_div_pow hC_hole hL (by norm_num : 10 ≤ 57)
  calc
    _ ≤ 2 * (C_ch * C_step / (L : ℝ) ^ 17) + 2 * (C_hole / (L : ℝ) ^ 57) := hdensity
    _ ≤ 2 * (C_ch * C_step / (L : ℝ) ^ 10) + 2 * (C_hole / (L : ℝ) ^ 10) := by gcongr
    _ = (2 * (C_ch * C_step) + 2 * C_hole) / (L : ℝ) ^ 10 := by ring

omit [DecidableEq a] in
/-- The actual final protocol vector retains norm close to one, and its unnormalized
physical density retains trace close to one. Both losses are bounded by the reference
norm loss and the accumulated vector error, without a small-error hypothesis.

The reference trajectory, contractions and step bounds are supplied; this result does
not construct the distributed protocol. Source: Polynomial-PEPS manuscript (Sept 24
2026), §8.1, `eq:reference-junk` and the paragraph following `eq:protocol-density`,
`07-assembly.tex:18–51`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. This is an original consequence of the
product-reference estimates; no OpenAI Lean code is copied or adapted. -/
theorem protocol_norm_and_trace_deficit_le (S : (t : ℕ) → E t →ₗ[ℂ] E (t + 1))
    (x r : (t : ℕ) → E t) {n L : ℕ} (hL : 1 ≤ L) {C_ch C_step C_hole : ℝ}
    (hC_step : 0 ≤ C_step) (hC_hole : 0 ≤ C_hole) (hn : (n : ℝ) ≤ C_ch * (L : ℝ) ^ 3)
    (hS : ∀ t < n, ∀ v, ‖S t v‖ ≤ ‖v‖) (hr₀ : ‖r 0‖ ≤ 1)
    (hx₀ : x 0 = r 0) (hx : ∀ t < n, x (t + 1) = S t (x t))
    (hstep : ∀ t < n, ‖S t (r t) - r (t + 1)‖ ≤ C_step / (L : ℝ) ^ 20)
    (K : E n →ₗᵢ[ℂ] EuclideanSpace ℂ (a × b)) (Ω : EuclideanSpace ℂ a)
    (Ξ : EuclideanSpace ℂ b) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1)
    (hlower : 1 - C_hole / (L : ℝ) ^ 57 ≤ ‖Ξ‖)
    (href : K (r n) = Matrix.euclideanTensorVector Ω Ξ) :
    1 - C_hole / (L : ℝ) ^ 57 - C_ch * C_step / (L : ℝ) ^ 17 ≤ ‖K (x n)‖ ∧
      1 - (Matrix.partialTraceRight
        (Matrix.euclideanOuterProduct (K (x n)) (K (x n)))).trace.re ≤
        2 * (C_hole / (L : ℝ) ^ 57 + C_ch * C_step / (L : ℝ) ^ 17) := by
  classical
  obtain ⟨-, herror, -⟩ := rectangularTraceNorm_protocol_density_sub_le S x r hL hC_step
    hC_hole hn hS hr₀ hx₀ hx hstep K Ω Ξ hΩ hΞ hlower href
  exact ⟨Matrix.one_sub_le_norm_of_product_reference (K (x n)) Ω Ξ hΩ herror hlower,
    Matrix.trace_deficit_partialTraceRight_le_of_product_reference
      (K (x n)) Ω Ξ hΩ herror hlower⟩

/-- **The compressed density estimate.** Under the hypotheses of
`rectangularTraceNorm_protocol_density_sub_le`, every operator `σ` within `C_comp L⁻⁵` of the
actual physical density `Tr_private |Ψ⟩⟨Ψ|`, as produced by the compression theorem with
accuracy `L⁻⁵`, satisfies `‖σ - |Ω⟩⟨Ω|‖₁ ≤ (C_comp + 2 C_ch C_step + 2 C_hole) L⁻⁵`. The
operator `σ` need not be positive or Hermitian.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `eq:protocol-density` and
`eq:compressed-density`, `07-assembly.tex:18–63`. -/
theorem rectangularTraceNorm_compressed_density_sub_le
    (S : (t : ℕ) → E t →ₗ[ℂ] E (t + 1))
    (x r : (t : ℕ) → E t) {n L : ℕ} (hL : 1 ≤ L) {C_ch C_step C_hole C_comp : ℝ}
    (hC_step : 0 ≤ C_step) (hC_hole : 0 ≤ C_hole) (hn : (n : ℝ) ≤ C_ch * (L : ℝ) ^ 3)
    (hS : ∀ t < n, ∀ v, ‖S t v‖ ≤ ‖v‖) (hr₀ : ‖r 0‖ ≤ 1)
    (hx₀ : x 0 = r 0) (hx : ∀ t < n, x (t + 1) = S t (x t))
    (hstep : ∀ t < n, ‖S t (r t) - r (t + 1)‖ ≤ C_step / (L : ℝ) ^ 20)
    (K : E n →ₗᵢ[ℂ] EuclideanSpace ℂ (a × b)) (Ω : EuclideanSpace ℂ a)
    (Ξ : EuclideanSpace ℂ b) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1)
    (hlower : 1 - C_hole / (L : ℝ) ^ 57 ≤ ‖Ξ‖)
    (href : K (r n) = Matrix.euclideanTensorVector Ω Ξ) (σ : Matrix a a ℂ)
    (hσ : Matrix.rectangularTraceNorm
      (σ - Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (x n)) (K (x n)))) ≤
        C_comp / (L : ℝ) ^ 5) :
    Matrix.rectangularTraceNorm (σ - Matrix.euclideanOuterProduct Ω Ω) ≤
      (C_comp + 2 * (C_ch * C_step) + 2 * C_hole) / (L : ℝ) ^ 5 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨-, -, hdensity⟩ := rectangularTraceNorm_protocol_density_sub_le S x r hL hC_step
    hC_hole hn hS hr₀ hx₀ hx hstep K Ω Ξ hΩ hΞ hlower href
  have hC_ch : 0 ≤ C_ch := by
    have h0 : (0 : ℝ) ≤ C_ch * (L : ℝ) ^ 3 := (Nat.cast_nonneg n).trans hn
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have h10 := div_pow_le_div_pow
    (by positivity : 0 ≤ 2 * (C_ch * C_step) + 2 * C_hole) hL (by norm_num : 5 ≤ 10)
  calc
    _ = Matrix.rectangularTraceNorm
        ((σ - Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (x n)) (K (x n)))) +
          (Matrix.partialTraceRight (Matrix.euclideanOuterProduct (K (x n)) (K (x n))) -
            Matrix.euclideanOuterProduct Ω Ω)) := by rw [sub_add_sub_cancel]
    _ ≤ _ := Matrix.rectangularTraceNorm_add_le _ _
    _ ≤ C_comp / (L : ℝ) ^ 5 + (2 * (C_ch * C_step) + 2 * C_hole) / (L : ℝ) ^ 5 :=
      add_le_add hσ (hdensity.trans h10)
    _ = _ := by ring

end Density

end TNLean.Lattice.PartyCircuit
