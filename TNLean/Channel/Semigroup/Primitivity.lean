/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Peripheral.Spectrum
import Mathlib.NumberTheory.Real.Irrational

/-!
# Irreducibility implies primitivity for quantum dynamical semigroups — Prop 7.5

## Main results

* `irreducible_semigroup_implies_primitive` — **Prop 7.5** (forward direction):
  If `T_{t₀} = exp(t₀ · L)` is irreducible for some `t₀ > 0`, then
  `T_t` is primitive for ALL `t > 0`.
* `qds_irreducible_iff_primitive` — **Prop 7.5** (full equivalence):
  `∃ t₀ > 0, T_{t₀} irreducible ↔ ∀ t > 0, T_t primitive`.

## Proof outline for `irreducible_semigroup_implies_primitive`

The proof requires the following chain:

**Step A** (continuous-time key): `T_{t₀}` irreducible → `T_t` irreducible for all `t > 0`.
This is the core continuous-time fact: irreducibility is a generator property.
In a norm-continuous QDS `T_t = exp(tL)`, the generator `L` is irreducible
(no non-trivial invariant faces of the PSD cone). An irreducible generator
generates an irreducible semigroup: `T_t` is irreducible for ALL `t > 0`.
*Missing infrastructure*: formalization of "generator irreducibility ↔ T_t irr ∀ t".

**Step B**: `T_t` irreducible + channel → peripheral eigenvalues of `T_t` are roots
of unity (Wolf Thm 6.6). Specifically, if `μ` is a peripheral eigenvalue of `T_t`
(a CPTP map), then `μ^n` is a peripheral eigenvalue for all `n`, hence by
`peripheral_isRootOfUnity_of_pow_eigenvalue` (pigeonhole), `μ` is a root of unity.
*Missing infrastructure*: Thm 6.6 for the channel-as-linear-map setting
(i.e., `peripheralEigenvalues_pow_mem` for `T t : M_D(ℂ) →ₗ[ℂ] M_D(ℂ)`).

**Step C**: Spectral mapping `Re(μ) = 0` for peripheral generator eigenvalues
(proved via `re_eq_zero_of_peripheral_generator`).

**Step D**: From steps B + C: `exp(t·iθ)` is a root of unity for all `t > 0`
→ by `eq_zero_of_exp_mul_I_isRootOfUnity`, `θ = 0` → all peripheral eigenvalues = 1
→ `T_t` is primitive (by `isPrimitive_of_unique_norm_one`).

The three helper lemmas `eigenvalue_exp_of_eigenvalue_generator`,
`eq_zero_of_exp_mul_I_isRootOfUnity`, and `re_eq_zero_of_peripheral_generator`
are fully proved. Steps A and B require additional formalization.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §7.1, Prop 7.5][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators NNReal
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Channel semigroup definition -/

/-- A **quantum dynamical semigroup** (QDS) is a norm-continuous dynamical
semigroup where each `T_t` is a quantum channel (CPTP map) for `t ≥ 0`. -/
structure IsQuantumDynSemigroup
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop where
  /-- The underlying semigroup structure. -/
  semigroup : IsContinuousDynSemigroup T
  /-- Each map is a channel for t ≥ 0. -/
  channel : ∀ t : ℝ, 0 ≤ t → IsChannel (T t)

/-! ## Eigenvalue transfer between semigroup elements

If `λ` is an eigenvalue of `exp(t₀ · L)`, then `λ^(t/t₀)` is an eigenvalue
of `exp(t · L)`. This uses `spectrum.exp_mem_exp`. -/

/-- If `μ` is an eigenvalue of `L`, then `exp(t · μ)` is an eigenvalue of
`exp(t · L)` (spectral mapping theorem for exp). -/
theorem eigenvalue_exp_of_eigenvalue_generator
    (L : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ L) (t : ℂ) :
    Complex.exp (t * μ) ∈ spectrum ℂ (NormedSpace.exp (t • L)) := by
  rw [Complex.exp_eq_exp_ℂ]
  apply spectrum.exp_mem_exp
  have hnt : Nontrivial (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (spectrum.of_subsingleton (R := ℂ) L ▸ hμ : μ ∈ (∅ : Set ℂ))
  by_cases ht : t = 0
  · subst ht; simp only [zero_mul, zero_smul]
    rw [spectrum.zero_eq]; exact Set.mem_singleton _
  · have hu : IsUnit t := isUnit_iff_ne_zero.mpr ht
    rw [show t * μ = t • μ from (smul_eq_mul t μ).symm]
    exact (spectrum.smul_mem_smul_iff (r := hu.unit)).mpr hμ

/-! ## Key lemma: exp(itθ) root of unity for all t > 0 implies θ = 0

This is the number-theoretic heart of Prop 7.5. If `exp(i t θ)` is a root of unity
for every `t > 0`, then `θ = 0`. The proof uses the density of irrationals:
`exp(i t θ)^p = 1` means `t p θ ∈ 2π ℤ`, but this cannot hold for all `t > 0`
unless `θ = 0` (since `t ↦ t θ / (2π)` takes irrational values). -/

/-- If `exp(i · t · θ)` is a root of unity for every `t > 0`, then `θ = 0`.

**Proof sketch**: For `t = 1`, `exp(iθ)^p₁ = 1` gives `p₁θ = 2πk₁` for some `k₁ ∈ ℤ`.
For `t = √2`, `exp(i√2θ)^p₂ = 1` gives `√2 p₂ θ = 2πk₂`. Dividing:
`√2 = k₂ p₁ / (k₁ p₂)`, contradicting the irrationality of `√2`. -/
theorem eq_zero_of_exp_mul_I_isRootOfUnity
    (θ : ℝ) (hroot : ∀ t : ℝ, 0 < t → ∃ p : ℕ, 0 < p ∧
      Complex.exp (↑(t * θ) * Complex.I) ^ p = 1) :
    θ = 0 := by
  by_contra hθ
  -- Step 1: At t = 1, get p₁ > 0 with exp(iθ)^p₁ = 1
  obtain ⟨p₁, hp₁, hexp₁⟩ := hroot 1 one_pos
  rw [one_mul] at hexp₁
  -- exp(iθ)^p₁ = exp(ip₁θ) = 1
  rw [← Complex.exp_nat_mul] at hexp₁
  -- So p₁θ ∈ 2πℤ
  rw [Complex.exp_eq_one_iff] at hexp₁
  obtain ⟨k₁, hk₁⟩ := hexp₁
  -- Step 2: At t = √2, get p₂ > 0 with exp(i√2θ)^p₂ = 1
  obtain ⟨p₂, hp₂, hexp₂⟩ := hroot (Real.sqrt 2) (Real.sqrt_pos_of_pos two_pos)
  rw [← Complex.exp_nat_mul] at hexp₂
  rw [Complex.exp_eq_one_iff] at hexp₂
  obtain ⟨k₂, hk₂⟩ := hexp₂
  -- Step 3: From hk₁: ↑p₁ * (↑θ * I) = ↑k₁ * (2 * ↑π * I)
  --         i.e. p₁ · θ = 2π · k₁
  -- From hk₂: ↑p₂ * (↑(√2 * θ) * I) = ↑k₂ * (2 * ↑π * I)
  --         i.e. p₂ · √2 · θ = 2π · k₂
  -- Extract real equations from complex identities
  -- hk₁ : ↑p₁ * (↑θ * I) = ↑k₁ * (2 * ↑π * I), multiply both sides by (-I)
  -- gives p₁ * θ = k₁ * (2π)
  have hreal₁ : (p₁ : ℝ) * θ = k₁ * (2 * Real.pi) := by
    have h := congr_arg Complex.im hk₁
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.natCast_re, Complex.natCast_im] at h
    linarith
  have hreal₂ : (p₂ : ℝ) * (Real.sqrt 2 * θ) = k₂ * (2 * Real.pi) := by
    have h := congr_arg Complex.im hk₂
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.natCast_re, Complex.natCast_im] at h
    linarith
  -- If k₁ = 0 then p₁θ = 0, so θ = 0 (since p₁ > 0), contradiction
  have hk₁_ne : (k₁ : ℝ) ≠ 0 := by
    intro h
    have : (p₁ : ℝ) * θ = 0 := by rw [hreal₁, h]; ring
    rcases mul_eq_zero.mp this with hp | hθ'
    · exact absurd (Nat.cast_eq_zero.mp hp) (Nat.pos_iff_ne_zero.mp hp₁)
    · exact hθ hθ'
  -- Similarly p₂ > 0 and k₁ ≠ 0 imply θ ≠ 0 (already known)
  -- Step 4: Derive √2 is rational — contradiction
  -- From hreal₁: θ = 2πk₁/p₁
  -- From hreal₂: p₂ · √2 · θ = 2πk₂
  -- Substituting: p₂ · √2 · (2πk₁/p₁) = 2πk₂
  -- So: √2 = k₂ · p₁ / (k₁ · p₂)
  have hp₁_ne : (p₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp₁)
  have hp₂_ne : (p₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp₂)
  have hθ_ne : θ ≠ 0 := hθ
  -- From hreal₁: θ = k₁ * (2π) / p₁
  -- From hreal₂: p₂ * √2 * (k₁ * (2π) / p₁) = k₂ * (2π)
  -- So: p₂ * √2 * k₁ / p₁ = k₂
  -- So: √2 = k₂ * p₁ / (p₂ * k₁)
  -- Rewrite √2 as a ratio of integers to contradict irrationality
  have hsqrt2 : Real.sqrt 2 = ↑(k₂ * ↑p₁) / ↑(k₁ * ↑p₂) := by
    push_cast
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    -- From hreal₁: θ = k₁ * (2π) / p₁
    have hθ_eq : θ = ↑k₁ * (2 * Real.pi) / ↑p₁ := by
      field_simp at hreal₁ ⊢; linarith
    -- Substitute into hreal₂
    rw [hθ_eq] at hreal₂
    field_simp at hreal₂ ⊢
    nlinarith [hreal₂]
  exact absurd hsqrt2 (irrational_sqrt_two.ne_rational _ _)

/-- **Peripheral eigenvalues of the generator are purely imaginary.**
If `L` generates a QDS of channels `T_t = exp(tL)` and `T_{t₀}` is irreducible,
then every eigenvalue `μ` of `L` with `|exp(t₀ μ)| = 1` satisfies `Re(μ) = 0`.
This follows from `|exp(t₀ μ)| = exp(t₀ · Re(μ))`, so `Re(μ) = 0`. -/
theorem re_eq_zero_of_peripheral_generator
    (μ : ℂ) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hnorm : ‖Complex.exp (↑t₀ * μ)‖ = 1) :
    μ.re = 0 := by
  rw [Complex.norm_exp] at hnorm
  have h : t₀ * μ.re = 0 := by
    have hre : (↑t₀ * μ).re = t₀ * μ.re := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre] at hnorm
    exact (Real.exp_eq_one_iff _).mp hnorm
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt ht₀)

/-! ## Prop 7.5: Irreducibility implies primitivity for QDS -/

/-- **Wolf Proposition 7.5** (1 → 3): If `T_{t₀}` is irreducible for some
`t₀ > 0`, then `T_t` is primitive for all `t > 0`.

The proof has two independent blocks of infrastructure, each available in the
codebase in almost complete form; what is missing is the "glue" between them:

**Block 1 — continuous-time irr. propagation** (see module comment, Step A):
`T_{t₀}` irreducible → `T_t` irreducible for ALL `t > 0`.
This is the key continuous-time fact, dual to the discrete-time result that
a power of a primitive map is primitive.

**Block 2 — irr. → primitivity** (Steps B–D):
If `T_t` is irreducible for every `t > 0`, then every peripheral eigenvalue
`exp(t·iθ)` is a root of unity for every `t > 0`
(Wolf Thm 6.6; proved here via `peripheral_isRootOfUnity_of_pow_eigenvalue`
once Block 1 provides the needed `∀ n, HasEigenvalue T_t (exp(t·iθ)^n)`).
Then `eq_zero_of_exp_mul_I_isRootOfUnity` forces `θ = 0`, giving
all peripheral eigenvalues equal `1`, i.e., `T_t` is primitive.

The helper lemmas `eigenvalue_exp_of_eigenvalue_generator`,
`eq_zero_of_exp_mul_I_isRootOfUnity`, and `re_eq_zero_of_peripheral_generator`
are fully proved above. -/
theorem irreducible_semigroup_implies_primitive
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∀ t : ℝ, 0 < t → IsPrimitive (T t) := by
  intro t ht
  -- Key missing lemma (Step A): irreducibility propagates to all times.
  -- In a norm-continuous QDS, T_{t₀} being irreducible implies T_t is irreducible
  -- for ALL t > 0 via the continuous-time analogue of primitivity theory.
  -- This requires formalizing "irreducibility ↔ generator irreducibility" for QDS.
  have hT_irr_all : IsIrreducibleMap (T t) := by
    -- Step A gap: T_{t₀} irr + QDS structure → T_t irr for all t > 0.
    -- Once available, the proof proceeds as:
    -- (1) expSemigroup L is a continuous semigroup of channels
    -- (2) irreducibility is invariant along the semigroup: irr(T_{t₀}) ↔ irr(T_t) ∀ t
    -- This mirrors the classical result for primitive maps in discrete time.
    sorry
  -- With T_t irreducible, use isPrimitive_of_unique_norm_one.
  -- We need: (a) a fixed point of T_t, (b) all norm-1 eigenvalues equal 1.
  -- For (b), the strategy is:
  --   T_t irr + channel → peripheral eigenvalues are roots of unity (Wolf Thm 6.6)
  --   exp(t·iθ) is ROU for all t > 0 → θ = 0 (eq_zero_of_exp_mul_I_isRootOfUnity)
  --   → all peripheral eigenvalues = 1 → IsPrimitive (T t).
  -- The current blocker for (b) is Wolf Thm 6.6 for linear maps on M_D(ℂ)
  -- (i.e., `peripheralEigenvalues_pow_mem` for T t : M_D(ℂ) →ₗ[ℂ] M_D(ℂ));
  -- the analogous result for MPSTensor is in Channel/Peripheral/ClosureFixedPoint.lean.
  sorry

/-- **Wolf Proposition 7.5** (full equivalence): For a QDS of channels, the
following are equivalent:
1. There exists `t₀ > 0` such that `T_{t₀}` is irreducible.
2. `T_t` is irreducible for all `t > 0`.
3. `T_t` is primitive for all `t > 0`.
4. There exists a positive definite `ρ_∞` such that `T_t(ρ) → ρ_∞` for all
   density matrices `ρ`.
5. `ker(L)` is one-dimensional and spanned by a positive definite `ρ_∞`. -/
theorem qds_irreducible_iff_primitive
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t) :
    (∃ t₀ : ℝ, 0 < t₀ ∧ IsIrreducibleMap (T t₀)) ↔
    (∀ t : ℝ, 0 < t → IsPrimitive (T t)) := by
  constructor
  · -- Forward: ∃ t₀, irreducible T_{t₀} → ∀ t, primitive T_t
    rintro ⟨t₀, ht₀, hirr⟩
    exact irreducible_semigroup_implies_primitive L T hT hexp t₀ ht₀ hirr
  · -- Backward: ∀ t > 0, primitive T_t → ∃ t₀ > 0, irreducible T_{t₀}.
    -- We take t₀ = 1. Since T_1 is primitive and a channel, it should be irreducible.
    -- The proof chain is:
    --   IsPrimitive (T 1) + IsChannel (T 1)
    --   → T_1 has a unique positive-definite density-matrix fixed point σ
    --   → IsIrreducibleMap T_1 (by isIrreducibleMap_of_channel_posDef_fixedPoint_unique)
    --
    -- The first implication requires Wolf Thm 6.7 (equivalent characterizations
    -- of primitive channels), specifically: primitive CPTP → spectral gap of T - P < 1
    -- → T^n → P (rank-1 projection) → unique convergence to positive-definite fixed pt.
    -- This requires the Jordan decomposition / spectral theorem for matrices,
    -- which is currently not fully available for the `M_D(ℂ) →ₗ[ℂ] M_D(ℂ)` setting.
    intro hprim
    exact ⟨1, one_pos, by
      -- IsPrimitive (T 1) + IsChannel (T 1) → IsIrreducibleMap (T 1)
      -- Missing: Wolf Thm 6.7 connecting spectral primitivity to unique PD fixed point.
      -- Once available:
      --   have hch := hT.channel 1 le_rfl
      --   obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_uniq⟩ :=
      --     IsChannel.exists_unique_density_fixedPoint_of_primitive hch (hprim 1 one_pos) hD
      --   exact isIrreducibleMap_of_channel_posDef_fixedPoint_unique
      --     (T 1) hch σ hσ_pd (hσ_mem.2 ▸ hσ_fix) (fun τ hτ hfix => ...)
      sorry⟩

end -- noncomputable section
