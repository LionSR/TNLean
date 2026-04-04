/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic
import TNLean.Channel.Semigroup.Kernel
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Irreducible.FromSpectral
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.IrreducibleChannel
import TNLean.Channel.Peripheral.PeriodicityRemoval
import TNLean.Channel.Peripheral.ClosureFixedPoint
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.Channel.Primitive
import TNLean.MPS.Irreducible.Adjoint
import TNLean.Spectral.SpectralGap
import Mathlib.Analysis.Calculus.Deriv.Mul
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
of unity (Wolf Thm 6.6). This channel-level bridge is now available as
`peripheral_isRootOfUnity_of_irreducible_channel`, proved by choosing a Kraus
representation, converting to an irreducible tensor, and applying the existing
blocking-periodicity theorem.

**Step C**: For an irreducible channel `T_t` with period `p` (i.e., `μ^p = 1` for
peripheral `μ`), the eigenvector `V` with `T_t V = μ V` satisfies
`T_{pt} V = V`.  Since `T_{pt}` is also irreducible, its fixed-point space
is one-dimensional.  Thus `V = c · σ'` (the unique faithful density fixed point),
and `T_t σ' = μ σ'`.  Trace preservation forces `μ = 1`.

The helper lemmas `eigenvalue_exp_of_eigenvalue_generator`,
`eq_zero_of_exp_mul_I_isRootOfUnity`, and `re_eq_zero_of_peripheral_generator`
are fully proved. Step A (generator irreducibility ↔ semigroup irreducibility)
is formalized via `irreducible_all_of_irreducible_time` in
`IrreducibleAnalysis.lean`, but that theorem transitively depends on 13
`sorry` placeholders (formerly `axiom` declarations).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §7.1, Prop 7.5][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

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

set_option maxHeartbeats 5000000 in
-- The spectral-mapping step uses `spectrum.exp_mem_exp` on a large CLM expression.
/-- If `μ` is an eigenvalue of `L`, then `exp(t · μ)` is an eigenvalue of
`exp(t · L)` (spectral mapping theorem for exp). -/
theorem eigenvalue_exp_of_eigenvalue_generator
    (L : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ L) (t : ℂ) :
    Complex.exp (t * μ) ∈ spectrum ℂ (NormedSpace.exp (t • L)) := by
  let hFinite :
      FiniteDimensional ℂ (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) :=
    (endEquiv (D := D)).toLinearEquiv.finiteDimensional
  let hComplete :
      CompleteSpace (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) := by
    letI : FiniteDimensional ℂ
        (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) := hFinite
    exact FiniteDimensional.complete ℂ
      (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
  have hnt : Nontrivial (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (spectrum.of_subsingleton (R := ℂ) L ▸ hμ : μ ∈ (∅ : Set ℂ))
  have htmul : t * μ ∈ spectrum ℂ (t • L) := by
    by_cases ht : t = 0
    · subst ht
      have hzero : (0 : ℂ) ∈ spectrum ℂ
          (0 : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) := by
        rw [spectrum.zero_eq]
        exact Set.mem_singleton _
      have hmul : (0 : ℂ) * μ = 0 := by simp
      have hzsmul : (0 : ℂ) • L = 0 := zero_smul ℂ L
      rw [hmul, hzsmul]
      exact hzero
    · have hu : IsUnit t := isUnit_iff_ne_zero.mpr ht
      simpa [smul_eq_mul] using
        (spectrum.smul_mem_smul_iff (a := L) (r := hu.unit)).mpr hμ
  simpa [Complex.exp_eq_exp_ℂ] using
    (@spectrum.exp_mem_exp ℂ
      (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
      inferInstance inferInstance inferInstance hComplete (t • L) (z := t * μ) htmul)

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

end -- noncomputable section
