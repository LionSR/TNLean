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
are fully proved. Step A still requires additional formalization.

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
/-- If `μ` is an eigenvalue of `L`, then `exp(t · μ)` is an eigenvalue of
`exp(t · L)` (spectral mapping theorem for exp). -/
theorem eigenvalue_exp_of_eigenvalue_generator
    (L : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ L) (t : ℂ) :
    Complex.exp (t * μ) ∈ spectrum ℂ (NormedSpace.exp (t • L)) := by
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
      rw [show t * μ = t • μ from (smul_eq_mul t μ).symm]
      exact (spectrum.smul_mem_smul_iff (a := L) (r := hu.unit)).mpr hμ
  simpa [Complex.exp_eq_exp_ℂ] using (spectrum.exp_mem_exp (a := t • L) htmul)

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

/-! ## Helper lemmas for the primitivity proof -/

/-- Semigroup iteration: `T (n * t) = (T t) ^ n` for nonneg `t`. -/
private theorem semigroup_pow
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hS : IsDynSemigroup T) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    T (↑n * t) = (T t) ^ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    change T 0 = LinearMap.id
    exact hS.zero
  | succ n ih =>
    have hnt : 0 ≤ (↑n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
    have hcast : (↑(n + 1) : ℝ) * t = ↑n * t + t := by push_cast; ring
    have hcomp := hS.comp (↑n * t) t hnt ht
    rw [hcast, hcomp, ih]
    exact (pow_succ (T t) n).symm

/-- Eigenvector equation for powers of a linear map: if `f v = μ • v` then
`(f ^ n) v = μ ^ n • v`. -/
private theorem pow_apply_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (v : V) (μ : ℂ) (n : ℕ) (hv : f v = μ • v) :
    (f ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp [pow_zero]
  | succ n ih =>
    have hstep : (f ^ (n + 1)) v = (f ^ n) (f v) := by
      change (f ^ n * f) v = (f ^ n) (f v)
      rfl
    rw [hstep, hv, map_smul, ih, smul_smul, pow_succ']

/-- A density matrix is nonzero. -/
private lemma ne_zero_of_mem_densityMatrices' {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ ∈ densityMatrices D) : ρ ≠ 0 := by
  intro h; subst h
  simp [mem_densityMatrices, Matrix.trace_zero (Fin D) ℂ] at hρ

/-- If a compression is preserved by a linear map, then it is preserved by every power. -/
private theorem compression_preserved_by_pow
    (E : Mat →ₗ[ℂ] Mat) (P : Mat) (hP : IsOrthogonalProjection P)
    (hInv : ∀ X : Mat, P * E (P * X * P) * P = E (P * X * P)) :
    ∀ n : ℕ, ∀ X : Mat, P * (E ^ n) (P * X * P) * P = (E ^ n) (P * X * P) := by
  intro n
  induction n with
  | zero =>
      intro X
      rw [pow_zero]
      calc
        P * (P * X * P) * P = ((P * P) * X) * (P * P) := by
          simp [Matrix.mul_assoc]
        _ = P * X * P := by
          simp [Matrix.mul_assoc, hP.2]
  | succ n ih =>
      intro X
      rw [pow_succ']
      change P * E ((E ^ n) (P * X * P)) * P = E ((E ^ n) (P * X * P))
      rw [← ih X]
      exact hInv ((E ^ n) (P * X * P))

private abbrev endCLMEquiv' :
    (Mat →ₗ[ℂ] Mat) ≃ₐ[ℂ] (Mat →L[ℂ] Mat) :=
  Module.End.toContinuousLinearMap Mat

private theorem expSemigroup_toCLM''
    (L : Mat →ₗ[ℂ] Mat) (t : ℝ) :
    endCLMEquiv' (expSemigroup L t) = expSemigroupCLM (endCLMEquiv' L) t := by
  simp [expSemigroup, endCLMEquiv']

private abbrev applyCLMReal' :
    (Mat →L[ℂ] Mat) →L[ℝ] Mat →L[ℝ] Mat :=
  (ContinuousLinearMap.flip
      (ContinuousLinearMap.apply ℂ Mat :
        Mat →L[ℂ] (Mat →L[ℂ] Mat) →L[ℂ] Mat)).bilinearRestrictScalars ℝ

set_option maxHeartbeats 1000000 in
private theorem hasDerivAt_expSemigroup_apply'
    (L : Mat →ₗ[ℂ] Mat) (X : Mat) (t : ℝ) :
    HasDerivAt (fun u : ℝ => expSemigroup L u X) (expSemigroup L t (L X)) t := by
  have hCLM :
      HasDerivAt
        (fun u : ℝ => expSemigroupCLM (endCLMEquiv' L) u)
        (expSemigroupCLM (endCLMEquiv' L) t * endCLMEquiv' L) t :=
    hasDerivAt_expSemigroupCLM (endCLMEquiv' L) t
  have hApply :
      HasDerivAt
        (fun u : ℝ => applyCLMReal' (D := D) (expSemigroupCLM (endCLMEquiv' L) u) X)
        (applyCLMReal' (D := D) (expSemigroupCLM (endCLMEquiv' L) t) 0 +
          applyCLMReal' (D := D)
            (expSemigroupCLM (endCLMEquiv' L) t * endCLMEquiv' L) X)
        t := by
    simpa using
      (ContinuousLinearMap.hasDerivAt_of_bilinear
        (B := applyCLMReal' (D := D))
        (u := fun u : ℝ => expSemigroupCLM (endCLMEquiv' L) u)
        (v := fun _ : ℝ => X)
        (u' := expSemigroupCLM (endCLMEquiv' L) t * endCLMEquiv' L)
        (v' := 0)
        hCLM (hasDerivAt_const t X))
  simpa [applyCLMReal', expSemigroup_toCLM'',
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply] using hApply

/-- A genuine eigenvector of the generator stays an eigenvector for the whole semigroup. -/
private theorem expSemigroup_apply_eigenvector
    (L : Mat →ₗ[ℂ] Mat) (X : Mat) (μ : ℂ)
    (hX : L X = μ • X) (t : ℝ) :
    expSemigroup L t X = Complex.exp ((t : ℂ) * μ) • X := by
  let c : ℝ → ℂ := fun u => Complex.exp (-((u : ℂ) * μ))
  let g : ℝ → Mat := fun u => expSemigroup L u X
  let f : ℝ → Mat := fun u => c u • g u
  have hdiff : Differentiable ℝ f := by
    intro u
    have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * μ) ((1 : ℂ) * μ) u :=
      (Complex.ofRealCLM.hasDerivAt.mul_const μ)
    have hc : HasDerivAt c (-(c u * μ)) u := by
      dsimp [c]
      simpa using (Complex.hasDerivAt_exp (-((u : ℂ) * μ))).comp u hmul.neg
    have hg : HasDerivAt g (μ • g u) u := by
      dsimp [g]
      simpa [hX, smul_smul, mul_assoc] using hasDerivAt_expSemigroup_apply' (D := D) L X u
    exact (hc.smul hg).differentiableAt
  have hderiv : ∀ u : ℝ, deriv f u = 0 := by
    intro u
    have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * μ) ((1 : ℂ) * μ) u :=
      (Complex.ofRealCLM.hasDerivAt.mul_const μ)
    have hc : HasDerivAt c (-(c u * μ)) u := by
      dsimp [c]
      simpa using (Complex.hasDerivAt_exp (-((u : ℂ) * μ))).comp u hmul.neg
    have hg : HasDerivAt g (μ • g u) u := by
      dsimp [g]
      simpa [hX, smul_smul, mul_assoc] using hasDerivAt_expSemigroup_apply' (D := D) L X u
    have hf : HasDerivAt f (c u • (μ • g u) + (-(c u * μ)) • g u) u := by
      simpa [f, c, g] using hc.smul hg
    have hz : c u • (μ • g u) + (-(c u * μ)) • g u = 0 := by
      have : ((c u * μ) + (-(c u * μ))) • g u = 0 := by
        simp
      simpa [smul_smul, add_smul, mul_assoc] using this
    rw [hf.deriv, hz]
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv 0 t
  have hft0 : f 0 = X := by
    simp [f, c, g, expSemigroup_zero]
  have hfteq : f t = X := by
    calc
      f t = f 0 := by simpa using hconst.symm
      _ = X := hft0
  have hct_ne : c t ≠ 0 := by
    dsimp [c]
    exact Complex.exp_ne_zero _
  have hmain : c t • expSemigroup L t X = c t • (Complex.exp ((t : ℂ) * μ) • X) := by
    calc
      c t • expSemigroup L t X = f t := by simp [f, g]
      _ = X := hfteq
      _ = c t • (Complex.exp ((t : ℂ) * μ) • X) := by
        dsimp [c]
        rw [smul_smul]
        have : Complex.exp (-((t : ℂ) * μ)) * Complex.exp ((t : ℂ) * μ) = 1 := by
          rw [← Complex.exp_add]
          simp
        rw [this, one_smul]
  have hcancel := congrArg ((c t)⁻¹ • ·) hmain
  simpa [c, smul_smul, inv_mul_cancel₀ hct_ne, one_smul,
    mul_comm, mul_left_comm, mul_assoc] using hcancel

/-- The peripheral spectrum of an irreducible finite-dimensional channel has cardinality at most
`dim(Mat)`.

This is proved by choosing one nonzero eigenvector for each peripheral eigenvalue and using the
linear independence of eigenvectors corresponding to distinct eigenvalues. -/
private theorem peripheral_card_le_finrank [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) :
    (peripheralEigenvalues_finite E).toFinset.card ≤ Module.finrank ℂ Mat := by
  classical
  let hfin := peripheralEigenvalues_finite E
  letI : Fintype ↥(peripheralEigenvalues E) := Set.Finite.fintype hfin
  let xs : ↥(peripheralEigenvalues E) → Mat :=
    fun μ => Classical.choose (μ.2.1.exists_hasEigenvector)
  have hxs : ∀ μ : ↥(peripheralEigenvalues E), Module.End.HasEigenvector E (μ : ℂ) (xs μ) := by
    intro μ
    exact Classical.choose_spec (μ.2.1.exists_hasEigenvector)
  have hlin : LinearIndependent ℂ xs :=
    Module.End.eigenvectors_linearIndependent E (peripheralEigenvalues E) xs hxs
  rw [Set.Finite.card_toFinset hfin]
  simpa using LinearIndependent.fintype_card_le_finrank (R := ℂ) (M := Mat) hlin

/-- If peripheral powers are all again peripheral, then the order of a peripheral eigenvalue is
bounded by the dimension of the matrix space.

This is the finite-dimensional pigeonhole step used to force a common period at a divisor time.
The remaining input needed in the main proof is the closure of peripheral eigenvalues under powers
for the chosen irreducible time slice. -/
private theorem bounded_root_of_peripheral_closed_powers [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) (μ : ℂ) (hμ : μ ∈ peripheralEigenvalues E)
    (hclosed : ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues E) :
    ∃ p : ℕ, 0 < p ∧ p ≤ Module.finrank ℂ Mat ∧ μ ^ p = 1 := by
  classical
  let N := Module.finrank ℂ Mat
  let hfin := peripheralEigenvalues_finite E
  letI : Fintype ↥(peripheralEigenvalues E) := Set.Finite.fintype hfin
  let f : Fin (N + 1) → ↥(peripheralEigenvalues E) :=
    fun n => ⟨μ ^ (n : ℕ), hclosed n⟩
  have hnotinj : ¬ Function.Injective f := by
    intro hf
    have hle1 : Fintype.card (Fin (N + 1)) ≤ Fintype.card ↥(peripheralEigenvalues E) :=
      Fintype.card_le_of_injective f hf
    have hle2 : Fintype.card ↥(peripheralEigenvalues E) ≤ N := by
      simpa [N] using peripheral_card_le_finrank E
    have : N + 1 ≤ N := by
      simpa [Fintype.card_fin] using le_trans hle1 hle2
    omega
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨a, b, hab, hne⟩ := hnotinj
  have hab' : μ ^ (a : ℕ) = μ ^ (b : ℕ) := congrArg Subtype.val hab
  have hab_ne : (a : ℕ) ≠ b := by
    intro h
    apply hne
    exact Fin.ext h
  rcases Nat.lt_or_gt_of_ne hab_ne with hlt | hgt
  · refine ⟨(b : ℕ) - (a : ℕ), Nat.sub_pos_of_lt hlt, ?_, ?_⟩
    · exact Nat.sub_le _ _ |>.trans (Nat.le_of_lt_succ b.2)
    · have hμ_ne : μ ≠ 0 := ne_zero_of_norm_eq_one hμ.2
      exact mul_left_cancel₀ (pow_ne_zero _ hμ_ne) (by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
        exact hab'.symm)
  · refine ⟨(a : ℕ) - (b : ℕ), Nat.sub_pos_of_lt hgt, ?_, ?_⟩
    · exact Nat.sub_le _ _ |>.trans (Nat.le_of_lt_succ a.2)
    · have hμ_ne : μ ≠ 0 := ne_zero_of_norm_eq_one hμ.2
      exact mul_left_cancel₀ (pow_ne_zero _ hμ_ne) (by
        rw [← pow_add, Nat.add_sub_cancel' hgt.le, mul_one]
        exact hab')

/-- Power-closure helper at an irreducible time slice.

This is the only new semigroup-specific ingredient still missing from the refactor below: we need
that after a similarity transform by a positive-definite fixed point, the irreducible channel
becomes unital with an adjoint fixed point, so Wolf's peripheral-power closure theorem applies.

The statement is substantially simpler than the original circular `sorry`: it is a pure channel
lemma, independent of continuous-time propagation or generator kernels. -/
private theorem peripheral_powers_closed_of_irreducible_channel_with_fixed [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) (hE : IsChannel E) (hIrr : IsIrreducibleMap E)
    (σ : Mat) (hσ_pd : σ.PosDef) (hσ_fix : E σ = σ)
    {μ : ℂ} (hμ : μ ∈ peripheralEigenvalues E) :
    ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues E := by
  classical
  -- ── Step 1: Kraus representation ──
  obtain ⟨r, K, hK⟩ := hE.cp
  have hE_eq : E = MPSTensor.transferMap (d := r) (D := D) K :=
    LinearMap.ext fun X => by simpa [MPSTensor.transferMap_apply] using hK X
  have hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1 :=
    kraus_sum_conjTranspose_mul_of_tp K E hK hE.tp
  -- ── Step 2: Square root S = CFC.sqrt σ ──
  let S : Mat := CFC.sqrt σ
  have hS_herm : Sᴴ = S := MPSTensor.conjTranspose_cfc_sqrt (D := D) σ
  have hS_sq : S * S = σ := MPSTensor.cfc_sqrt_mul_self_of_posDef (D := D) σ hσ_pd
  have hS_det : S.det ≠ 0 :=
    (MPSTensor.isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ_pd).ne_zero
  have hSmul : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S (Ne.isUnit hS_det)
  have hSinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S (Ne.isUnit hS_det)
  have hSinv_herm : (S⁻¹)ᴴ = S⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hS_herm]
  -- ── Step 3: Gauged operators L_i = S⁻¹ K_i S ──
  let L : Fin r → Mat := fun i => S⁻¹ * K i * S
  -- ── Step 4: L is unital (∑ L_i L_i† = 1) ──
  have hL_unital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) L := by
    change ∑ i : Fin r, L i * (L i)ᴴ = 1
    exact gauged_unital K S σ hS_det (by rw [hS_herm]; exact hS_sq)
      (by rw [← hE_eq]; exact hσ_fix)
  -- ── Step 5: Kraus.adjointMap L σ = σ ──
  have hL_adj : Kraus.adjointMap L σ = σ := by
    simp only [Kraus.adjointMap_apply, L]
    -- Rewrite conjTranspose of each L_i
    have hconj : ∀ i : Fin r, (S⁻¹ * K i * S)ᴴ = S * (K i)ᴴ * S⁻¹ := by
      intro i
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSinv_herm, hS_herm,
          Matrix.mul_assoc]
    simp_rw [hconj]
    -- S⁻¹ * σ * S⁻¹ = 1
    have hcancel : S⁻¹ * σ * S⁻¹ = 1 := by
      calc S⁻¹ * σ * S⁻¹ = S⁻¹ * (S * S) * S⁻¹ := by rw [hS_sq]
        _ = S⁻¹ * S * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hSinv, hSmul, Matrix.mul_one]
    -- Each term simplifies: S * (K i)ᴴ * S⁻¹ * σ * (S⁻¹ * K i * S)
    -- = S * ((K i)ᴴ * K i) * S
    have h_term_adj : ∀ i : Fin r,
        S * (K i)ᴴ * S⁻¹ * σ * (S⁻¹ * K i * S) = S * ((K i)ᴴ * K i) * S := by
      intro i
      simp only [Matrix.mul_assoc]
      congr 1
      calc (K i)ᴴ * (S⁻¹ * (σ * (S⁻¹ * (K i * S))))
          = (K i)ᴴ * ((S⁻¹ * σ * S⁻¹) * (K i * S)) := by simp only [Matrix.mul_assoc]
        _ = (K i)ᴴ * (1 * (K i * S)) := by rw [hcancel]
        _ = (K i)ᴴ * (K i * S) := by rw [Matrix.one_mul]
    simp_rw [h_term_adj]
    -- ∑ S * ((K i)ᴴ * K i) * S = S * (∑ (K i)ᴴ * K i) * S = σ
    rw [← Finset.sum_mul, ← Finset.mul_sum, hK_tp, Matrix.mul_one, hS_sq]
  -- ── Step 6: transferMap L X = S⁻¹ E(SXS) S⁻¹  (key identity) ──
  have h_term : ∀ (i : Fin r) (X : Mat),
      L i * X * (L i)ᴴ = S⁻¹ * (K i * (S * X * S) * (K i)ᴴ) * S⁻¹ := by
    intro i X
    change (S⁻¹ * K i * S) * X * (S⁻¹ * K i * S)ᴴ =
        S⁻¹ * (K i * (S * X * S) * (K i)ᴴ) * S⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSinv_herm, hS_herm]
    simp only [Matrix.mul_assoc]
  have hL_transfer : ∀ X, MPSTensor.transferMap (d := r) (D := D) L X =
      S⁻¹ * E (S * X * S) * S⁻¹ := by
    intro X
    simp only [MPSTensor.transferMap_apply]
    simp_rw [h_term _ X]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    congr 1; congr 1
    rw [hE_eq, MPSTensor.transferMap_apply]
  -- ── Step 7: transferMap L is irreducible ──
  have hL_irr : IsIrreducibleMap (MPSTensor.transferMap (d := r) (D := D) L) := by
    suffices h : MPSTensor.transferMap (d := r) (D := D) L = similarityMap (D := D) S E by
      rw [h]; exact isIrreducibleMap_similarity (D := D) hS_det hIrr
    apply LinearMap.ext; intro X
    rw [hL_transfer X]
    change S⁻¹ * E (S * X * S) * S⁻¹ = S⁻¹ * E (S * X * Sᴴ) * (Sᴴ)⁻¹
    rw [hS_herm]
  -- Helper: sandwich cancellation lemmas
  have hSandwich : ∀ A : Mat, S * (S⁻¹ * A * S⁻¹) * S = A := by
    intro A
    calc S * (S⁻¹ * A * S⁻¹) * S
        = S * S⁻¹ * A * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hSmul, hSinv, Matrix.one_mul, Matrix.mul_one]
  have hSinvSandwich : ∀ A : Mat, S⁻¹ * (S * A * S) * S⁻¹ = A := by
    intro A
    calc S⁻¹ * (S * A * S) * S⁻¹
        = S⁻¹ * S * A * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hSinv, hSmul, Matrix.one_mul, Matrix.mul_one]
  -- ── Step 8: eigenvalue transfer (E → transferMap L) ──
  have heig_fwd : ∀ ν, Module.End.HasEigenvalue E ν →
      Module.End.HasEigenvalue (MPSTensor.transferMap (d := r) (D := D) L) ν := by
    intro ν hν
    obtain ⟨V, hV⟩ := hν.exists_hasEigenvector
    have hVne : V ≠ 0 := hV.2
    have hEV : E V = ν • V := Module.End.mem_eigenspace_iff.mp hV.1
    let W : Mat := S⁻¹ * V * S⁻¹
    have hWne : W ≠ 0 := by
      intro hW; apply hVne
      rw [show V = S * W * S from (hSandwich V).symm, hW, mul_zero, zero_mul]
    have hLW : MPSTensor.transferMap (d := r) (D := D) L W = ν • W := by
      rw [hL_transfer, hSandwich V, hEV, mul_smul_comm, smul_mul_assoc]
    exact hasEigenvalue_of_eigenvector_eq _ ν W hLW hWne
  -- ── Step 9: eigenvalue transfer (transferMap L → E) ──
  have heig_bwd : ∀ ν, Module.End.HasEigenvalue (MPSTensor.transferMap (d := r) (D := D) L) ν →
      Module.End.HasEigenvalue E ν := by
    intro ν hν
    obtain ⟨W, hW⟩ := hν.exists_hasEigenvector
    have hWne : W ≠ 0 := hW.2
    have hLW : MPSTensor.transferMap (d := r) (D := D) L W = ν • W :=
      Module.End.mem_eigenspace_iff.mp hW.1
    let V : Mat := S * W * S
    have hVne : V ≠ 0 := by
      intro hV; apply hWne
      rw [show W = S⁻¹ * V * S⁻¹ from (hSinvSandwich W).symm, hV, mul_zero, zero_mul]
    have hEV : E V = ν • V := by
      -- From hL_transfer W and hLW: S⁻¹ * E V * S⁻¹ = ν • W
      have h1 : S⁻¹ * E V * S⁻¹ = ν • W := by
        have := hL_transfer W; rw [hLW] at this; exact this.symm
      -- Sandwich with S to recover E V
      have h2 : E V = S * (ν • W) * S := by
        have := hSandwich (E V); rw [h1] at this; exact this.symm
      rw [h2, mul_smul_comm, smul_mul_assoc]
    exact hasEigenvalue_of_eigenvector_eq _ ν V hEV hVne
  -- ── Step 10: Apply power closure theorem and transfer back ──
  have hμ_L : μ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) L) :=
    ⟨heig_fwd μ hμ.1, hμ.2⟩
  have hpow := MPSTensor.peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint
    L hL_unital σ hσ_pd hL_adj hL_irr μ hμ_L
  intro n
  obtain ⟨hpow_eig, hpow_norm⟩ := hpow n
  exact ⟨heig_bwd (μ ^ n) hpow_eig, hpow_norm⟩

/-- Evaluation of powers after bundling an endomorphism as a continuous linear map. -/
private theorem toContinuousLinearMap_pow_apply [NeZero D]
    (F : Mat →ₗ[ℂ] Mat) (X : Mat) (n : ℕ) :
    (((Module.End.toContinuousLinearMap Mat) F) ^ n) X = (F ^ n) X := by
  have hpowEq : ((Module.End.toContinuousLinearMap Mat) F) ^ n =
      (Module.End.toContinuousLinearMap Mat) (F ^ n) := by
    simpa using (map_pow (Module.End.toContinuousLinearMap Mat) F n)
  rw [hpowEq]
  rfl

/-- In finite dimensions, a strict modulus bound on every eigenvalue gives a spectral-radius gap. -/
private theorem spectralRadius_lt_one_of_eigenvalues_lt_one [NeZero D]
    (F : Mat →ₗ[ℂ] Mat)
    (hF : ∀ ν : ℂ, Module.End.HasEigenvalue F ν → ‖ν‖ < 1) :
    spectralRadius ℂ ((Module.End.toContinuousLinearMap Mat) F) < 1 := by
  let Φ : (Mat →ₗ[ℂ] Mat) ≃ₐ[ℂ] (Mat →L[ℂ] Mat) := Module.End.toContinuousLinearMap Mat
  haveI : Nontrivial (Mat →L[ℂ] Mat) := ContinuousLinearMap.instNontrivialId
  obtain ⟨μ, hμ_spec, hμ_norm⟩ := spectrum.exists_nnnorm_eq_spectralRadius (Φ F)
  have hμ_spec_end : μ ∈ spectrum ℂ F := by
    rw [AlgEquiv.spectrum_eq Φ] at hμ_spec
    exact hμ_spec
  have hμ_ev : Module.End.HasEigenvalue F μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  have hμ_lt : ‖μ‖ < 1 := hF μ hμ_ev
  rw [← hμ_norm]
  exact by
    exact_mod_cast hμ_lt

/-- For an irreducible primitive channel, every trace-zero matrix lies in the decaying complement
of the fixed-point projection, hence its powers converge to zero. -/
private theorem primitive_channel_pow_tendsto_zero_of_trace_zero [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) (hE : IsChannel E) (hIrr : IsIrreducibleMap E)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_fix : E σ = σ)
    (hPrim : IsPrimitive E) {X : Mat} (htrX : Matrix.trace X = 0) :
    Filter.Tendsto (fun n : ℕ => (E ^ n) X) Filter.atTop (nhds 0) := by
  have htrσ : Matrix.trace σ ≠ 0 := by
    simpa [hσ_mem.2]
  let P : Mat →ₗ[ℂ] Mat := fixedPointProj (D := D) σ htrσ
  have hσ_ne : σ ≠ 0 := ne_zero_of_mem_densityMatrices' hσ_mem
  have hcompl_lt : ∀ ν : ℂ, Module.End.HasEigenvalue (E - P) ν → ‖ν‖ < 1 := by
    intro ν hν
    exact compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel
      E hE hIrr σ hσ_fix hσ_ne htrσ hPrim ν hν
  have hsr_lt : spectralRadius ℂ ((Module.End.toContinuousLinearMap Mat) (E - P)) < 1 :=
    spectralRadius_lt_one_of_eigenvalues_lt_one (D := D) (E - P) hcompl_lt
  have hpow0 : Filter.Tendsto
      (fun n : ℕ => ((Module.End.toContinuousLinearMap Mat) (E - P)) ^ n)
      Filter.atTop (nhds 0) :=
    MPSTensor.pow_tendsto_zero_of_spectralRadius_lt_one _ hsr_lt
  have hNpow0 : Filter.Tendsto (fun n : ℕ => ((E - P) ^ n) X) Filter.atTop (nhds 0) := by
    have hEval : Continuous (fun A : Mat →L[ℂ] Mat => A X) :=
      (ContinuousLinearMap.apply ℂ Mat X).continuous
    have hEvalT : Filter.Tendsto
        (fun n : ℕ => (((Module.End.toContinuousLinearMap Mat) (E - P)) ^ n) X)
        Filter.atTop (nhds 0) :=
      (hEval.tendsto 0).comp hpow0
    refine hEvalT.congr' ?_
    filter_upwards [] with n
    exact toContinuousLinearMap_pow_apply (D := D) (E - P) X n
  have hPX : P X = 0 := by
    simp [P, fixedPointProj, htrX]
  refine hNpow0.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn1 : 1 ≤ n := by
    omega
  have hpowEq :=
    pow_eq_fixedPointProj_add_compl_pow (D := D) (E := E) (ρ := σ) htrσ hE.tp hσ_fix hn1
  have hsumX : (P + (E - P) ^ n) X = ((E - P) ^ n) X := by
    simp [LinearMap.add_apply, hPX]
  calc
    ((E - P) ^ n) X = (P + (E - P) ^ n) X := by symm; exact hsumX
    _ = (E ^ n) X := by rw [← hpowEq]

/-! ## Prop 7.5: Irreducibility implies primitivity for QDS -/

set_option maxHeartbeats 50000000 in
/-- **Wolf Proposition 7.5** (1 → 3): If `T_{t₀}` is irreducible for some
`t₀ > 0`, then `T_t` is primitive for all `t > 0`.

The proof has two parts:

**Part 1 — Irreducibility propagation** (`hT_irr_all`):
`T_{t₀}` irreducible → `T_s` irreducible for ALL `s > 0`.
Uses the kernel bridge: `ker(L) = Span{σ}` where `σ` is the unique
faithful density fixed point of `T_{t₀}`. Then `σ` is fixed by all `T_s`
(semigroup commutativity + density uniqueness). For each `s > 0`, `T_s`
is shown irreducible via `isIrreducibleMap_of_channel_posDef_fixedPoint_unique`.

**Part 2 — Roots of unity → primitivity**:
Given irreducibility at all times, peripheral eigenvalues are roots of unity
(Wolf Thm 6.6). If `μ` is a peripheral eigenvalue of `T_t` with `μ^p = 1`,
the eigenvector `V` is a fixed point of `T_{pt}`. By irreducibility of
`T_{pt}`, `V` must be proportional to the unique faithful density fixed
point `σ'`, giving `T_t σ' = μ σ'`. Trace preservation then forces `μ = 1`.
**This part is fully proved.** -/
theorem irreducible_semigroup_implies_primitive
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∀ t : ℝ, 0 < t → IsPrimitive (T t) := by
  -- **Part 1**: Irreducibility propagation.
  -- If T_{t₀} is irreducible, then T_s is irreducible for ALL s > 0.
  -- The proof establishes ker(L) = Span{σ} (the unique faithful density fixed
  -- point), then uses `isIrreducibleMap_of_channel_posDef_fixedPoint_unique`.
  have hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s) := by
    have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
    have hTt₀_ch : IsChannel (T t₀) := hT.channel t₀ (le_of_lt ht₀)
    obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique⟩ :=
      IsChannel.exists_unique_density_fixedPoint_of_irreducible (E := T t₀) hTt₀_ch hirr hD
    -- Step 1: σ is fixed by ALL T_u for u ≥ 0 (semigroup commutativity + uniqueness).
    have hσ_fix_all : ∀ u : ℝ, 0 ≤ u → T u σ = σ := by
      intro u hu
      exact hσ_unique (T u σ)
        (IsChannel.map_densityMatrices _ (hT.channel u hu) σ hσ_mem)
        (by have h1 := hT.semigroup.semigroup.comp t₀ u (le_of_lt ht₀) hu
            have h2 := hT.semigroup.semigroup.comp u t₀ hu (le_of_lt ht₀)
            show T t₀ (T u σ) = T u σ
            have heval1 : (T t₀).comp (T u) σ = T (t₀ + u) σ := by
              rw [h1]
            have heval2 : (T u).comp (T t₀) σ = T (u + t₀) σ := by
              rw [h2]
            simp only [LinearMap.comp_apply] at heval1 heval2
            rw [heval1, add_comm, ← heval2, hσ_fix])
    have hfixed_1d : ∀ X : Matrix (Fin D) (Fin D) ℂ, T t₀ X = X →
        X = Matrix.trace X • σ := by
      intro X hX
      exact eq_of_sub_eq_zero
        (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel hTt₀_ch hirr _
          (by rw [map_sub, map_smul, hX, hσ_fix])
          (by rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul,
                   mul_one, sub_self]))
    let N : ℕ := Nat.factorial (Module.finrank ℂ Mat)
    have hN_pos : 0 < N := Nat.factorial_pos _
    let u : ℝ := t₀ / N
    have hu_nonneg : 0 ≤ u := le_of_lt <| div_pos ht₀ (Nat.cast_pos.mpr hN_pos)
    have hu_pos : 0 < u := div_pos ht₀ (Nat.cast_pos.mpr hN_pos)
    have hNu : (N : ℝ) * u = t₀ := by
      dsimp [u]
      field_simp [hN_pos.ne']
    have hTt₀_eq_pow : T t₀ = (T u) ^ N := by
      calc
        T t₀ = T ((N : ℝ) * u) := by rw [hNu]
        _ = (T u) ^ N := semigroup_pow T hT.semigroup.semigroup u hu_nonneg N
    have hTu_ch : IsChannel (T u) := hT.channel u hu_nonneg
    have hTu_fix : T u σ = σ := hσ_fix_all u hu_nonneg
    have hTu_irr : IsIrreducibleMap (T u) := by
      intro P hP_proj hP_inv
      exact hirr P hP_proj (by
        intro X
        rw [hTt₀_eq_pow]
        exact compression_preserved_by_pow (E := T u) (P := P) hP_proj hP_inv N X)
    have hTu_prim : IsPrimitive (T u) := by
      apply isPrimitive_of_unique_norm_one (T u) σ hTu_fix (ne_zero_of_mem_densityMatrices' hσ_mem)
      intro μ hμ_eig hμ_norm
      have hμ_per : μ ∈ peripheralEigenvalues (T u) := ⟨hμ_eig, hμ_norm⟩
      have hclosed : ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues (T u) :=
        peripheral_powers_closed_of_irreducible_channel_with_fixed
          (T u) hTu_ch hTu_irr σ hσ_pd hTu_fix hμ_per
      obtain ⟨p, hp_pos, hp_le, hμp⟩ :=
        bounded_root_of_peripheral_closed_powers (T u) μ hμ_per hclosed
      have hp_dvdN : p ∣ N := by
        simpa [N] using Nat.dvd_factorial hp_pos hp_le
      rcases hp_dvdN with ⟨m, hm⟩
      have hμN : μ ^ N = 1 := by
        rw [hm, pow_mul, hμp, one_pow]
      obtain ⟨X, hX⟩ := hμ_eig.exists_hasEigenvector
      have hX_ne : X ≠ 0 := hX.2
      have hTuX : T u X = μ • X := Module.End.mem_eigenspace_iff.mp hX.1
      have hTt₀X : T t₀ X = X := by
        rw [hTt₀_eq_pow, pow_apply_eigenvector (T u) X μ N hTuX, hμN, one_smul]
      have hX_eq : X = Matrix.trace X • σ := hfixed_1d X hTt₀X
      have htr_ne : Matrix.trace X ≠ 0 := by
        intro htr
        apply hX_ne
        rw [hX_eq, htr]
        simp
      have htpX := hTu_ch.tp X
      rw [hTuX, Matrix.trace_smul] at htpX
      have htpX' : μ * Matrix.trace X = Matrix.trace X := by
        simpa [smul_eq_mul] using htpX
      have hzero : (μ - 1) * Matrix.trace X = 0 := by
        calc
          (μ - 1) * Matrix.trace X = μ * Matrix.trace X - Matrix.trace X := by ring
          _ = 0 := by rw [htpX', sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right htr_ne)
    intro s hs
    apply isIrreducibleMap_of_channel_posDef_fixedPoint_unique (T s)
      (hT.channel s (le_of_lt hs)) σ hσ_pd (hσ_fix_all s (le_of_lt hs))
    intro τ hτ_psd hτ_fix
    let δ : Mat := τ - Matrix.trace τ • σ
    have hδ_tr : Matrix.trace δ = 0 := by
      dsimp [δ]
      rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul, mul_one, sub_self]
    have hδ_fix : T s δ = δ := by
      dsimp [δ]
      rw [map_sub, map_smul, hτ_fix, hσ_fix_all s (le_of_lt hs)]
    have hδ_decay : Filter.Tendsto (fun n : ℕ => T ((n : ℝ) * u) δ) Filter.atTop (nhds 0) := by
      have hpow_decay :=
        primitive_channel_pow_tendsto_zero_of_trace_zero
          (E := T u) hTu_ch hTu_irr σ hσ_mem hTu_fix hTu_prim hδ_tr
      refine hpow_decay.congr' ?_
      filter_upwards [] with n
      rw [← semigroup_pow T hT.semigroup.semigroup u hu_nonneg n]
    let m : ℕ → ℕ := fun n => Int.toNat ⌊((n : ℝ) * u) / s⌋
    let r : ℕ → ℝ := fun n => s * Int.fract (((n : ℝ) * u) / s)
    have hr_mem : ∀ n : ℕ, r n ∈ Set.Icc 0 s := by
      intro n
      dsimp [r]
      refine Set.mem_Icc.mpr ?_
      constructor
      · exact mul_nonneg (le_of_lt hs) (Int.fract_nonneg _)
      · have hlt : Int.fract (((n : ℝ) * u) / s) < 1 := Int.fract_lt_one _
        nlinarith [hlt, hs]
    have hdecomp : ∀ n : ℕ, (n : ℝ) * u = (m n : ℝ) * s + r n := by
      intro n
      dsimp [m, r]
      have ha : ↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s) = ((n : ℝ) * u) / s :=
        Int.floor_add_fract (((n : ℝ) * u) / s)
      have hfloor_nonneg : 0 ≤ ⌊((n : ℝ) * u) / s⌋ := by
        apply Int.floor_nonneg.mpr
        positivity
      have htoNat : ((Int.toNat ⌊((n : ℝ) * u) / s⌋ : ℕ) : ℝ) = ↑⌊((n : ℝ) * u) / s⌋ := by
        exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
      have hmulha :
          s * (↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s)) =
            s * (((n : ℝ) * u) / s) := by
        exact congrArg (fun x : ℝ => s * x) ha
      calc
        (n : ℝ) * u = s * (((n : ℝ) * u) / s) := by field_simp [hs.ne']
        _ = s * (↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s)) := by
              simpa using hmulha.symm
        _ = ((Int.toNat ⌊((n : ℝ) * u) / s⌋ : ℕ) : ℝ) * s +
              s * Int.fract (((n : ℝ) * u) / s) := by
              rw [mul_add, htoNat]
              ring
    have hms_fix : ∀ n : ℕ, T ((m n : ℝ) * s) δ = δ := by
      intro n
      have hpow_fix : ∀ k : ℕ, ((T s) ^ k) δ = δ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [pow_succ']
            simpa [ih] using hδ_fix
      rw [semigroup_pow T hT.semigroup.semigroup s (le_of_lt hs) (m n)]
      exact hpow_fix (m n)
    have hres_eq : ∀ n : ℕ, T ((n : ℝ) * u) δ = T (r n) δ := by
      intro n
      calc
        T ((n : ℝ) * u) δ = T (r n + (m n : ℝ) * s) δ := by
          rw [hdecomp n, add_comm]
        _ = T (r n) (T ((m n : ℝ) * s) δ) := by
          simp [LinearMap.comp_apply,
            hT.semigroup.semigroup.comp (r n) ((m n : ℝ) * s) (hr_mem n).1
              (mul_nonneg (Nat.cast_nonneg (m n)) (le_of_lt hs))]
        _ = T (r n) δ := by rw [hms_fix n]
    have hmap_le : Filter.map r Filter.atTop ≤ Filter.principal (Set.Icc 0 s) := by
      rw [Filter.le_principal_iff]
      show r ⁻¹' Set.Icc 0 s ∈ Filter.atTop
      exact Filter.Eventually.of_forall hr_mem
    obtain ⟨a, ha_mem, hcluster⟩ := (isCompact_Icc (a := 0) (b := s)).exists_clusterPt hmap_le
    obtain ⟨φ, hφmono, hφtendsto⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
    have hδ_cont : Continuous (fun t : ℝ => T t δ) := by
      have hEval : Continuous (fun A : Mat →L[ℂ] Mat => A δ) :=
        (ContinuousLinearMap.apply ℂ Mat δ).continuous
      simpa using hEval.comp hT.semigroup.continuous
    have hsub_decay : Filter.Tendsto (fun k : ℕ => T (((φ k : ℝ)) * u) δ) Filter.atTop (nhds 0) :=
      hδ_decay.comp hφmono.tendsto_atTop
    have hsub_res : Filter.Tendsto (fun k : ℕ => T (r (φ k)) δ) Filter.atTop (nhds (T a δ)) :=
      (hδ_cont.tendsto a).comp hφtendsto
    have hsub_res_zero : Filter.Tendsto (fun k : ℕ => T (r (φ k)) δ) Filter.atTop (nhds 0) := by
      refine hsub_decay.congr' ?_
      exact Filter.Eventually.of_forall (fun k => hres_eq (φ k))
    have hTa_zero : T a δ = 0 := tendsto_nhds_unique hsub_res hsub_res_zero
    have hδ_zero_exp : expSemigroup L a δ = 0 := by
      rw [← hexp a ha_mem.1]
      exact hTa_zero
    have hδ_zero : δ = 0 := by
      have h := congrArg (fun Y => expSemigroup L (-a) Y) hδ_zero_exp
      simp only [map_zero] at h
      have hcomp : (expSemigroup L (-a)) ((expSemigroup L a) δ) =
          (expSemigroup L (-a)).comp (expSemigroup L a) δ := rfl
      rw [hcomp, ← expSemigroup_comp, show -a + a = 0 from neg_add_cancel a,
        expSemigroup_zero, LinearMap.id_apply] at h
      exact h
    exact ⟨Matrix.trace τ, sub_eq_zero.mp hδ_zero⟩
  -- **Part 2**: Roots of unity → primitivity (fully proved below).
  intro t ht
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hTt_ch : IsChannel (T t) := hT.channel t (le_of_lt ht)
  have hT_irr : IsIrreducibleMap (T t) := hT_irr_all t ht
  -- Get the unique PosDef density-matrix fixed point σ of T_t.
  obtain ⟨σ, hσ_mem, _hσ_pd, hσ_fix, _hσ_uniq⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible (E := T t) hTt_ch hT_irr hD
  have hσ_ne : σ ≠ 0 := ne_zero_of_mem_densityMatrices' hσ_mem
  -- Apply isPrimitive_of_unique_norm_one: suffices to show μ = 1 for all
  -- peripheral eigenvalues μ.
  apply isPrimitive_of_unique_norm_one (T t) σ hσ_fix hσ_ne
  intro μ hμ_eig hμ_norm
  -- Peripheral eigenvalues of T_t are roots of unity (Wolf Thm 6.6).
  obtain ⟨p, hp_pos, hpow⟩ :=
    peripheral_isRootOfUnity_of_irreducible_channel (T t) hTt_ch hT_irr μ ⟨hμ_eig, hμ_norm⟩
  -- Get eigenvector V with (T t) V = μ • V, V ≠ 0.
  obtain ⟨V, hV_ev⟩ := hμ_eig.exists_hasEigenvector
  have hV_ne : V ≠ 0 := hV_ev.2
  have hTV : (T t) V = μ • V := Module.End.mem_eigenspace_iff.mp hV_ev.1
  -- (T t)^p V = μ^p • V = 1 • V = V: V is a fixed point of T_{pt}.
  have hTpV : ((T t) ^ p) V = V := by
    rw [pow_apply_eigenvector (T t) V μ p hTV, hpow, one_smul]
  -- T_{pt} = (T t)^p by the semigroup law.
  have hTpow : (T t) ^ p = T (↑p * t) :=
    (semigroup_pow T hT.semigroup.semigroup t (le_of_lt ht) p).symm
  -- T_{pt} is an irreducible channel.
  have hpt_pos : 0 < (↑p : ℝ) * t := mul_pos (Nat.cast_pos.mpr hp_pos) ht
  have hpt_ch : IsChannel (T (↑p * t)) := hT.channel _ (le_of_lt hpt_pos)
  have hpt_irr : IsIrreducibleMap (T (↑p * t)) := hT_irr_all _ hpt_pos
  -- V is a fixed point of T_{pt}.
  have hV_fix : T (↑p * t) V = V := by rw [← hTpow]; exact hTpV
  -- Get unique PosDef density-matrix fixed point σ' of T_{pt}.
  obtain ⟨σ', hσ'_mem, _hσ'_pd, hσ'_fix, _⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible
      (E := T (↑p * t)) hpt_ch hpt_irr hD
  -- V has nonzero trace (trace-zero fixed points of irreducible channels are zero).
  have hV_tr_ne : Matrix.trace V ≠ 0 := by
    intro htr
    exact hV_ne (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
      hpt_ch hpt_irr V hV_fix htr)
  -- The fixed-point space of T_{pt} is one-dimensional: V = (trace V) • σ'.
  have hV_eq : V = (Matrix.trace V) • σ' := by
    have hW_fix : T (↑p * t) (V - (Matrix.trace V) • σ') = V - (Matrix.trace V) • σ' := by
      rw [map_sub, map_smul, hV_fix, hσ'_fix]
    have hW_tr : Matrix.trace (V - (Matrix.trace V) • σ') = 0 := by
      rw [Matrix.trace_sub, Matrix.trace_smul, hσ'_mem.2, smul_eq_mul, mul_one, sub_self]
    exact sub_eq_zero.mp
      (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
        hpt_ch hpt_irr _ hW_fix hW_tr)
  -- Derive T_t σ' = μ • σ' from the eigenvector equation.
  have hTσ' : (T t) σ' = μ • σ' := by
    have h1 : (Matrix.trace V) • (T t) σ' = (μ * Matrix.trace V) • σ' := by
      calc (Matrix.trace V) • (T t) σ'
          = (T t) ((Matrix.trace V) • σ') := (map_smul (T t) _ σ').symm
        _ = (T t) V := by rw [← hV_eq]
        _ = μ • V := hTV
        _ = μ • ((Matrix.trace V) • σ') := by rw [hV_eq]
        _ = (μ * Matrix.trace V) • σ' := by rw [smul_smul]
    -- Cancel the nonzero scalar (trace V).
    have h2 : (Matrix.trace V) • (T t) σ' = (Matrix.trace V) • (μ • σ') := by
      rw [h1, smul_smul]
    have h3 := congr_arg ((Matrix.trace V)⁻¹ • ·) h2
    simp only [smul_smul, inv_mul_cancel₀ hV_tr_ne, one_smul] at h3
    exact h3
  -- **Key step**: trace preservation forces μ = 1.
  -- trace(T_t σ') = trace(σ') = 1 (TP), and trace(μ • σ') = μ · trace(σ') = μ.
  have htp : IsTracePreservingMap (T t) := hTt_ch.tp
  have h_tr_eq : Matrix.trace ((T t) σ') = Matrix.trace σ' := htp σ'
  rw [hTσ', Matrix.trace_smul, hσ'_mem.2, smul_eq_mul, mul_one] at h_tr_eq
  exact h_tr_eq

/-- **Wolf Proposition 7.5** (full equivalence): For a QDS of channels, the
following are equivalent:
1. There exists `t₀ > 0` such that `T_{t₀}` is irreducible.
2. `T_t` is irreducible for all `t > 0`.
3. `T_t` is primitive for all `t > 0`.
4. There exists a positive definite `ρ_∞` such that `T_t(ρ) → ρ_∞` for all
   density matrices `ρ`.
5. `ker(L)` is one-dimensional and spanned by a positive definite `ρ_∞`. -/
theorem qds_irreducible_iff_primitive
    [NeZero D]
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
    --
    -- **Status**: this direction is not provable with the current definition
    -- `IsPrimitive E := peripheralEigenvalues E = {1}`.
    --
    -- The issue is that `IsPrimitive` records only the *set* of peripheral
    -- eigenvalues and does NOT exclude a higher-dimensional eigenspace at `1`.
    -- Reducible dephasing-type channels (e.g., the identity on `M₂(ℂ)`) have
    -- peripheral set `{1}` while still having several linearly independent
    -- fixed points, making the implication to irreducibility false.
    --
    -- To close this theorem correctly, the RHS should be replaced by a stronger
    -- notion, e.g. spectral-gap primitivity (spectral radius of `E - P` < 1),
    -- uniqueness of the PSD fixed point, or the full Wolf Thm 6.7 package.
    intro hprim
    exact ⟨1, one_pos, by sorry⟩

end -- noncomputable section
