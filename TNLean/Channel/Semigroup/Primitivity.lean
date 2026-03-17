/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.IrreducibleChannel
import TNLean.Channel.FixedPoint.Cesaro
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

/-! ## Prop 7.5: Irreducibility implies primitivity for QDS -/

/-- **Wolf Proposition 7.5** (1 → 3): If `T_{t₀}` is irreducible for some
`t₀ > 0`, then `T_t` is primitive for all `t > 0`.

The proof has two parts:

**Part 1 — Irreducibility propagation** (`hT_irr_all`):
`T_{t₀}` irreducible → `T_s` irreducible for ALL `s > 0`.
This is the continuous-time fact, dual to the discrete-time result that
a power of a primitive map is primitive. It requires formalizing the
equivalence between generator and semigroup irreducibility conditions
(cf. Wolf §7.1, Evans–Høegh-Krohn 1978). **Currently left as sorry.**

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
  -- **Part 1**: Irreducibility propagation (the remaining sorry).
  -- In a norm-continuous QDS, `T_{t₀}` irreducible implies `T_s` irreducible
  -- for ALL `s > 0`. This is a generator-level property: irreducibility of
  -- `T_{t₀}` implies that `L` has no non-trivial invariant face, which is
  -- equivalent to `T_s` being irreducible for every `s > 0`.
  -- The proof requires formalizing the equivalence between semigroup and
  -- generator irreducibility (Wolf §7.1, Evans–Høegh-Krohn 1978).
  have hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s) := by
    sorry
  -- **Part 2**: Roots of unity → primitivity (fully proved below).
  intro t ht
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hTt_ch : IsChannel (T t) := hT.channel t (le_of_lt ht)
  have hT_irr : IsIrreducibleMap (T t) := hT_irr_all t ht
  -- Get the unique PosDef density-matrix fixed point σ of T_t.
  obtain ⟨σ, hσ_mem, _hσ_pd, hσ_fix, _hσ_uniq⟩ :=
    hTt_ch.exists_unique_density_fixedPoint_of_irreducible hT_irr hD
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
    hpt_ch.exists_unique_density_fixedPoint_of_irreducible hpt_irr hD
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
