/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.MeanErgodicProjection
import Mathlib.Analysis.Matrix.Normed

/-!
# Trivial Jordan blocks for peripheral eigenvalues — Wolf Proposition 6.2

**Wolf Proposition 6.2**: Let $T: M_d(\mathbb{C}) \to M_d(\mathbb{C})$ be a
trace-preserving (or unital) positive linear map. If $\lambda$ is an eigenvalue
of $T$ with $|\lambda| = 1$, then its geometric multiplicity equals its algebraic
multiplicity, i.e., all Jordan blocks for $\lambda$ are one-dimensional.

The proof: if a Jordan block of size $\ge 2$ existed, the binomial expansion
$T^n = (\lambda I + N)^n$ applied to a rank-$2$ generalized eigenvector
would produce a term proportional to $n$, giving $\|T^n X\| \ge n\|Y\| - \|X\|$,
which grows without bound. This contradicts the bounded-orbit theorem
for positive trace-preserving maps.

## Main results

* `IsPositiveMap.no_rank_two_genEigenvector_of_tracePreserving`:
  $\ker(T-\lambda)^2 = \ker(T-\lambda)$ when $|\lambda| = 1$.
* `IsPositiveMap.peripheral_Jordan_trivial_of_tracePreserving`:
  generalized eigenspace equals eigenspace for peripheral eigenvalues.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.2][Wolf2012QChannels]
* Local source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224.
-/

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius
open Matrix Filter

variable {D : ℕ}

namespace IsPositiveMap

/-! ### Binomial expansion for rank-2 generalized eigenvectors -/

/-- If $(T - \lambda)^2 X = 0$, then $T^n X = \lambda^n X + n \lambda^{n-1} (T-\lambda)X$.

Proved by induction on $n$ using $T = \lambda I + N$ with $N = T - \lambda I$
and $N^2 X = 0$.

Source: Wolf, Proposition 6.2 proof, Eq. (6.10); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
lemma pow_apply_rank_two_genEig
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (μ : ℂ) (n : ℕ) (X : V)
    (hN2 : ((T - μ • (1 : V →ₗ[ℂ] V)) ^ 2) X = 0) :
    (T ^ n) X = (μ ^ n) • X +
      ((n : ℂ) * μ ^ (n - 1)) • ((T - μ • (1 : V →ₗ[ℂ] V)) X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', show (T * T ^ n) X = T ((T ^ n) X) from rfl, ih]
    rw [map_add, map_smul, map_smul]
    have h_TTX : T ((T - μ • (1 : V →ₗ[ℂ] V)) X) =
        μ • ((T - μ • (1 : V →ₗ[ℂ] V)) X) := by
      -- T = (T-μ) + μ, so T((T-μ)X) = (T-μ)^2 X + μ(T-μ)X = μ(T-μ)X (since (T-μ)^2 X = 0)
      calc
        T ((T - μ • (1 : V →ₗ[ℂ] V)) X)
            = ((T - μ • (1 : V →ₗ[ℂ] V)) + μ • (1 : V →ₗ[ℂ] V))
                ((T - μ • (1 : V →ₗ[ℂ] V)) X) := by simp
        _ = (T - μ • (1 : V →ₗ[ℂ] V)) ((T - μ • (1 : V →ₗ[ℂ] V)) X) +
            (μ • (1 : V →ₗ[ℂ] V)) ((T - μ • (1 : V →ₗ[ℂ] V)) X) :=
          by rw [LinearMap.add_apply]
        _ = ((T - μ • (1 : V →ₗ[ℂ] V)) ^ 2) X +
            μ • ((T - μ • (1 : V →ₗ[ℂ] V)) X) := by
          simp [pow_two, LinearMap.smul_apply]
        _ = 0 + μ • ((T - μ • (1 : V →ₗ[ℂ] V)) X) := by rw [hN2]
        _ = μ • ((T - μ • (1 : V →ₗ[ℂ] V)) X) := by simp
    -- Substitute into the expression
    rw [h_TTX]

    have h_TX : T X = μ • X + (T - μ • (1 : V →ₗ[ℂ] V)) X := by
      calc
        T X = ((T - μ • (1 : V →ₗ[ℂ] V)) + μ • (1 : V →ₗ[ℂ] V)) X := by simp
        _ = (T - μ • (1 : V →ₗ[ℂ] V)) X + (μ • (1 : V →ₗ[ℂ] V)) X :=
          by rw [LinearMap.add_apply]
        _ = (T - μ • (1 : V →ₗ[ℂ] V)) X + μ • X := by simp
        _ = μ • X + (T - μ • (1 : V →ₗ[ℂ] V)) X := add_comm _ _
    rw [h_TX]
    -- = μ^n (μ X + (T-μ) X) + n μ^n (T-μ) X
    -- = μ^{n+1} X + μ^n (T-μ) X + n μ^n (T-μ) X
    -- = μ^{n+1} X + (n+1) μ^n (T-μ) X

    -- Replace T X by μ X + (T-μ)X
    -- T X was already rewritten above
    simp only [smul_add, smul_smul]
    have hX : (μ ^ n : ℂ) * μ = μ ^ (n + 1) := by ring
    -- Simplify (T-μ)X-term: μ^n + μ*n*μ^(n-1) = (n+1)*μ^n = ↑(n+1)*μ^{(n+1)-1}
    have hV : (μ ^ n : ℂ) + (μ : ℂ) * ((n : ℂ) * (μ ^ (n - 1) : ℂ))
        = (↑(n + 1) : ℂ) * (μ ^ (n + 1 - 1) : ℂ) := by
      have h_pow : (μ : ℂ) ^ (n + 1 - 1) = (μ : ℂ) ^ n := by
        rw [show (n : ℕ) + 1 - 1 = n by omega]
      rw [h_pow]
      push_cast
      rcases Nat.eq_zero_or_pos n with (rfl | hn)
      · simp
      · -- n ≥ 1: then μ * μ^(n-1) = μ^n
        have h_mul_pow : (μ : ℂ) * (μ : ℂ) ^ (n - 1) = (μ : ℂ) ^ n := by
          rw [← pow_succ', Nat.sub_add_cancel hn]
        calc
          (μ ^ n : ℂ) + (μ : ℂ) * ((n : ℂ) * (μ : ℂ) ^ (n - 1))
              = (μ ^ n : ℂ) + ((n : ℂ) * ((μ : ℂ) * (μ : ℂ) ^ (n - 1))) := by ring
          _ = (μ ^ n : ℂ) + ((n : ℂ) * (μ : ℂ) ^ n) := by rw [h_mul_pow]
          _ = ((n : ℂ) + 1) * (μ ^ n : ℂ) := by ring
    have h_v_coeff : (μ ^ n : ℂ) + ((n : ℂ) * (μ ^ (n - 1) : ℂ) * μ)
        = (↑(n + 1) : ℂ) * (μ ^ (n + 1 - 1) : ℂ) := by
      -- hV LHS is μ^n + μ*(n*μ^(n-1)) which equals μ^n + n*μ^(n-1)*μ by commutativity
      simpa [mul_comm, mul_left_comm, mul_assoc] using hV
    rw [hX]
    have h_combine : (μ ^ n : ℂ) • ((T - μ • (1 : V →ₗ[ℂ] V)) X) +
        ((n : ℂ) * (μ ^ (n - 1) : ℂ) * μ) • ((T - μ • (1 : V →ₗ[ℂ] V)) X) =
        (↑(n + 1) * (μ ^ (n + 1 - 1) : ℂ)) • ((T - μ • (1 : V →ₗ[ℂ] V)) X) := by
      rw [← add_smul, h_v_coeff]
    -- Apply this in the larger expression
    -- The LHS is: μ^{n+1} • X + (μ^n • v + c • v)
    -- The parenthesization is (μ^{n+1} • X + μ^n • v) + c • v
    -- We need to rewrite the last two terms
    -- Use `rw` with `add_comm` and `add_assoc` to bring the v-terms together
    -- The LHS is: μ^(n+1) • X + μ^n • v + c • v
    -- where v = (T-μ)X, c = n*μ^(n-1)*μ
    -- Regroup: μ^(n+1) • X + (μ^n • v + c • v)
    -- Then apply h_combine to the parenthesized part
    rw [add_assoc, h_combine]

/-- **Wolf Proposition 6.2** (key step): For a positive trace-preserving map,
no rank-2 generalized eigenvector exists at a peripheral eigenvalue.

If $(T-\lambda)^2 X = 0$ with $|\lambda| = 1$, then $(T-\lambda)X = 0$.

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
theorem no_rank_two_genEigenvector_of_tracePreserving
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (μ : ℂ) (hμ_norm : ‖μ‖ = 1) (X : Matrix (Fin D) (Fin D) ℂ)
    (hN2 : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) ^ 2) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) X = 0 := by
  set N := T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
  by_contra h_not
  have hNX_ne_zero : N X ≠ 0 := h_not
  have hNX_norm_pos : 0 < ‖N X‖ := norm_pos_iff.mpr hNX_ne_zero
  have hbounded : T.HasBoundedOrbits :=
    hPos.hasBoundedOrbits_of_tracePreserving hTP
  -- Binomial expansion: T^n X = μ^n X + n μ^{n-1} (N X)
  have h_pow_formula (n : ℕ) :
      (T ^ n) X = (μ ^ n) • X + ((n : ℂ) * μ ^ (n - 1)) • (N X) :=
    pow_apply_rank_two_genEig T μ n X hN2
  -- Norm lower bound: ‖T^n X‖ ≥ n ‖N X‖ - ‖X‖
  -- Uses: ‖a + b‖ ≥ ‖b‖ - ‖a‖, and ‖μ^k‖ = 1 for all k
  have h_norm_μ_pow (k : ℕ) : ‖μ ^ k‖ = 1 := by
    rw [norm_pow, hμ_norm, one_pow]
  have h_norm_bound (n : ℕ) : (n : ℝ) * ‖N X‖ - ‖X‖ ≤ ‖(T ^ n) X‖ := by
    rw [h_pow_formula n]
    -- Let a = n μ^{n-1} (N X), b = μ^n X
    -- ‖a + b‖ ≥ ‖a‖ - ‖b‖
    have h_rev_triangle : ‖((n : ℂ) * μ ^ (n - 1)) • (N X)‖ ≤
        ‖((n : ℂ) * μ ^ (n - 1)) • (N X) + (μ ^ n) • X‖ + ‖(μ ^ n) • X‖ := by
      calc
        ‖((n : ℂ) * μ ^ (n - 1)) • (N X)‖
            = ‖(((n : ℂ) * μ ^ (n - 1)) • (N X) + (μ ^ n) • X) - (μ ^ n) • X‖ := by simp
        _ ≤ ‖((n : ℂ) * μ ^ (n - 1)) • (N X) + (μ ^ n) • X‖ + ‖(μ ^ n) • X‖ :=
          norm_sub_le _ _
    -- Compute norms of the pieces
    have h_norm_a : ‖((n : ℂ) * μ ^ (n - 1)) • (N X)‖ = (n : ℝ) * ‖N X‖ := by
      rw [norm_smul, norm_mul, h_norm_μ_pow (n - 1), mul_one, Complex.norm_natCast]
    have h_norm_b : ‖(μ ^ n) • X‖ = ‖X‖ := by
      rw [norm_smul, h_norm_μ_pow n, one_mul]
    rw [h_norm_a, h_norm_b] at h_rev_triangle
    -- Rearranged: (n)*‖NX‖ - ‖X‖ ≤ ‖...‖
    -- Using a - b ≤ c ↔ a ≤ c + b
    have h_goal : (n : ℝ) * ‖N X‖ - ‖X‖ ≤
        ‖(μ ^ n) • X + ((n : ℂ) * μ ^ (n - 1)) • (N X)‖ := by
      rw [sub_le_iff_le_add]
      simpa [add_comm] using h_rev_triangle
    simpa [add_comm] using h_goal
  -- For large n, n * ‖N X‖ exceeds any bound → contradicts bounded orbits
  rcases isBounded_iff_forall_norm_le.mp (hbounded X) with ⟨C, hC⟩
  -- hC : ∀ x ∈ Set.range (fun n => (T ^ n) X), ‖x‖ ≤ C
  -- Pick n large enough so that n * ‖N X‖ - ‖X‖ > C
  have hpos : 0 < ‖N X‖ := hNX_norm_pos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, C + ‖X‖ < (n : ℝ) * ‖N X‖ := by
    have h_arch := exists_nat_gt ((C + ‖X‖) / ‖N X‖)
    rcases h_arch with ⟨n, hn⟩
    refine ⟨n, (div_lt_iff₀ hpos).mp hn⟩
  have hC_n := hC ((T^[n]) X) ⟨n, rfl⟩
  have h_bound_n := h_norm_bound n
  -- h_bound_n gives bound on ‖(T^n)X‖, but hC_n is about ‖(T^[n])X‖
  -- Use Module.End.pow_apply to connect them: (T^n)X = (T^[n])X
  have h_pow_eq : (T ^ n) X = (T^[n]) X := by simpa using Module.End.pow_apply T n X
  rw [h_pow_eq] at h_bound_n
  -- Now h_bound_n: (n:ℝ)*‖NX‖ - ‖X‖ ≤ ‖(T^[n])X‖
  -- hC_n: ‖(T^[n])X‖ ≤ C
  -- hn: C + ‖X‖ < (n:ℝ)*‖NX‖
  -- Combine: C + ‖X‖ < n*‖NX‖, so C < n*‖NX‖ - ‖X‖ ≤ ‖(T^[n])X‖ ≤ C
  have h_ineq : C < (n : ℝ) * ‖N X‖ - ‖X‖ := by linarith
  have h_chain : (n : ℝ) * ‖N X‖ - ‖X‖ ≤ C := by
    -- from h_bound_n and hC_n
    -- hC_n: B ≤ C
    -- So A - ‖X‖ ≤ B ≤ C → A - ‖X‖ ≤ C
    -- But we need A - ‖X‖ ≤ C which follows from h_bound_n and hC_n
    linarith
  linarith

/-- **Wolf Proposition 6.2** (full statement): For a positive trace-preserving map,
the generalized eigenspace for any peripheral eigenvalue $\lambda$ equals
the eigenspace: $\ker(T-\lambda)^k = \ker(T-\lambda)$ for all $k \ge 1$.

In other words, peripheral eigenvalues have trivial Jordan blocks
(algebraic multiplicity equals geometric multiplicity).

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
theorem peripheral_Jordan_trivial_of_tracePreserving
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (μ : ℂ) (hμ_norm : ‖μ‖ = 1) (k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hNk : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) ^ k) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) X = 0 := by
  -- Prove by induction on k that ((T-μ)^k) X = 0 implies (T-μ) X = 0
  induction k with
  | zero =>
    have hX_zero : X = 0 := by simpa using hNk
    simp [hX_zero]
  | succ m ih =>
    set N := T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
      with hN_def
    by_cases hm : m = 0
    · subst hm; simpa using hNk
    · -- m ≥ 1, rank-2 reduction
      set Y := (N ^ (m - 1)) X
      have hN2_Y : (N ^ 2) Y = 0 := by
        dsimp [Y]
        -- (T-μ)^2((T-μ)^{m-1}X) = ((T-μ)^2*(T-μ)^{m-1})X = (T-μ)^{m+1}X
        have : (N ^ 2) Y =
            (N ^ (2 + (m - 1))) X := by
          dsimp [Y]
          calc
            (N ^ 2)
                ((N ^ (m - 1)) X)
                = ((N ^ 2) *
                   (N ^ (m - 1))) X := rfl
            _ = (N ^ (2 + (m - 1))) X := by
              rw [pow_add]
        rw [this, show (2 : ℕ) + (m - 1) = m + 1 by omega]
        exact hNk
      have hN1_Y : N Y = 0 :=
        hPos.no_rank_two_genEigenvector_of_tracePreserving hTP μ hμ_norm Y hN2_Y
      -- hN1_Y: (T - μ•1) Y = 0  where Y = (T-μ•1)^(m-1) X
      -- We need: ((T-μ•1)^m) X = 0 for the induction hypothesis ih
      -- Compute: (T-μ•1) Y = (T-μ•1) ((T-μ•1)^(m-1) X) = ((T-μ•1)^m) X
      -- because (T-μ•1) ∘ (T-μ•1)^(m-1) = (T-μ•1)^m in the endomorphism ring
      have h_pow_eq : N Y
          = (N ^ m) X := by
        dsimp [Y]
        calc
          N
              ((N ^ (m - 1)) X)
              = ((N) *
                 (N ^ (m - 1))) X := rfl
          _ = ((N ^ (1 : ℕ)) *
               (N ^ (m - 1))) X := by
            simp
          _ = (N ^ ((1 : ℕ) + (m - 1))) X := by
            rw [← pow_add]
          _ = (N ^ m) X := by
            rw [show (1 : ℕ) + (m - 1) = m by omega]
      -- Now rewrite hN1_Y using h_pow_eq
      rw [h_pow_eq] at hN1_Y
      exact ih hN1_Y


end IsPositiveMap
