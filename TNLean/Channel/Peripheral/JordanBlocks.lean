/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.MeanErgodicProjection
import TNLean.Channel.Schwarz.PositiveMapProperties
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
which grows without bound. This contradicts the uniform boundedness of the
orbits of a positive trace-preserving or unital map. Wolf's bound
$\operatorname{tr}[A\,T(B)] \le \|A\|_\infty \|B\|_\infty \operatorname{tr}[1\,T(1)]
= d \|A\|_\infty \|B\|_\infty$ holds verbatim in both cases: for a unital map
$T(1) = 1$, and powers of unital maps are unital. Both cases are therefore
formalized by the same route, through `T.HasBoundedOrbits`.

## Main results

* `IsPositiveMap.hasBoundedOrbits_of_unital`: a positive unital matrix
  endomorphism has bounded forward orbits.
* `IsPositiveMap.no_rank_two_genEigenvector_of_tracePreserving` and
  `IsPositiveMap.no_rank_two_genEigenvector_of_unital`:
  $\ker(T-\lambda)^2 = \ker(T-\lambda)$ when $|\lambda| = 1$.
* `IsPositiveMap.peripheral_Jordan_trivial_of_tracePreserving` and
  `IsPositiveMap.peripheral_Jordan_trivial_of_unital`:
  generalized eigenspace equals eigenspace for peripheral eigenvalues.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.2][Wolf2012QChannels]
* Local source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open Matrix

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

/-! ### Bounded orbits of positive unital maps -/

/-- A positive semidefinite matrix is bounded above by its trace times the
identity matrix in the Loewner order.

Diagonalize `X` by the spectral theorem: the difference
`(trace X) • 1 - X` is unitarily congruent to a diagonal matrix whose entries
are `trace X - λᵢ = ∑_{j ≠ i} λⱼ ≥ 0`, since every eigenvalue `λⱼ` of a
positive semidefinite matrix is nonnegative. -/
private theorem posSemidef_le_trace_smul_one {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X.PosSemidef) :
    X ≤ (X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  rw [Matrix.le_iff]
  set U := hX.1.eigenvectorUnitary
  set c : ℝ := X.trace.re with hc
  have htr : c = ∑ i : Fin D, hX.1.eigenvalues i := by
    rw [hc, hX.1.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  set Dg : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.diagonal fun i : Fin D => ((hX.1.eigenvalues i : ℝ) : ℂ)
  have hsp : X = (U : Matrix (Fin D) (Fin D) ℂ) * Dg * star (U : Matrix (Fin D) (Fin D) ℂ) := by
    have h := hX.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hDgeq : Matrix.diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) = Dg := by
      ext i j
      simp [Dg, Matrix.diagonal_apply, RCLike.ofReal]
    rwa [hDgeq] at h
  have hU1 : (U : Matrix (Fin D) (Fin D) ℂ) * star (U : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.prop
  have hdiag : ((c : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) - Dg).PosSemidef := by
    have hdiag_eq : (c : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) - Dg =
        Matrix.diagonal fun i : Fin D => (((c - hX.1.eigenvalues i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Dg, Matrix.one_apply_eq, Complex.ofReal_sub]
      · simp [Dg, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
    rw [hdiag_eq]
    refine Matrix.PosSemidef.diagonal fun i : Fin D => ?_
    rw [Pi.zero_apply]
    rw [Complex.nonneg_iff]
    refine ⟨?_, by simp⟩
    simp only [Complex.ofReal_re, sub_nonneg]
    rw [htr]
    exact Finset.single_le_sum (fun j _ => hX.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hdecomp : (c : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) - X =
      (U : Matrix (Fin D) (Fin D) ℂ) *
        ((c : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) - Dg) * star (U : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hsp, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU1]
  rw [hdecomp]
  have h := hdiag.conjTranspose_mul_mul_same (star (U : Matrix (Fin D) (Fin D) ℂ))
  have hUU : (star (U : Matrix (Fin D) (Fin D) ℂ))ᴴ = (U : Matrix (Fin D) (Fin D) ℂ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rwa [hUU] at h

/-- The forward orbit of a positive semidefinite matrix under a positive
unital endomorphism is bounded.

Every iterate remains positive semidefinite, and positivity together with
`T 1 = 1` propagates the Loewner bound `T^[n] X ≤ (trace X) • 1`: each iterate
stays in the bounded trace section `{Y | 0 ≤ Y, trace Y ≤ D · trace X}` of the
positive cone.  This is the unital case of Wolf's uniform boundedness
observation in the proof of Proposition 6.2,
`tr[A T(B)] ≤ ‖A‖ ‖B‖ tr[1 T(1)] = d ‖A‖ ‖B‖`, which holds verbatim for
unital positive maps and all their powers.

Source: Wolf, proof of Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 190--199. -/
private theorem isBounded_orbit_of_posSemidef_of_unital
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hT1 : T 1 = 1)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) :
    Bornology.IsBounded (Set.range fun n : ℕ ↦ T^[n] X) := by
  classical
  have htr_nonneg : 0 ≤ X.trace.re := (Complex.nonneg_iff.mp hX.trace_nonneg).1
  have hiter_pos : ∀ n : ℕ, (T^[n] X).PosSemidef := by
    intro n
    induction n with
    | zero => simpa using hX
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hT _ ih
  have hiter_le : ∀ n : ℕ, T^[n] X ≤ (X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    intro n
    induction n with
    | zero => simpa using posSemidef_le_trace_smul_one hX
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc
          T (T^[n] X) ≤ T ((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)) :=
            hT.map_le_map ih
          _ = (X.trace.re : ℝ) • T 1 := LinearMap.map_smul_of_tower T _ _
          _ = (X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by rw [hT1]
  have htrace_top : ((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)).trace =
      (X.trace.re : ℂ) * D := by
    rw [Matrix.trace_smul]
    simp [Matrix.trace_one]
  have hiter_trace : ∀ n : ℕ,
      (T^[n] X).trace ≤ ((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)).trace := by
    intro n
    have hle := hiter_le n
    rw [Matrix.le_iff] at hle
    have h0 := hle.trace_nonneg
    rw [Matrix.trace_sub] at h0
    exact sub_nonneg.mp h0
  have htop_psd : ((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul htr_nonneg
  have hiter_trace_norm : ∀ n : ℕ,
      ‖(T^[n] X).trace‖ ≤ ‖((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)).trace‖ := by
    intro n
    rw [show ‖(T^[n] X).trace‖ = ((T^[n] X).trace).re from by
        simpa using congrArg Complex.re
          (Complex.norm_of_nonneg' (hiter_pos n).trace_nonneg),
      show ‖((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)).trace‖ =
        (((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)).trace).re from by
        simpa using congrArg Complex.re (Complex.norm_of_nonneg' htop_psd.trace_nonneg)]
    rw [← sub_nonneg]
    simpa [map_sub] using (Complex.nonneg_iff.mp (sub_nonneg.mpr (hiter_trace n))).1
  apply (posSemidef_trace_bounded_isBounded
    ‖((X.trace.re : ℝ) • (1 : Matrix (Fin D) (Fin D) ℂ)).trace‖).subset
  intro Y hY
  obtain ⟨n, rfl⟩ := hY
  exact ⟨hiter_pos n, hiter_trace_norm n⟩

/-- A positive unital endomorphism of a finite-dimensional complex matrix
algebra has bounded forward orbits on every matrix.

Wolf's proof of Proposition 6.2 bounds `tr[A T(B)]` uniformly over the powers
of any trace-preserving **or unital** positive map; for a unital map
`tr[1 T(1)] = tr[1] = d`, so the same uniform bound applies.  The positive
semidefinite orbit bound above is lifted to all matrices by Hermitian
decomposition (`hasBoundedOrbits_of_posSemidef_orbit_bounded`).

Source: Wolf, proof of Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 190--199. -/
theorem hasBoundedOrbits_of_unital
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hT1 : T 1 = 1) :
    T.HasBoundedOrbits :=
  hT.hasBoundedOrbits_of_posSemidef_orbit_bounded fun hX =>
    hT.isBounded_orbit_of_posSemidef_of_unital hT1 hX

/-- **Wolf Proposition 6.2** (shared key step): For a positive map with
bounded orbits, no rank-2 generalized eigenvector exists at a peripheral
eigenvalue.

If $(T-\lambda)^2 X = 0$ with $|\lambda| = 1$, then $(T-\lambda)X = 0$.

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
private theorem no_rank_two_genEigenvector_of_hasBoundedOrbits
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hbounded : T.HasBoundedOrbits)
    (μ : ℂ) (hμ_norm : ‖μ‖ = 1) (X : Matrix (Fin D) (Fin D) ℂ)
    (hN2 : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) ^ 2) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) X = 0 := by
  set N := T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
  by_contra h_not
  have hNX_ne_zero : N X ≠ 0 := h_not
  have hNX_norm_pos : 0 < ‖N X‖ := norm_pos_iff.mpr hNX_ne_zero
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

/-- **Wolf Proposition 6.2** (key step, trace-preserving case): For a positive
trace-preserving map, no rank-2 generalized eigenvector exists at a peripheral
eigenvalue.

If $(T-\lambda)^2 X = 0$ with $|\lambda| = 1$, then $(T-\lambda)X = 0$.

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
theorem no_rank_two_genEigenvector_of_tracePreserving
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (μ : ℂ) (hμ_norm : ‖μ‖ = 1) (X : Matrix (Fin D) (Fin D) ℂ)
    (hN2 : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) ^ 2) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) X = 0 :=
  no_rank_two_genEigenvector_of_hasBoundedOrbits
    (hPos.hasBoundedOrbits_of_tracePreserving hTP) μ hμ_norm X hN2

/-- **Wolf Proposition 6.2** (key step, unital case): For a positive unital
map, no rank-2 generalized eigenvector exists at a peripheral eigenvalue.

If $(T-\lambda)^2 X = 0$ with $|\lambda| = 1$, then $(T-\lambda)X = 0$.

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
theorem no_rank_two_genEigenvector_of_unital
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hT1 : T 1 = 1)
    (μ : ℂ) (hμ_norm : ‖μ‖ = 1) (X : Matrix (Fin D) (Fin D) ℂ)
    (hN2 : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) ^ 2) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) X = 0 :=
  no_rank_two_genEigenvector_of_hasBoundedOrbits
    (hPos.hasBoundedOrbits_of_unital hT1) μ hμ_norm X hN2

/-- **Wolf Proposition 6.2** (full statement, shared form): For a positive map
with bounded orbits, the generalized eigenspace for any peripheral eigenvalue
$\lambda$ equals the eigenspace: $\ker(T-\lambda)^k = \ker(T-\lambda)$ for all
$k \ge 1$.

In other words, peripheral eigenvalues have trivial Jordan blocks
(algebraic multiplicity equals geometric multiplicity).

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
private theorem peripheral_Jordan_trivial_of_hasBoundedOrbits
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hbounded : T.HasBoundedOrbits)
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
        no_rank_two_genEigenvector_of_hasBoundedOrbits hbounded μ hμ_norm Y hN2_Y
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

/-- **Wolf Proposition 6.2** (full statement, trace-preserving case): For a
positive trace-preserving map, the generalized eigenspace for any peripheral
eigenvalue $\lambda$ equals the eigenspace: $\ker(T-\lambda)^k =
\ker(T-\lambda)$ for all $k \ge 1$.

In other words, peripheral eigenvalues have trivial Jordan blocks
(algebraic multiplicity equals geometric multiplicity).

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
theorem peripheral_Jordan_trivial_of_tracePreserving
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (μ : ℂ) (hμ_norm : ‖μ‖ = 1) (k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hNk : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) ^ k) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) X = 0 :=
  peripheral_Jordan_trivial_of_hasBoundedOrbits
    (hPos.hasBoundedOrbits_of_tracePreserving hTP) μ hμ_norm k X hNk

/-- **Wolf Proposition 6.2** (full statement, unital case): For a positive
unital map, the generalized eigenspace for any peripheral eigenvalue
$\lambda$ equals the eigenspace: $\ker(T-\lambda)^k = \ker(T-\lambda)$ for
all $k \ge 1$.

In other words, peripheral eigenvalues have trivial Jordan blocks
(algebraic multiplicity equals geometric multiplicity).

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.2; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 181--224. -/
theorem peripheral_Jordan_trivial_of_unital
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hT1 : T 1 = 1)
    (μ : ℂ) (hμ_norm : ‖μ‖ = 1) (k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hNk : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) ^ k) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)) X = 0 :=
  peripheral_Jordan_trivial_of_hasBoundedOrbits
    (hPos.hasBoundedOrbits_of_unital hT1) μ hμ_norm k X hNk


end IsPositiveMap
