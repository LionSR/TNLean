/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic

/-!
# Newton–Girard: power sums determine a multiset of complex numbers

This module proves the **Newton–Girard multiplicity-recovery lemma**: if
two multisets of complex numbers have the same cardinality and the same
power-sum sequence
`∑_{a ∈ s} a^N` for every `N : ℕ`, they are equal as multisets.

This is the algebraic input behind the CPSV16 §II equal-MPV multiplicity
matching step.  After the dominant BNT block on the two sides is identified,
the equal-MPV identity restricted to that block reads
`∑_q μ_{j,q}^N = ∑_q ν_{j,q}^N e^{i\phi_j N}` for every `N`
(CPSV16 lines 1184–1188, around the snippet
`From this equation it follows that r_{a,j}=r_{b,j}=:r_j and
\mu_{j,q}=\nu_{j,q}e^{i\phi_j}`).  Reading both sides as power sums of
multisets `{μ_{j,q}}_q` and `{ν_{j,q} e^{i\phi_j}}_q`, the Newton–Girard
multiset equality below forces the two multisets to agree, hence the
within-sector multiplicities `r_j` match and the within-sector weights are
related by `μ_{j,q} = ν_{j,σ_j(q)} e^{i\phi_j}` for some permutation `σ_j`.

## Strategy

The proof proceeds through three classical steps:

1. **Newton's identity at the multiset level.**  Mathlib's
   `MvPolynomial.mul_esymm_eq_sum` gives the universal identity
   `k · e_k = (-1)^{k+1} ∑_{i + j = k, i < k} (-1)^i e_i p_j`
   in `MvPolynomial σ R`.  Specialising to
   `σ = Fin (s.toList.length)` and applying `MvPolynomial.aeval` to the
   index function `s.toList.get` translates this to a recurrence between
   the multiset elementary symmetric polynomial `Multiset.esymm s k` and
   the multiset power sum `(s.map (· ^ j)).sum`.

2. **Power sums determine elementary symmetric polynomials.**  Strong
   induction on `k` using Newton's identity: the recurrence carries the
   factor `(k : ℂ)`, and complex multiplication by a nonzero natural
   number is cancellable (the complex field has characteristic zero), so
   equal power sums force equal elementary symmetric polynomials.

3. **Elementary symmetric polynomials determine the multiset.**  Vieta's
   formula `Multiset.prod_X_sub_C_coeff` and
   `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card` express the
   coefficients of `(s.map (X - C ·)).prod : ℂ[X]` in terms of `s.esymm`.
   Once these polynomials coincide for `s` and `t`, the roots multiset
   recovery `Polynomial.roots_multiset_prod_X_sub_C` extracts `s = t`.

## Main result

* `Multiset.eq_of_power_sum_eq` — two multisets of complex numbers with
  equal cardinality and equal power sums of every degree are equal.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and
  Boundary Theories*, arXiv:1606.00608.  Lines 1184–1188:
  multiplicity recovery from equality of raw power sums of within-sector
  weights, the algebraic step Newton–Girard discharges.
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix product states and projected entangled pair states*,
  arXiv:2011.12127.  Lines 1846–1884 (raw two-layer BNT decomposition
  `∑_q μ_{j,q}^N`, the same multiset shape Newton–Girard consumes).

## Tags

Newton identities, multiset, power sum, elementary symmetric function,
multiplicity recovery
-/

open scoped BigOperators

namespace MPSTensor

namespace NewtonGirard

open Multiset Finset Polynomial MvPolynomial

/-- Index a multiset by `Fin s.toList.length` via the list realisation
`s.toList`.  This is the cleanest interface to feed a multiset into the
`MvPolynomial` symmetric-function API, since `s.toList.get` is a
`Fin s.toList.length → ℂ`. -/
private noncomputable def enum (s : Multiset ℂ) : Fin s.toList.length → ℂ :=
  s.toList.get

/-- The multiset image of the enumeration `enum s` recovers `s`. -/
private lemma enum_image (s : Multiset ℂ) :
    Multiset.map (enum s) (Finset.univ : Finset (Fin s.toList.length)).val = s := by
  classical
  -- `univ.val.map f = ↑(List.ofFn f)`; `List.ofFn (l.get) = l`; `↑s.toList = s`.
  have h1 :
      Multiset.map (enum s) (Finset.univ : Finset (Fin s.toList.length)).val
        = ((List.ofFn (enum s) : List ℂ) : Multiset ℂ) := by
    rw [Fin.univ_val_map]
  have h2 : List.ofFn (enum s) = s.toList := List.ofFn_get s.toList
  rw [h1, h2, Multiset.coe_toList]

/-- The `aeval`-pullback of the MvPolynomial elementary symmetric
polynomial along `enum s` equals the multiset elementary symmetric
polynomial `s.esymm k`. -/
private lemma aeval_esymm_enum (s : Multiset ℂ) (k : ℕ) :
    (MvPolynomial.aeval (enum s)) (MvPolynomial.esymm (Fin s.toList.length) ℂ k)
      = s.esymm k := by
  classical
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, enum_image]

/-- The `aeval`-pullback of the MvPolynomial power-sum polynomial along
`enum s` equals the multiset power sum `(s.map (· ^ n)).sum`. -/
private lemma aeval_psum_enum (s : Multiset ℂ) (n : ℕ) :
    (MvPolynomial.aeval (enum s)) (MvPolynomial.psum (Fin s.toList.length) ℂ n)
      = (s.map (· ^ n)).sum := by
  classical
  unfold MvPolynomial.psum
  rw [map_sum]
  simp only [map_pow, MvPolynomial.aeval_X]
  -- LHS: `∑ i : Fin s.toList.length, (enum s i)^n`.  We compute this as
  -- `(Multiset.map (·^n) (Multiset.map (enum s) Finset.univ.val)).sum`
  -- using `Finset.sum_eq_multiset_sum` and `Multiset.map_map`, then apply
  -- `enum_image`.
  have hsum :
      ∑ i : Fin s.toList.length, (enum s i) ^ n
        = (Multiset.map (fun i : Fin s.toList.length => (enum s i) ^ n)
              (Finset.univ : Finset (Fin s.toList.length)).val).sum := by
    rfl
  rw [hsum]
  -- Push the `(· ^ n)` map outside.
  have hmap :
      Multiset.map (fun i : Fin s.toList.length => (enum s i) ^ n)
          (Finset.univ : Finset (Fin s.toList.length)).val
        = Multiset.map (· ^ n)
            (Multiset.map (enum s) (Finset.univ : Finset (Fin s.toList.length)).val) := by
    rw [Multiset.map_map]
    rfl
  rw [hmap, enum_image]

/-- **Multiset-level Newton identity.**

Specialisation of `MvPolynomial.mul_esymm_eq_sum` to a multiset of complex
numbers via `MvPolynomial.aeval (enum s)`.  This recurrence is what
forces equal power sums to imply equal elementary symmetric polynomials.

Paper anchor: CPSV16 lines 1184–1188 — the algebraic content behind the
"power sums match ⇒ multisets match" step. -/
private lemma multiset_mul_esymm_eq_sum (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  classical
  -- Start from the symbolic identity in `MvPolynomial (Fin s.toList.length) ℂ`.
  have hsym := MvPolynomial.mul_esymm_eq_sum (Fin s.toList.length) ℂ k
  -- Apply `aeval (enum s)` to both sides.
  have h := congrArg ((MvPolynomial.aeval (enum s)).toFun) hsym
  -- Compute the image of both sides.
  -- LHS: `aeval (enum s) (k * esymm σ ℂ k) = (k : ℂ) * s.esymm k`.
  have hL :
      (MvPolynomial.aeval (enum s)).toFun
          (((k : ℕ) : MvPolynomial (Fin s.toList.length) ℂ) *
            MvPolynomial.esymm (Fin s.toList.length) ℂ k)
        = (k : ℂ) * s.esymm k := by
    -- `(MvPolynomial.aeval f).toFun = ⇑(MvPolynomial.aeval f)`
    change (MvPolynomial.aeval (enum s)) _ = _
    rw [map_mul, map_natCast, aeval_esymm_enum]
  -- RHS: `aeval (enum s) ((-1)^(k+1) * ∑ ...) = (-1)^(k+1) * ∑ ...`.
  have hR :
      (MvPolynomial.aeval (enum s)).toFun
          ((-1 : MvPolynomial (Fin s.toList.length) ℂ) ^ (k + 1) *
            ∑ a ∈ Finset.antidiagonal k with a.1 < k,
              (-1) ^ a.1 *
                MvPolynomial.esymm (Fin s.toList.length) ℂ a.1 *
                MvPolynomial.psum (Fin s.toList.length) ℂ a.2)
        = (-1) ^ (k + 1) *
            ∑ a ∈ Finset.antidiagonal k with a.1 < k,
              (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
    change (MvPolynomial.aeval (enum s)) _ = _
    rw [map_mul, map_pow, map_neg, map_one]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [map_mul, map_mul, map_pow, map_neg, map_one,
      aeval_esymm_enum, aeval_psum_enum]
  -- Combine.
  rw [hL, hR] at h
  exact h

/-- **Power sums determine elementary symmetric polynomials (multiset, ℂ).**

If `Multiset.card s = Multiset.card t` and all multiset power sums of `s`
and `t` agree, then all multiset elementary symmetric polynomials agree.

The proof is strong induction on the degree `k`, using
`multiset_mul_esymm_eq_sum`: the recurrence in lower-degree esymms and
power sums, with the `(k : ℂ)` factor cancellable since `ℂ` has
characteristic zero. -/
private lemma esymm_eq_of_power_sum_eq (s t : Multiset ℂ)
    (hpow : ∀ N : ℕ, (s.map (· ^ N)).sum = (t.map (· ^ N)).sum) :
    ∀ k : ℕ, s.esymm k = t.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    by_cases hk : k = 0
    · subst hk
      simp [Multiset.esymm]
    -- `k ≥ 1`: divide Newton's identity by `(k : ℂ) ≠ 0`.
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk_pos.ne'
    have hs := multiset_mul_esymm_eq_sum s k
    have ht := multiset_mul_esymm_eq_sum t k
    -- Show RHS for `s` = RHS for `t`.
    have hRHS_eq :
        ((-1 : ℂ) ^ (k + 1) *
          ∑ a ∈ Finset.antidiagonal k with a.1 < k,
            (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum)
          =
        ((-1 : ℂ) ^ (k + 1) *
          ∑ a ∈ Finset.antidiagonal k with a.1 < k,
            (-1) ^ a.1 * t.esymm a.1 * (t.map (· ^ a.2)).sum) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro a ha
      have ha_lt : a.1 < k := by
        rw [Finset.mem_filter] at ha
        exact ha.2
      have ha_esymm : s.esymm a.1 = t.esymm a.1 := IH a.1 ha_lt
      have ha_pow : (s.map (· ^ a.2)).sum = (t.map (· ^ a.2)).sum := hpow a.2
      rw [ha_esymm, ha_pow]
    have hkeq : (k : ℂ) * s.esymm k = (k : ℂ) * t.esymm k := by
      rw [hs, ht]; exact hRHS_eq
    exact mul_left_cancel₀ hkne hkeq

/-- **Newton–Girard multiplicity recovery for multisets of complex numbers.**

Two multisets `a, b : Multiset ℂ` of equal cardinality whose power sums
`∑_{x ∈ a} x^N = ∑_{x ∈ b} x^N` agree for every `N : ℕ` are equal.

Paper anchor: CPSV16 lines 1184–1188 — once the dominant BNT block has
been matched on both sides and the equal-MPV identity has been projected
onto that block, the within-sector weight multisets `{μ_{j,q}}_q` and
`{ν_{j,q} e^{i\phi_j}}_q` admit equal power sums of every degree.  This
lemma is the algebraic input that forces equality of these multisets,
recovering the matched within-sector multiplicity `r_j`.

The proof is by Newton–Girard: equality of power sums propagates to
equality of elementary symmetric polynomials
(`esymm_eq_of_power_sum_eq`), from which Vieta's formula for the
coefficients of `(a.map (X - C ·)).prod` forces equality of the
associated monic polynomials, and `roots_multiset_prod_X_sub_C` recovers
the multiset of roots. -/
theorem Multiset.eq_of_power_sum_eq (a b : Multiset ℂ)
    (h_card : Multiset.card a = Multiset.card b)
    (hPow : ∀ N : ℕ, (a.map (· ^ N)).sum = (b.map (· ^ N)).sum) : a = b := by
  classical
  -- Step 1: esymm equal for all degrees.
  have hesymm : ∀ k : ℕ, a.esymm k = b.esymm k :=
    esymm_eq_of_power_sum_eq a b hPow
  -- Step 2: build the polynomials `(·.map (X - C ·)).prod` for `a` and `b`,
  -- and show their coefficients agree at every degree.
  let fA : ℂ[X] := (a.map (fun x : ℂ => Polynomial.X - Polynomial.C x)).prod
  let fB : ℂ[X] := (b.map (fun x : ℂ => Polynomial.X - Polynomial.C x)).prod
  have hdegA : fA.natDegree = Multiset.card a :=
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card a
  have hdegB : fB.natDegree = Multiset.card b :=
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card b
  have hAB_eq : fA = fB := by
    refine Polynomial.ext (fun k => ?_)
    by_cases hk_a : k ≤ Multiset.card a
    · have hk_b : k ≤ Multiset.card b := h_card ▸ hk_a
      have hAcoeff : fA.coeff k =
          (-1) ^ (Multiset.card a - k) * a.esymm (Multiset.card a - k) :=
        Multiset.prod_X_sub_C_coeff a hk_a
      have hBcoeff : fB.coeff k =
          (-1) ^ (Multiset.card b - k) * b.esymm (Multiset.card b - k) :=
        Multiset.prod_X_sub_C_coeff b hk_b
      rw [hAcoeff, hBcoeff, h_card, hesymm (Multiset.card b - k)]
    · -- `k > card a = card b`, so both coefficients vanish.
      push Not at hk_a
      have hk_b : Multiset.card b < k := h_card ▸ hk_a
      have hAzero : fA.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hdegA]; exact hk_a
      have hBzero : fB.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hdegB]; exact hk_b
      rw [hAzero, hBzero]
  -- Step 3: recover `a` and `b` as the roots multisets.
  have hrootsA : fA.roots = a := Polynomial.roots_multiset_prod_X_sub_C a
  have hrootsB : fB.roots = b := Polynomial.roots_multiset_prod_X_sub_C b
  calc a = fA.roots := hrootsA.symm
    _ = fB.roots := by rw [hAB_eq]
    _ = b := hrootsB

end NewtonGirard

end MPSTensor
