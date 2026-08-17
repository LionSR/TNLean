/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ZModCyclicSums
import TNLean.Analysis.ProjectionGeometry

/-!
# Finite-range Knabe inequality for cyclic families of projections

This file develops the Knabe open-to-periodic gap transfer for an abstract
one-dimensional cyclic family of symmetric projections with a finite
interaction range `R`.

Let `h i` be symmetric projections indexed by the cyclic group `ZMod N`, and
write \(H=\sum_i h_i\). For \(m\geq R\), define the window sum
\(A_s=\sum_{q=0}^{m-1}h_{s+q}\), represented by `cyclicWindowSum h m s`.
Suppose every window satisfies
\(\gamma\,\operatorname{Re}\langle A_s v,v\rangle\leq
\operatorname{Re}\langle A_s v,A_s v\rangle\), uniformly in \(s\) and \(v\).
If terms at cyclic separation at least \(R\) commute pointwise and \(N\geq2m\),
then
\(\delta\,\operatorname{Re}\langle Hv,v\rangle\leq
\operatorname{Re}\langle Hv,Hv\rangle\), where
\(\delta=(m\gamma-(R-1)^2)/(m-R+1)\), whenever
\((R-1)^2<m\gamma\).

For \(R=2\), this recovers Knabe's nearest-neighbor coefficient
\((m\gamma-1)/(m-1)\).

## Sources

The nearest-neighbor threshold `γ > 1 / m` goes back to Knabe, J. Stat. Phys.
52, 627 (1988) (`Knabe1988Energy`); the same criterion is stated in
Pérez-García et al., arXiv:quant-ph/0608197, lines 1483-1489, and in
Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, lines 2194-2197
(paragraph "The Knabe bound").  The finite-range coefficient above is a
TNLean derivation obtained by running Knabe's window argument with a general
range; it is recorded in the note
`docs/paper-gaps/knabe_finite_range_coefficient.tex`, is not stated in any of
the cited sources, and is not attributed to any of them.

## Main results

* `ProjectionGeometry.cyclicWindowSum_sq_sum_eq`: the cyclic double-counting
  identity `∑ s A s ^ 2 = m • H + ∑ e (m - e) • Q e`.
* `ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe`: the
  finite-range Knabe inequality.
* `ProjectionGeometry.quadraticForm_sum_projections_of_cyclic_knabe_nearest_neighbor`:
  the nearest-neighbor specialization `R = 2`.
-/

open scoped InnerProductSpace

namespace ProjectionGeometry




section CyclicFamily

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {N : ℕ} [NeZero N]

/-- The sum of `m` consecutive terms of a cyclic family, starting at `s`. -/
def cyclicWindowSum (h : ZMod N → E →ₗ[𝕜] E) (m : ℕ) (s : ZMod N) : E →ₗ[𝕜] E :=
  ∑ q : Fin m, h (s + (q : ℕ))

/-- The operator cross terms of a cyclic family at offset `e`. -/
def cyclicCrossTerms (h : ZMod N → E →ₗ[𝕜] E) (e : ℕ) : E →ₗ[𝕜] E :=
  ∑ i : ZMod N, (h i * h (i + e) + h i * h (i - e))

/-- Cyclic expansion of the sum of squared windows. If `H = ∑ i, h i` and
`Q e = cyclicCrossTerms h e`, then
`∑ s, (cyclicWindowSum h m s) ^ 2 = m • H + ∑ e, (m - e) • Q e`. -/
theorem cyclicWindowSum_sq_sum_eq (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) (m : ℕ) :
    (∑ s : ZMod N, cyclicWindowSum h m s * cyclicWindowSum h m s) =
      m • ∑ i : ZMod N, h i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) • cyclicCrossTerms h e := by
  classical
  have hWindow : ∀ s : ZMod N, cyclicWindowSum h m s =
      ∑ q ∈ Finset.range m, h (s + q) := by
    intro s
    rw [cyclicWindowSum]
    exact Fin.sum_univ_eq_sum_range (fun q : ℕ => h (s + (q : ZMod N))) m
  have hDiag : ∀ i : ZMod N, h i * h i = h i := by
    intro i
    ext v
    exact LinearMap.IsIdempotentElem.apply_apply (hh i).isIdempotentElem v
  calc
    (∑ s : ZMod N, cyclicWindowSum h m s * cyclicWindowSum h m s) =
        ∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
          h (s + q) * h (s + q') := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hWindow s, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
    _ = m • ∑ i : ZMod N, h i * h i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) •
          ∑ i : ZMod N, (h i * h (i + e) + h i * h (i - e)) :=
      ZModCyclicSums.sum_cyclic_window_eq (fun i j => h i * h j) m
    _ = m • ∑ i : ZMod N, h i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) • cyclicCrossTerms h e := by
      rw [Finset.sum_congr rfl fun i _ => hDiag i]
      rfl

/-- The ordered real cross terms of a cyclic family at offset `e`: the sum over
all sites of the two ordered quadratic forms of the pairs at cyclic offsets
`e` and `-e`. -/
def reInnerCyclicCrossTerms (h : ZMod N → E →ₗ[𝕜] E) (e : ℕ) (v : E) : ℝ :=
  ∑ i : ZMod N, (RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 + RCLike.re ⟪h i v, h (i - e) v⟫_𝕜)

/-- For a cyclic family of symmetric projections, the real cross-term sum is
the quadratic form of the corresponding cross-term operator. -/
theorem reInnerCyclicCrossTerms_eq_re_inner_cyclicCrossTerms
    (h : ZMod N → E →ₗ[𝕜] E) (hh : ∀ i, (h i).IsSymmetricProjection)
    (e : ℕ) (v : E) :
    reInnerCyclicCrossTerms h e v = RCLike.re ⟪cyclicCrossTerms h e v, v⟫_𝕜 := by
  classical
  unfold reInnerCyclicCrossTerms cyclicCrossTerms
  simp only [LinearMap.sum_apply, LinearMap.add_apply, sum_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 + RCLike.re ⟪h i v, h (i - e) v⟫_𝕜 =
    RCLike.re ⟪h i (h (i + e) v) + h i (h (i - e) v), v⟫_𝕜
  rw [inner_add_left, map_add, (hh i).isSymmetric (h (i + e) v) v,
    (hh i).isSymmetric (h (i - e) v) v,
    ← inner_conj_symm (h i v) (h (i + e) v),
    ← inner_conj_symm (h i v) (h (i - e) v), RCLike.conj_re, RCLike.conj_re]

/-- The cyclic double-counting identity for a family of symmetric projections:
summing the quadratic form of every window of `m` consecutive terms produces
the diagonal with multiplicity `m` and each offset pair of cross terms with
multiplicity `m - e`. -/
theorem re_inner_cyclicWindowSum_sum_eq (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) (m : ℕ) (v : E) :
    (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜) =
      m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
        ∑ e ∈ Finset.Ico 1 m, (m - e) * reInnerCyclicCrossTerms h e v := by
  classical
  have hExpand : ∀ s : ZMod N,
      RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜 =
        ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
          RCLike.re ⟪h (s + q) v, h (s + q') v⟫_𝕜 := by
    intro s
    rw [cyclicWindowSum, re_inner_sum_apply_apply,
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => ∑ q' : Fin m,
          RCLike.re ⟪h (s + (k : ZMod N)) v, h (s + ((q' : ℕ) : ZMod N)) v⟫_𝕜) m]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact Fin.sum_univ_eq_sum_range
      (fun k' : ℕ => RCLike.re ⟪h (s + (q : ZMod N)) v, h (s + (k' : ZMod N)) v⟫_𝕜) m
  set T : ZMod N → ZMod N → ℝ := fun i j => RCLike.re ⟪h i v, h j v⟫_𝕜 with hT
  have hDiag : (∑ i : ZMod N, T i i) = RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
    rw [hT]
    rw [re_inner_sum_apply_left h v]
    exact Finset.sum_congr rfl fun i _ => (hh i).re_inner_apply_apply_self v
  calc (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜)
      = ∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
          T (s + q) (s + q') :=
        Finset.sum_congr rfl fun s _ => hExpand s
    _ = m • ∑ i : ZMod N, T i i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, (T i (i + e) + T i (i - e)) :=
        ZModCyclicSums.sum_cyclic_window_eq T m
    _ = m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
        ∑ e ∈ Finset.Ico 1 m, (m - e) * reInnerCyclicCrossTerms h e v := by
        rw [hDiag, nsmul_eq_mul]
        have hsmulB : ∀ e ∈ Finset.Ico 1 m,
            ((m - e : ℕ) • (∑ i : ZMod N, (T i (i + e) + T i (i - e)))) =
              ((m : ℝ) - (e : ℝ)) * reInnerCyclicCrossTerms h e v := by
          intro e he
          simp only [Finset.mem_Ico] at he
          rw [nsmul_eq_mul, Nat.cast_sub (by omega)]
          rfl
        refine congrArg _ ?_
        exact Finset.sum_congr rfl hsmulB

/-- Summing the quadratic forms of all windows counts every site `m` times. -/
theorem re_inner_cyclicWindowSum_sum_apply (h : ZMod N → E →ₗ[𝕜] E) (m : ℕ) (v : E) :
    (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) =
      m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
  classical
  have hExpand : ∀ s : ZMod N,
      RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜 =
        ∑ q : Fin m, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜 := by
    intro s
    simp only [cyclicWindowSum, re_inner_sum_apply_left]
  have h1 : (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) =
      ∑ s : ZMod N, ∑ q : Fin m, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜 :=
    Finset.sum_congr rfl fun s _ => hExpand s
  have hswap : (∑ s : ZMod N, ∑ q : Fin m, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜) =
      ∑ q : Fin m, ∑ s : ZMod N, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜 := Finset.sum_comm
  rw [h1, hswap]
  have hTrans : ∀ q : Fin m, (∑ s : ZMod N, RCLike.re ⟪h (s + (q : ℕ)) v, v⟫_𝕜) =
      RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
    intro q
    have hTra := ZModCyclicSums.sum_comp_addRight (M := ℝ)
      (fun u : ZMod N => RCLike.re ⟪h u v, v⟫_𝕜) ((q : ℕ) : ZMod N)
    rw [hTra]
    exact (re_inner_sum_apply_left h v).symm
  rw [Finset.sum_congr rfl fun q _ => hTrans q]
  simp

/-- The pairwise anticommutator bound, summed over the ring: the cross terms at
any offset are bounded by twice the total quadratic form. -/
theorem re_inner_cyclicCrossTerms_le_two (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) (e : ℕ) (v : E) :
    reInnerCyclicCrossTerms h e v ≤ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
  classical
  have hPair : ∀ i : ZMod N,
      RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 + RCLike.re ⟪h (i + e) v, h i v⟫_𝕜 ≤
        RCLike.re ⟪h i v, v⟫_𝕜 + RCLike.re ⟪h (i + e) v, v⟫_𝕜 :=
    fun i => LinearMap.IsSymmetricProjection.re_inner_anticommutator_le (hh i)
      (hh (i + e)) v
  -- The reversed ordered pair is a translate of the pair at offset `-e`.
  have hTrans : (∑ i : ZMod N, RCLike.re ⟪h (i + e) v, h i v⟫_𝕜) =
      ∑ i : ZMod N, RCLike.re ⟪h i v, h (i - e) v⟫_𝕜 := by
    refine Fintype.sum_equiv (Equiv.addRight ((e : ZMod N))) _ _ fun i => ?_
    change RCLike.re ⟪h (i + e) v, h i v⟫_𝕜 = RCLike.re ⟪h (i + e) v, h ((i + e) - e) v⟫_𝕜
    abel_nf
  have hDiag : (∑ i : ZMod N, RCLike.re ⟪h (i + e) v, v⟫_𝕜) =
      ∑ i : ZMod N, RCLike.re ⟪h i v, v⟫_𝕜 :=
    ZModCyclicSums.sum_comp_addRight (fun u : ZMod N => RCLike.re ⟪h u v, v⟫_𝕜) _
  have hSplit : reInnerCyclicCrossTerms h e v =
      (∑ i : ZMod N, (RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 +
        RCLike.re ⟪h (i + e) v, h i v⟫_𝕜)) := by
    unfold reInnerCyclicCrossTerms
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hTrans]
  calc reInnerCyclicCrossTerms h e v
      = (∑ i : ZMod N, (RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 +
        RCLike.re ⟪h (i + e) v, h i v⟫_𝕜)) := hSplit
    _ ≤ (∑ i : ZMod N, (RCLike.re ⟪h i v, v⟫_𝕜 +
        RCLike.re ⟪h (i + e) v, v⟫_𝕜)) :=
        Finset.sum_le_sum fun i _ => hPair i
    _ = (∑ i : ZMod N, RCLike.re ⟪h i v, v⟫_𝕜) +
        ∑ i : ZMod N, RCLike.re ⟪h (i + e) v, v⟫_𝕜 :=
        Finset.sum_add_distrib
    _ = 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
        rw [hDiag, ← Finset.sum_add_distrib, re_inner_sum_apply_left h v, two_mul,
          ← Finset.sum_add_distrib]

/-- Terms at cyclic separation at least `R` commute pointwise; commuting
symmetric projections have nonnegative ordered cross terms, so both legs of the
cross terms at an offset between `R` and `N - R` are nonnegative. -/
theorem re_inner_cyclicCrossTerms_nonneg (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) {R : ℕ}
    (hcomm : ∀ d : ℕ, R ≤ d → d + R ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    {e : ℕ} (he1 : R ≤ e) (he2 : e + R ≤ N) (v : E) :
    0 ≤ reInnerCyclicCrossTerms h e v := by
  have h1 : ∀ i : ZMod N, 0 ≤ RCLike.re ⟪h i v, h (i + e) v⟫_𝕜 :=
    fun i => LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
      (hh i) (hh (i + e)) (hcomm e he1 he2 i) v
  have h2 : ∀ i : ZMod N, 0 ≤ RCLike.re ⟪h i v, h (i - e) v⟫_𝕜 := by
    intro i
    have hshift : (i - (e : ZMod N)) = (i + ((N - e : ℕ) : ZMod N)) := by
      have hzero : (((e : ZMod N)) + ((N - e : ℕ) : ZMod N)) = 0 := by
        have hsum : e + (N - e) = N := by omega
        rw [← Nat.cast_add, hsum, ZMod.natCast_self]
      have hneg : ((N - e : ℕ) : ZMod N) = -((e : ZMod N)) :=
        eq_neg_of_add_eq_zero_right hzero
      rw [sub_eq_add_neg, hneg]
    rw [hshift]
    exact LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
      (hh i) (hh (i + ((N - e : ℕ) : ZMod N))) (hcomm (N - e) (by omega) (by omega) i) v
  exact Finset.sum_nonneg fun i _ => add_nonneg (h1 i) (h2 i)

/-- The diagonal-plus-cross-terms lower bound on the total square.  Expanding
`Re ⟪H v, H v⟫` over ordered pairs and grouping by cyclic offset, the offsets
between `m` and `N - m` carry nonnegative cross terms (they are at separation
at least `R`), so the total square dominates the diagonal plus the short cross
terms. -/
theorem re_inner_sum_two_ge_sum_cyclicCrossTerms (h : ZMod N → E →ₗ[𝕜] E)
    (hh : ∀ i, (h i).IsSymmetricProjection) {R m : ℕ}
    (hm1 : 1 ≤ m) (hN : 2 * m ≤ N) (hRm : R ≤ m)
    (hcomm : ∀ d : ℕ, R ≤ d → d + R ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    (v : E) :
    RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 + ∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
  classical
  set T : ZMod N → ZMod N → ℝ := fun i j => RCLike.re ⟪h i v, h j v⟫_𝕜 with hT
  -- Expand over ordered pairs and translate the second site.
  have hInner : ∀ i : ZMod N, (∑ j : ZMod N, T i j) = ∑ u : ZMod N, T i (i + u) := by
    intro i
    exact (Equiv.sum_comp (Equiv.addLeft i) (T i)).symm
  -- Split off the zero offset.
  have hSplit0 : ∀ i : ZMod N, (∑ u : ZMod N, T i (i + u)) = T i i +
      ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), T i (i + u) := by
    intro i
    have hEq : (∑ u : ZMod N, T i (i + u)) =
        T i (i + 0) + ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), T i (i + u) := by
      have hU : (Finset.univ : Finset (ZMod N)) =
          insert (0 : ZMod N) (Finset.univ.erase (0 : ZMod N)) :=
        (Finset.insert_erase (Finset.mem_univ 0)).symm
      calc (∑ u : ZMod N, T i (i + u))
          = (∑ u ∈ insert (0 : ZMod N) (Finset.univ.erase (0 : ZMod N)), T i (i + u)) := by
            rw [← hU]
        _ = T i (i + 0) + ∑ u ∈ Finset.univ.erase (0 : ZMod N), T i (i + u) :=
            Finset.sum_insert (by simp)
    rw [hEq, add_zero]
  -- Partition the nonzero offsets.
  set F : ZMod N → ℝ := fun u => ∑ i : ZMod N, T i (i + u) with hF
  have hPart := ZModCyclicSums.sum_offset_partition F hm1 hN
  -- The middle offsets carry nonnegative cross terms.
  have hMidNonneg : 0 ≤ ∑ k ∈ Finset.Ico m (N - m + 1), F k := by
    refine Finset.sum_nonneg fun k hk => Finset.sum_nonneg fun i _ => ?_
    simp only [Finset.mem_Ico] at hk
    exact LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
      (hh i) (hh (i + k)) (hcomm k (by omega) (by omega) i) v
  -- The reflected short offsets reproduce the second leg of the cross terms.
  have hCross : ∀ e ∈ Finset.Ico 1 m,
      F ((e : ZMod N)) + F ((N - e : ℕ) : ZMod N) =
        reInnerCyclicCrossTerms h e v := by
    intro e he
    simp only [Finset.mem_Ico] at he
    have hshift : (∑ i : ZMod N, T i (i + ((N - e : ℕ) : ZMod N))) =
        ∑ i : ZMod N, T i (i - e) := by
      have hneg : ((N - e : ℕ) : ZMod N) = -((e : ZMod N)) := by
        have hzero : (((e : ZMod N)) + ((N - e : ℕ) : ZMod N)) = 0 := by
          have hsum : e + (N - e) = N := by omega
          rw [← Nat.cast_add, hsum, ZMod.natCast_self]
        exact eq_neg_of_add_eq_zero_right hzero
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hneg, sub_eq_add_neg]
    change (∑ i : ZMod N, T i (i + ((e : ZMod N)))) +
        (∑ i : ZMod N, T i (i + ((N - e : ℕ) : ZMod N))) = _
    rw [hshift, ← Finset.sum_add_distrib]
    rfl
  calc RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 + ∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v
      = (∑ i : ZMod N, T i i) + (∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v) := by
        rw [re_inner_sum_apply_left h v]
        congr 1
        exact Finset.sum_congr rfl fun i _ => ((hh i).re_inner_apply_apply_self v).symm
    _ ≤ (∑ i : ZMod N, T i i) +
        (∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v +
          ∑ k ∈ Finset.Ico m (N - m + 1), F k) := by
        have hle := hMidNonneg
        linarith
    _ = RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
        have hCrossSum : (∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v) =
            (∑ e ∈ Finset.Ico 1 m, (F ((e : ZMod N)) + F ((N - e : ℕ) : ZMod N))) :=
          Finset.sum_congr rfl fun e he => (hCross e he).symm
        have hswap2 : (∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)),
            ∑ i : ZMod N, T i (i + u)) =
            (∑ i : ZMod N, ∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), T i (i + u)) :=
          Finset.sum_comm
        rw [re_inner_sum_apply_apply h v,
          Finset.sum_congr rfl fun i _ => hInner i,
          Finset.sum_congr rfl fun i _ => hSplit0 i, Finset.sum_add_distrib, hCrossSum,
          ← hPart, hswap2]


/-- **Finite-range cyclic Knabe inequality.**

Let `h i` be symmetric projections on a Hilbert space, indexed by the cyclic
group `ZMod N`, such that terms at cyclic separation at least `R` commute
pointwise (cyclic separation at least `R` means the offset `d` satisfies
`R ≤ d ≤ N - R`).  Let `A s = cyclicWindowSum h m s` be the sums of `m`
consecutive terms with `R ≤ m` and `2 * m ≤ N`, and suppose every window has
the quadratic-form gap `γ * Re ⟪A s v, v⟫ ≤ Re ⟪A s v, A s v⟫` uniformly.
Writing `H = ∑ i, h i`, the total term satisfies the quadratic-form gap

`δ * Re ⟪H v, v⟫ ≤ Re ⟪H v, H v⟫,  δ = (m * γ - (R - 1) ^ 2) / (m - R + 1),`

whenever the numerator is positive, `(R - 1) ^ 2 < m * γ`.  For `R = 2` this
is Knabe's nearest-neighbor coefficient `(m * γ - 1) / (m - 1)`.

The nearest-neighbor threshold `γ > 1 / m` goes back to Knabe, J. Stat. Phys.
52, 627 (1988); it is stated in this form in Pérez-García et al.,
arXiv:quant-ph/0608197, lines 1483-1489, and Cirac--Perez-Garcia--Schuch--
Verstraete, arXiv:2011.12127, lines 2194-2197.  The finite-range coefficient
is a TNLean derivation obtained by running Knabe's window argument with a
general range; see the paper-gap note
`docs/paper-gaps/knabe_finite_range_coefficient.tex`. -/
theorem quadraticForm_sum_projections_of_cyclic_knabe
    {N R m : ℕ} [NeZero N]
    (h : ZMod N → E →ₗ[𝕜] E) (hh : ∀ i, (h i).IsSymmetricProjection)
    (hN : 2 * m ≤ N) (hR : 1 ≤ R) (hmR : R ≤ m)
    (hcomm : ∀ d : ℕ, R ≤ d → d + R ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    {γ δ : ℝ} (hδ : δ = (m * γ - (R - 1) ^ 2) / (m - R + 1))
    (hnum : (R - 1) ^ 2 < m * γ)
    (hgap : ∀ s : ZMod N, ∀ v : E,
      γ * RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜 ≤
        RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜)
    (v : E) :
    δ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
  classical
  have hm1 : 1 ≤ m := le_trans hR hmR
  -- The summed window gap.
  have hi : m * γ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      ∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜 := by
    have hSumForm : (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) =
        m * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := re_inner_cyclicWindowSum_sum_apply h m v
    calc m * γ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜
        = γ * (∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜) := by
          rw [hSumForm]
          ring
      _ ≤ ∑ s : ZMod N, RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun s _ => hgap s v
  -- The cyclic expansion.
  have hii := re_inner_cyclicWindowSum_sum_eq h hh m v
  -- The pairwise bound, summed over the ring.
  have hiii : ∀ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v ≤
      2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 :=
    fun e _ => re_inner_cyclicCrossTerms_le_two h hh e v
  -- Nonnegative cross terms at separated offsets.
  have hiv : ∀ e ∈ Finset.Ico R m, 0 ≤ reInnerCyclicCrossTerms h e v := by
    intro e he
    simp only [Finset.mem_Ico] at he
    have he2 : e + R ≤ N := by omega
    exact re_inner_cyclicCrossTerms_nonneg h hh hcomm he.1 he2 v
  -- The diagonal-plus-cross lower bound on the total square.
  have hv := re_inner_sum_two_ge_sum_cyclicCrossTerms h hh hm1 hN hmR hcomm v
  -- The sum of the short-offset weights.
  have hvi : 2 * (∑ e ∈ Finset.Ico 1 R, ((R : ℝ) - 1 - e)) = ((R : ℝ) - 1) * ((R : ℝ) - 2) := by
    have hCast : ∀ e ∈ Finset.Ico 1 R,
        ((R : ℝ) - 1 - e) = ((R - 1 - e : ℕ) : ℝ) := by
      intro e he
      simp only [Finset.mem_Ico] at he
      rw [Nat.cast_sub (by omega : e ≤ R - 1), Nat.cast_sub hR]
      norm_num
    rw [Finset.sum_congr rfl hCast,
      Finset.sum_Ico_reflect (fun d : ℕ => (d : ℝ)) 1 (n := R - 1) (by omega)]
    simp only [Nat.sub_add_cancel hR, Nat.sub_self, Nat.Ico_zero_eq_range]
    have hTwo : ∀ n : ℕ, 2 * (∑ d ∈ Finset.range n, ((d : ℕ) : ℝ)) =
        (n : ℝ) * ((n : ℝ) - 1) := by
      intro n
      by_cases hn : n = 0
      · simp [hn]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn1]
          norm_num
        have hnat := congrArg (fun x : ℕ => (x : ℝ)) (Finset.sum_range_id_mul_two n)
        push_cast at hnat
        rw [← hcast, mul_comm]
        exact hnat
    rw [hTwo (R - 1), Nat.cast_sub hR]
    ring
  -- Assemble the upper bound on the summed window squares.
  have hc : (0 : ℝ) < ((m - R + 1 : ℕ) : ℝ) := by
    have h1 : 0 < m - R + 1 := by omega
    exact_mod_cast h1
  have hSplit : (∑ e ∈ Finset.Ico 1 m, ((m : ℝ) - e) * reInnerCyclicCrossTerms h e v) =
      (((m - R + 1 : ℕ) : ℝ) * (∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v) +
        ∑ e ∈ Finset.Ico 1 m, (((R : ℝ) - 1 - e) * reInnerCyclicCrossTerms h e v)) := by
    have hCoeff : ∀ e ∈ Finset.Ico 1 m,
        (((m : ℝ) - e) * reInnerCyclicCrossTerms h e v) =
          (((m - R + 1 : ℕ) : ℝ) * reInnerCyclicCrossTerms h e v +
            (((R : ℝ) - 1 - e) * reInnerCyclicCrossTerms h e v)) := by
      intro e he
      simp only [Finset.mem_Ico] at he
      have hc2 : ((m - R + 1 : ℕ) : ℝ) = (m : ℝ) - (R : ℝ) + 1 := by
        have h1 : (m - R + 1 : ℕ) = (m - R : ℕ) + 1 := by omega
        rw [h1, Nat.cast_add, Nat.cast_sub hmR]
        push_cast
        ring
      have hEq : ((m : ℝ) - e) =
          ((m - R + 1 : ℕ) : ℝ) + (((R : ℝ) - 1) - (e : ℝ)) := by
        rw [hc2]
        ring
      rw [hEq]
      ring
    rw [Finset.sum_congr rfl hCoeff, Finset.sum_add_distrib, Finset.mul_sum]
  have hDrop : (∑ e ∈ Finset.Ico 1 m, (((R : ℝ) - 1 - e) * reInnerCyclicCrossTerms h e v)) ≤
      ((R : ℝ) - 1) * ((R : ℝ) - 2) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
    have hUnion : Finset.Ico 1 m = Finset.Ico 1 R ∪ Finset.Ico R m :=
      (Finset.Ico_union_Ico_eq_Ico (a := 1) (b := R) (c := m) (by omega) (by omega)).symm
    have hDisj : Disjoint (Finset.Ico 1 R) (Finset.Ico R m) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      simp only [Finset.mem_inter, Finset.mem_Ico] at hx
      omega
    rw [hUnion, Finset.sum_union hDisj]
    have hShort : (∑ e ∈ Finset.Ico 1 R, (((R : ℝ) - 1 - e) * reInnerCyclicCrossTerms h e v)) ≤
        ((R : ℝ) - 1) * ((R : ℝ) - 2) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
      calc (∑ e ∈ Finset.Ico 1 R, (((R : ℝ) - 1 - e) * reInnerCyclicCrossTerms h e v))
          ≤ (∑ e ∈ Finset.Ico 1 R, (((R : ℝ) - 1 - e) *
              (2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜))) := by
            refine Finset.sum_le_sum fun e he => ?_
            simp only [Finset.mem_Ico] at he
            have heR : (e : ℝ) + 1 ≤ (R : ℝ) := by
              exact_mod_cast (show e + 1 ≤ R by omega)
            have hCoeffNonneg : (0 : ℝ) ≤ (R : ℝ) - 1 - e := by linarith
            exact mul_le_mul_of_nonneg_left
              (hiii e (by simp only [Finset.mem_Ico]; omega)) hCoeffNonneg
        _ = ((R : ℝ) - 1) * ((R : ℝ) - 2) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
            rw [← Finset.sum_mul]
            calc
              (∑ e ∈ Finset.Ico 1 R, (R - 1 - (e : ℝ))) *
                  (2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) =
                  (2 * ∑ e ∈ Finset.Ico 1 R, (R - 1 - (e : ℝ))) *
                    RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by ring
              _ = _ := by rw [hvi]
    have hLong : (∑ e ∈ Finset.Ico R m, (((R : ℝ) - 1 - e) * reInnerCyclicCrossTerms h e v)) ≤
        0 := by
      refine Finset.sum_nonpos fun e he => ?_
      have he' := Finset.mem_Ico.mp he
      have heR : (R : ℝ) ≤ (e : ℝ) := by exact_mod_cast he'.1
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hiv e he)
    linarith
  -- Combine.
  have hUpper : (∑ s : ZMod N,
      RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜) ≤
      (((m - R + 1 : ℕ) : ℝ) * RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 +
        ((R : ℝ) - 1) ^ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) := by
    have hCrossSumLe : (∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v) ≤
        RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 - RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
      have h1 := hv
      linarith
    rw [hii, hSplit]
    have hMidLe : (((m - R + 1 : ℕ) : ℝ) *
        (∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v)) ≤
        (((m - R + 1 : ℕ) : ℝ) *
          (RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 -
            RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜)) :=
      mul_le_mul_of_nonneg_left hCrossSumLe (le_of_lt hc)
    have hCast : ((m - R + 1 : ℕ) : ℝ) = (m : ℝ) - (R : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hmR]
      push_cast
      ring
    calc
      (m : ℝ) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
          (((m - R + 1 : ℕ) : ℝ) *
            (∑ e ∈ Finset.Ico 1 m, reInnerCyclicCrossTerms h e v) +
          ∑ e ∈ Finset.Ico 1 m,
            ((R : ℝ) - 1 - e) * reInnerCyclicCrossTerms h e v)
        ≤ (m : ℝ) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 +
            ((m - R + 1 : ℕ) : ℝ) *
              (RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 -
                RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) +
            ((R : ℝ) - 1) * ((R : ℝ) - 2) *
              RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by linarith
      _ = ((m - R + 1 : ℕ) : ℝ) *
            RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 +
          ((R : ℝ) - 1) ^ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 := by
            rw [hCast]
            ring
  have hKey : m * γ * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      (((m - R + 1 : ℕ) : ℝ) * RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 +
        ((R : ℝ) - 1) ^ 2 * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜) := hi.trans hUpper
  have hCastC : ((m - R + 1 : ℕ) : ℝ) = (m : ℝ) - (R : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hmR]
    push_cast
    ring
  have hDiv : (m * γ - ((R : ℝ) - 1) ^ 2) *
      RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 / ((m : ℝ) - R + 1) ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
    rw [← hCastC]
    refine (div_le_iff₀' hc).2 ?_
    linarith
  have _hδpos : 0 < δ := by
    rw [hδ]
    exact div_pos (sub_pos.mpr hnum) (by rw [← hCastC]; exact hc)
  rw [hδ, div_mul_eq_mul_div]
  exact hDiv

/-- **Nearest-neighbor cyclic Knabe inequality.**

For interaction range `R = 2`, the finite-range coefficient becomes
`(m * γ - 1) / (m - 1)`. Thus a window gap above `1 / m` gives a positive
periodic gap on every ring with `2 * m ≤ N`.

This is the threshold of Knabe, J. Stat. Phys. 52, 627 (1988), and the form
quoted in Pérez-García et al., arXiv:quant-ph/0608197, lines 1483-1489, and
Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, lines 2194-2197. -/
theorem quadraticForm_sum_projections_of_cyclic_knabe_nearest_neighbor
    {N m : ℕ} [NeZero N]
    (h : ZMod N → E →ₗ[𝕜] E) (hh : ∀ i, (h i).IsSymmetricProjection)
    (hN : 2 * m ≤ N) (hm : 2 ≤ m)
    (hcomm : ∀ d : ℕ, 2 ≤ d → d + 2 ≤ N → ∀ i : ZMod N, ∀ v : E,
      h i (h ((i + (d : ZMod N))) v) = h ((i + (d : ZMod N))) (h i v))
    {γ : ℝ} (hnum : 1 < m * γ)
    (hgap : ∀ s : ZMod N, ∀ v : E,
      γ * RCLike.re ⟪cyclicWindowSum h m s v, v⟫_𝕜 ≤
        RCLike.re ⟪cyclicWindowSum h m s v, cyclicWindowSum h m s v⟫_𝕜)
    (v : E) :
    ((m * γ - 1) / (m - 1)) * RCLike.re ⟪(∑ i, h i) v, v⟫_𝕜 ≤
      RCLike.re ⟪(∑ i, h i) v, (∑ i, h i) v⟫_𝕜 := by
  apply quadraticForm_sum_projections_of_cyclic_knabe h hh hN (R := 2)
    (by norm_num) hm hcomm (γ := γ) (δ := (m * γ - 1) / (m - 1))
  · ring
  · norm_num
    exact hnum
  · exact hgap

end CyclicFamily

end ProjectionGeometry
