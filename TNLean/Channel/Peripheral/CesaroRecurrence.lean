/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.SpectralProjection
import TNLean.Channel.FixedPoint.MeanErgodicProjection
import TNLean.Channel.Semigroup.CPClosure
import TNLean.Analysis.Dirichlet
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The recurrent subsequence and Cesàro spectral identities — Wolf Proposition 6.3

For a positive trace-preserving linear map `T` on `M_d(ℂ)`, Wolf's
Proposition 6.3(i) produces a strictly increasing sequence `n₁ < n₂ < ⋯` of
exponents with `T^(nᵢ) → T_φ`, where `T_φ` is the peripheral spectral
projection of `TNLean.Channel.Peripheral.SpectralProjection` (Wolf Equation
6.12).  The limit splits into two parts:

* on the **peripheral** spectral subspace, `T` acts on each peripheral
  eigenvector by a unit phase, and Dirichlet's simultaneous approximation
  theorem (`Dirichlet.exists_strictMono_pow_tendsto_one`, the corollary of
  Wolf's Lemma 6.1) provides a recurrent subsequence along which every phase
  tends to one, so `T^(nᵢ) x → x`;
* on the **non-peripheral** spectral subspace every eigenvalue has modulus
  strictly less than one (bounded orbits force `‖μ‖ ≤ 1`), and the binomial
  expansion of `(μ • 1 + N)ⁿ` with nilpotent `N` shows `Tⁿ x → 0` outright.

Since `T_φ` is a pointwise limit of the maps `T^(nᵢ)`, it inherits their
positivity, trace preservation, and complete positivity (via closedness of the
positive-semidefinite cone and of the set of completely positive maps in
finite dimension).

## Main statements

* `Module.End.tendsto_pow_apply_zero_of_mem_nonPeripheralSubspace`: powers
  vanish on the non-peripheral spectral subspace when all eigenvalues have
  modulus at most one.
* `Module.End.tendsto_pow_apply_self_of_mem_iSup_eigenspace`: recurrent
  subsequences fix the span of the peripheral eigenspaces.
* `IsPositiveMap.exists_strictMono_tendsto_pow_peripheralProjection`:
  **Wolf Proposition 6.3(i)** — `T^(nᵢ) → T_φ` pointwise along a strictly
  monotone recurrent subsequence.
* `IsPositiveMap.peripheralProjection_isPositiveMap`,
  `IsPositiveMap.peripheralProjection_isTracePreservingMap`,
  `IsPositiveMap.peripheralProjection_isCPMap`: `T_φ` inherits positivity,
  trace preservation, and complete positivity.
* `IsChannel.peripheralProjection`, `IsChannel.peripheralWeightedProjection`:
  the channel properties of `T_φ` and `T_φ' = T T_φ` (Wolf Equation 6.13).
* `IsPositiveMap.peripheralProjection_comp_meanErgodicProjection`:
  the absorption identity `T_φ T_∞ = T_∞` (Wolf Equation 6.14 area).

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.3 and
  Equations (6.11)--(6.15); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--271.
-/

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius Topology
open Matrix Filter

namespace Module.End

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Decay of powers on generalized eigenspaces with `‖μ‖ < 1` -/

/-- For a complex number of modulus less than one, the sequence
`n ↦ (n.choose m) * μⁿ` tends to zero for every fixed `m`: the binomial
coefficient grows polynomially while `μⁿ` decays exponentially. -/
theorem tendsto_choose_mul_pow_zero {μ : ℂ} (hμ : ‖μ‖ < 1) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ (n.choose m : ℂ) * μ ^ n) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ m * ‖μ‖ ^ n) atTop (𝓝 0) := by
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp only [norm_zero]
      refine tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn ↦ ?_
      rw [zero_pow (by omega : n ≠ 0), mul_zero]
    · have hr : 1 < ‖μ‖⁻¹ := (one_lt_inv₀ (norm_pos_iff.mpr hμ0)).mpr hμ
      have hdiv := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) m hr).tendsto_div_nhds_zero
      have heq : (fun n : ℕ ↦ (n : ℝ) ^ m / ‖μ‖⁻¹ ^ n) = fun n : ℕ ↦ (n : ℝ) ^ m * ‖μ‖ ^ n := by
        funext n
        simp only [inv_pow, div_eq_mul_inv, inv_inv]
      rwa [heq] at hdiv
  refine squeeze_zero_norm (fun n ↦ ?_) hreal
  rw [norm_mul, Complex.norm_natCast, norm_pow]
  calc
    ((n.choose m : ℝ)) * ‖μ‖ ^ n ≤ ((n : ℝ) ^ m / (m.factorial : ℝ)) * ‖μ‖ ^ n := by
      exact mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div m n)
        (pow_nonneg (norm_nonneg μ) n)
    _ ≤ (n : ℝ) ^ m * ‖μ‖ ^ n := by
      exact mul_le_mul_of_nonneg_right
        (div_le_self (pow_nonneg (Nat.cast_nonneg n) m)
          (by exact_mod_cast Nat.factorial_pos m))
        (pow_nonneg (norm_nonneg μ) n)

/-- The binomial expansion applied to a vector annihilated by `(f - μ • 1) ^ l`:
for `n ≥ l`, `fⁿ x` is the sum over `m < l` of `(n.choose m) • μ^(n-m) • N^m x`,
where `N = f - μ • 1`. -/
private theorem pow_apply_eq_sum_choose_smul {f : Module.End ℂ V} {μ : ℂ} {l : ℕ}
    {x : V} (hx : x ∈ LinearMap.ker ((f - μ • 1) ^ l)) {n : ℕ} (hn : l ≤ n) :
    (f ^ n) x = ∑ m ∈ Finset.range l,
      ((n.choose m : ℂ) * μ ^ (n - m)) • (((f - μ • 1) ^ m) x) := by
  classical
  set N := f - μ • 1 with hN
  have hf : f = N + μ • 1 := by rw [hN, sub_add_cancel]
  have hcomm : Commute N (μ • 1) := (Algebra.commutes μ N).symm
  have hNl : (N ^ l) x = 0 := by rwa [LinearMap.mem_ker] at hx
  have hvan : ∀ m : ℕ, l ≤ m → (N ^ m) x = 0 := by
    intro m hm
    rw [← Nat.sub_add_cancel hm, pow_add, Module.End.mul_apply, hNl, map_zero]
  have hscalar : ∀ (k : ℕ) (y : V), ((μ • 1 : Module.End ℂ V) ^ k) y = μ ^ k • y := by
    intro k y
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        change μ • (μ ^ k • y) = μ ^ (k + 1) • y
        rw [smul_smul, pow_succ']
  calc
    (f ^ n) x = ((N + μ • 1) ^ n) x := by rw [hf]
    _ = ∑ m ∈ Finset.range (n + 1),
        (N ^ m * (μ • 1) ^ (n - m) * ↑(n.choose m)) x := by
      calc
        ((N + μ • 1) ^ n) x =
            (∑ m ∈ Finset.range (n + 1),
              N ^ m * (μ • 1) ^ (n - m) * ↑(n.choose m)) x :=
          congrArg (fun g : Module.End ℂ V ↦ g x) (hcomm.add_pow n)
        _ = _ := by
          change (LinearMap.applyₗ (R := ℂ) x) (∑ m ∈ Finset.range (n + 1),
            N ^ m * (μ • 1) ^ (n - m) * (↑(n.choose m) : Module.End ℂ V)) = _
          rw [map_sum]
          simp only [LinearMap.applyₗ_apply_apply]
    _ = ∑ m ∈ Finset.range l,
        (N ^ m * (μ • 1) ^ (n - m) * ↑(n.choose m)) x := by
      refine (Finset.sum_subset (Finset.range_mono (hn.trans (Nat.le_succ n)))
        fun m hm hm' ↦ ?_).symm
      rw [Finset.mem_range] at hm hm'
      have hlm : l ≤ m := Nat.le_of_not_gt hm'
      simp only [Module.End.mul_apply, Module.End.natCast_apply, hscalar]
      rw [map_smul, map_nsmul, hvan m hlm]
      simp
    _ = ∑ m ∈ Finset.range l,
        ((n.choose m : ℂ) * μ ^ (n - m)) • ((N ^ m) x) := by
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      simp only [Module.End.mul_apply, Module.End.natCast_apply, hscalar]
      rw [map_smul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      exact mul_comm _ _

/-- **Decay of powers on a generalized eigenvector of modulus `< 1`.**  On
`ker ((f - μ • 1) ^ l)` the binomial expansion of `fⁿ = (N + μ • 1)ⁿ` has only
`l` surviving terms, each a polynomial factor times the exponentially decaying
`μ^(n-m)`. -/
theorem tendsto_pow_apply_zero_of_norm_lt_one {f : Module.End ℂ V} {μ : ℂ}
    (hμ : ‖μ‖ < 1) {l : ℕ} {x : V} (hx : x ∈ LinearMap.ker ((f - μ • 1) ^ l)) :
    Tendsto (fun n : ℕ ↦ (f ^ n) x) atTop (𝓝 0) := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · -- `μ = 0`: `f ^ l x = (f - 0) ^ l x = 0`, so the sequence is eventually zero.
    refine tendsto_atTop_of_eventually_const (i₀ := l) fun n hn ↦ ?_
    rw [← Nat.sub_add_cancel hn, pow_add, Module.End.mul_apply]
    have : (f ^ l) x = 0 := by
      have h := hx
      rw [LinearMap.mem_ker] at h
      simpa using h
    rw [this, map_zero]
  · -- `μ ≠ 0`: use the binomial expansion; each of the `l` terms tends to zero.
    have hterm : ∀ m : ℕ, Tendsto (fun n : ℕ ↦
        ((n.choose m : ℂ) * μ ^ (n - m)) • (((f - μ • 1) ^ m) x)) atTop (𝓝 0) := by
      intro m
      have hscal : Tendsto (fun n : ℕ ↦ (n.choose m : ℂ) * μ ^ (n - m)) atTop (𝓝 0) := by
        have heq : ∀ n : ℕ, m ≤ n → (n.choose m : ℂ) * μ ^ (n - m) =
            ((n.choose m : ℂ) * μ ^ n) / μ ^ m := by
          intro n hmn
          apply (eq_div_iff (pow_ne_zero m hμ0)).2
          calc
            (n.choose m : ℂ) * μ ^ (n - m) * μ ^ m =
                (n.choose m : ℂ) * (μ ^ (n - m) * μ ^ m) := by ring
            _ = (n.choose m : ℂ) * μ ^ n := by
              rw [← pow_add, Nat.sub_add_cancel hmn]
        have hdiv : Tendsto (fun n : ℕ ↦
            ((n.choose m : ℂ) * μ ^ n) / μ ^ m) atTop (𝓝 0) := by
          simpa only [zero_div] using (tendsto_choose_mul_pow_zero hμ m).div_const (μ ^ m)
        exact hdiv.congr'
          (Filter.eventually_atTop.mpr ⟨m, fun n hn ↦ (heq n hn).symm⟩)
      simpa using hscal.smul
        (tendsto_const_nhds (x := ((f - μ • 1) ^ m) x))
    have hsum : Tendsto (fun n : ℕ ↦ ∑ m ∈ Finset.range l,
        ((n.choose m : ℂ) * μ ^ (n - m)) • (((f - μ • 1) ^ m) x)) atTop
        (𝓝 (∑ m ∈ Finset.range l, (0 : V))) :=
      tendsto_finsetSum (Finset.range l) fun m _ ↦ hterm m
    rw [Finset.sum_const_zero] at hsum
    exact hsum.congr' (Filter.eventually_atTop.mpr
      ⟨l, fun n hn ↦ (pow_apply_eq_sum_choose_smul hx hn).symm⟩)

/-- **Decay of powers on a maximal generalized eigenspace of modulus `< 1`.** -/
theorem tendsto_pow_apply_zero_of_mem_maxGenEigenspace_of_norm_lt_one
    [FiniteDimensional ℂ V] {f : Module.End ℂ V} {μ : ℂ} (hμ : ‖μ‖ < 1) {x : V}
    (hx : x ∈ f.maxGenEigenspace μ) :
    Tendsto (fun n : ℕ ↦ (f ^ n) x) atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := (f.mem_maxGenEigenspace μ x).mp hx
  exact tendsto_pow_apply_zero_of_norm_lt_one hμ
    (by rwa [LinearMap.mem_ker])

/-- Bounded-index supremum over a finite set equals the supremum over its
`Finset` realization. -/
private theorem biSup_set_eq_toFinset {α : Type*} [CompleteLattice α] {s : Set ℂ}
    (hs : s.Finite) (p : ℂ → α) : ⨆ μ ∈ s, p μ = ⨆ μ ∈ hs.toFinset, p μ := by
  apply le_antisymm
  · exact iSup₂_le fun μ hμ ↦ le_biSup p (hs.mem_toFinset.mpr hμ)
  · exact iSup₂_le fun μ hμ ↦ le_biSup p (hs.mem_toFinset.mp hμ)

/-- **Powers vanish on the non-peripheral spectral subspace.**  When every
eigenvalue of `f` has modulus at most one, each non-peripheral eigenvalue has
modulus strictly less than one, so `fⁿ x → 0` on the sum of the non-peripheral
generalized eigenspaces. -/
theorem tendsto_pow_apply_zero_of_mem_nonPeripheralSubspace [FiniteDimensional ℂ V]
    {f : Module.End ℂ V}
    (hb : ∀ μ : ℂ, f.HasEigenvalue μ → ‖μ‖ ≤ 1) {x : V}
    (hx : x ∈ f.nonPeripheralSubspace) :
    Tendsto (fun n : ℕ ↦ (f ^ n) x) atTop (𝓝 0) := by
  rw [nonPeripheralSubspace, biSup_set_eq_toFinset
    (f.finite_hasEigenvalue_and_norm_ne_one)] at hx
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).mp hx
  rw [← hv]
  have hzero : ∀ μ ∈ (f.finite_hasEigenvalue_and_norm_ne_one).toFinset,
      Tendsto (fun n : ℕ ↦ (f ^ n) (v μ : V)) atTop (𝓝 0) := by
    intro μ hμ
    have hμ' := (f.finite_hasEigenvalue_and_norm_ne_one).mem_toFinset.mp hμ
    exact tendsto_pow_apply_zero_of_mem_maxGenEigenspace_of_norm_lt_one
      (lt_of_le_of_ne' (hb μ hμ'.1) hμ'.2.symm) (v μ).2
  simpa only [map_sum, Finset.sum_const_zero] using
    tendsto_finsetSum _ fun μ hμ ↦ hzero μ hμ

/-! ### Recurrent subsequences on eigenspaces -/

/-- **Recurrent subsequences fix the span of peripheral eigenspaces.**  If the
phases `μ ^ (n i)` tend to `1` along a sequence of exponents for every `μ` in
a finite index set, then `f ^ (n i) x → x` on the sum of the corresponding
eigenspaces.  This is the mechanism of Wolf Proposition 6.3(i): along the
Dirichlet recurrent subsequence, `T ^ (n i)` converges to the identity on the
peripheral spectral subspace. -/
theorem tendsto_pow_apply_self_of_mem_iSup_eigenspace {f : Module.End ℂ V}
    {s : Finset ℂ} {n : ℕ → ℕ}
    (hn : ∀ μ ∈ s, Tendsto (fun i : ℕ ↦ μ ^ n i) atTop (𝓝 1)) {x : V}
    (hx : x ∈ ⨆ μ ∈ s, f.eigenspace μ) :
    Tendsto (fun i : ℕ ↦ (f ^ n i) x) atTop (𝓝 x) := by
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).mp hx
  rw [← hv]
  have hterm : ∀ μ ∈ s, Tendsto (fun i : ℕ ↦ (f ^ n i) (v μ : V)) atTop (𝓝 (v μ : V)) := by
    intro μ hμ
    have hmem : (v μ : V) ∈ f.eigenspace μ := (v μ).2
    have hEq : ∀ i : ℕ, (f ^ n i) (v μ : V) = μ ^ n i • (v μ : V) := by
      intro i
      rcases eq_or_ne (v μ : V) 0 with hz | hz
      · rw [hz, map_zero, smul_zero]
      · exact HasEigenvector.pow_apply ⟨hmem, hz⟩ (n i)
    have hlim : Tendsto (fun i : ℕ ↦ μ ^ n i • (v μ : V)) atTop (𝓝 ((1 : ℂ) • (v μ : V))) :=
      (hn μ hμ).smul tendsto_const_nhds
    rw [one_smul] at hlim
    exact hlim.congr' (Filter.Eventually.of_forall fun i ↦ (hEq i).symm)
  simpa only [map_sum] using tendsto_finsetSum _ fun μ hμ ↦ hterm μ hμ

end Module.End

/-! ### Bounded orbits bound the eigenvalues -/

namespace LinearMap.HasBoundedOrbits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E →ₗ[ℂ] E}

/-- If every forward orbit of `f` is bounded, every eigenvalue has modulus at
most one: on an eigenvector the orbit norms are `‖μ‖ⁿ ‖x‖`, which is unbounded
when `‖μ‖ > 1`. -/
theorem norm_le_one_of_hasEigenvalue (hf : f.HasBoundedOrbits) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue f μ) : ‖μ‖ ≤ 1 := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 : x ≠ 0 := hx.2
  have hfx : ∀ n : ℕ, (f ^ n) x = μ ^ n • x := fun n ↦ Module.End.HasEigenvector.pow_apply hx n
  by_contra hle
  push Not at hle
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (hf x)
  have hbound : ∀ n : ℕ, ‖μ‖ ^ n * ‖x‖ ≤ C + ‖x‖ := by
    intro n
    have hdist := hC ⟨n, rfl⟩ ⟨0, rfl⟩
    have hdist' : ‖(f ^ n) x - x‖ ≤ C := by
      simpa only [← Module.End.coe_pow, Function.iterate_zero_apply, dist_eq_norm] using hdist
    calc
      ‖μ‖ ^ n * ‖x‖ = ‖μ ^ n • x‖ := by rw [norm_smul, norm_pow]
      _ = ‖(f ^ n) x‖ := by rw [hfx]
      _ = ‖(f ^ n) x - x + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖(f ^ n) x - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ C + ‖x‖ := by
          gcongr
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hgrow := (tendsto_pow_atTop_atTop_of_one_lt hle).eventually
    (eventually_gt_atTop ((C + ‖x‖) / ‖x‖))
  obtain ⟨n, hn⟩ := hgrow.exists
  have := hbound n
  rw [div_lt_iff₀ hxn] at hn
  linarith

end LinearMap.HasBoundedOrbits

/-! ### Pointwise convergence implies operator-norm convergence in finite dimension -/

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- In finite dimension, pointwise convergence of continuous linear
endomorphisms implies convergence in the operator norm: evaluation on a finite
basis is a linear isomorphism onto a finite product, hence a homeomorphism. -/
theorem tendsto_of_tendsto_apply_of_finiteDimensional {S : ℕ → E →L[ℂ] E} {P : E →L[ℂ] E}
    (h : ∀ x : E, Tendsto (fun n : ℕ ↦ S n x) atTop (𝓝 (P x))) :
    Tendsto S atTop (𝓝 P) := by
  classical
  let ι := Fin (Module.finrank ℂ E)
  let b := Module.finBasis ℂ E
  -- Evaluation on the basis, as a continuous linear map into a finite product.
  let Φ : (E →L[ℂ] E) →L[ℂ] (ι → E) :=
    ContinuousLinearMap.pi fun i ↦ (ContinuousLinearMap.apply ℂ E) (b i)
  have hΦ : ∀ (f : E →L[ℂ] E) (i : ι), Φ f i = f (b i) := fun f i ↦
    ContinuousLinearMap.pi_apply _ f i
  -- `Φ` is bijective: maps are determined by their values on the basis.
  have hinj : Function.Injective Φ.toLinearMap := by
    intro f g hfg
    have hfg' : ∀ i : ι, f (b i) = g (b i) := fun i ↦
      calc f (b i) = Φ f i := (hΦ f i).symm
        _ = Φ g i := congrFun hfg i
        _ = g (b i) := hΦ g i
    have hlin : f.toLinearMap = g.toLinearMap := b.ext hfg'
    exact ContinuousLinearMap.ext fun x ↦ LinearMap.congr_fun hlin x
  have hsurj : Function.Surjective Φ.toLinearMap := by
    intro w
    refine ⟨LinearMap.toContinuousLinearMap (b.constr ℂ w), ?_⟩
    ext i
    change Φ (LinearMap.toContinuousLinearMap (b.constr ℂ w)) i = w i
    rw [hΦ]
    exact b.constr_basis (M' := E) ℂ w i
  let e := LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩
  -- Both directions are continuous in finite dimension.
  have hfwd : Continuous e := Φ.toLinearMap.continuous_of_finiteDimensional
  have hbwd : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  -- Convergence of the evaluations, then transport back.
  have hEval : Tendsto (fun n : ℕ ↦ e (S n)) atTop (𝓝 (e P)) := by
    rw [tendsto_pi_nhds]
    intro i
    have hS : ∀ n : ℕ, e (S n) i = S n (b i) := fun n ↦ hΦ (S n) i
    have hP : e P i = P (b i) := hΦ P i
    simp_rw [hS, hP]
    exact h (b i)
  have hb := (hbwd.tendsto (e P)).comp hEval
  have heq : e.symm ∘ (fun n : ℕ ↦ e (S n)) = S := by
    funext n
    exact e.symm_apply_apply (S n)
  rw [heq] at hb
  simpa only [LinearEquiv.symm_apply_apply] using hb

end ContinuousLinearMap

/-! ### Wolf Proposition 6.3(i): the recurrent subsequence for positive TP maps -/

namespace IsPositiveMap

variable {D : ℕ} [NeZero D]
  {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- **Wolf Proposition 6.3(i), pointwise form.**  For a positive
trace-preserving map, along any strictly monotone sequence of exponents that
simultaneously recurs for every peripheral eigenvalue (`μ ^ (n i) → 1`), the
powers `T ^ (n i)` converge pointwise to the peripheral spectral projection
`T_φ`. -/
theorem tendsto_pow_apply_peripheralProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {n : ℕ → ℕ} (hnmono : StrictMono n)
    (hn : ∀ μ ∈ peripheralEigenvalues T, Tendsto (fun i : ℕ ↦ μ ^ n i) atTop (𝓝 1))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop (𝓝 (T.peripheralProjection X)) := by
  have hb : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ ≤ 1 := fun μ hμ ↦
    (hPos.hasBoundedOrbits_of_tracePreserving hTP).norm_le_one_of_hasEigenvalue hμ
  -- The peripheral part: the projection's range is the span of the peripheral
  -- eigenspaces (Wolf Proposition 6.2), fixed by the recurrent subsequence.
  have hPmem : T.peripheralProjection X ∈
      ⨆ μ ∈ (peripheralEigenvalues_finite T).toFinset, T.eigenspace μ := by
    have h1 := T.peripheralProjection_apply_mem X
    rw [hPos.peripheralSubspace_eq_iSup_eigenspace hTP,
      Module.End.biSup_set_eq_toFinset (peripheralEigenvalues_finite T)] at h1
    exact h1
  have hper : Tendsto (fun i : ℕ ↦ (T ^ n i) (T.peripheralProjection X)) atTop
      (𝓝 (T.peripheralProjection X)) :=
    T.tendsto_pow_apply_self_of_mem_iSup_eigenspace
      (fun μ hμ ↦ hn μ ((peripheralEigenvalues_finite T).mem_toFinset.mp hμ)) hPmem
  -- The non-peripheral part: powers decay to zero, hence also along the
  -- subsequence.
  have hnonp : Tendsto (fun i : ℕ ↦ (T ^ n i) (X - T.peripheralProjection X)) atTop
      (𝓝 0) :=
    (T.tendsto_pow_apply_zero_of_mem_nonPeripheralSubspace hb
      (T.sub_peripheralProjection_mem X)).comp hnmono.tendsto_atTop
  -- Combine along the decomposition `X = T_φ X + (X - T_φ X)`.
  have hsum := hper.add hnonp
  rw [add_zero] at hsum
  exact hsum.congr' (Filter.Eventually.of_forall fun i ↦ by
    rw [← map_add, add_sub_cancel])

/-- The Dirichlet recurrent subsequence of the peripheral phases: strictly
monotone exponents along which every peripheral eigenvalue's powers tend to
one. Shared by the pointwise and operator-norm convergence statements of
Wolf Proposition 6.3(i). -/
private theorem exists_dirichlet_recurrent_subsequence :
    ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧
      ∀ μ ∈ peripheralEigenvalues T, Tendsto (fun i : ℕ ↦ μ ^ n i) atTop (𝓝 1) := by
  classical
  letI := (peripheralEigenvalues_finite T).fintype
  obtain ⟨n, hnmono, hn0, hn⟩ := Dirichlet.exists_strictMono_pow_tendsto_one
    (fun μ : peripheralEigenvalues T ↦ (μ : ℂ)) (fun μ ↦ μ.prop.2)
  exact ⟨n, hnmono, hn0, fun μ hμ ↦ hn ⟨μ, hμ⟩⟩

/-- **Wolf Proposition 6.3(i).**  For a positive trace-preserving map there is
a strictly monotone sequence of exponents — the Dirichlet recurrent
subsequence of the peripheral phases — along which `T ^ (n i) → T_φ`
pointwise. -/
theorem exists_strictMono_tendsto_pow_peripheralProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧
      ∀ X, Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop (𝓝 (T.peripheralProjection X)) := by
  obtain ⟨n, hnmono, hn0, hn⟩ := exists_dirichlet_recurrent_subsequence (T := T)
  exact ⟨n, hnmono, hn0, fun X ↦
    hPos.tendsto_pow_apply_peripheralProjection hTP hnmono hn X⟩

/-- **Wolf Proposition 6.3(i), operator-norm form.**  Along the recurrent
subsequence, the powers converge to `T_φ` in the operator norm (as continuous
linear endomorphisms). -/
theorem tendsto_endEquiv_pow_peripheralProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {n : ℕ → ℕ} (hnmono : StrictMono n)
    (hn : ∀ μ ∈ peripheralEigenvalues T, Tendsto (fun i : ℕ ↦ μ ^ n i) atTop (𝓝 1)) :
    Tendsto (fun i : ℕ ↦ endEquiv (T ^ n i)) atTop (𝓝 (endEquiv T.peripheralProjection)) :=
  ContinuousLinearMap.tendsto_of_tendsto_apply_of_finiteDimensional fun X ↦
    hPos.tendsto_pow_apply_peripheralProjection hTP hnmono hn X

/-! ### Positivity, trace preservation, and complete positivity of `T_φ` -/

omit [NeZero D] in
/-- Powers of a positive map stay positive on positive-semidefinite inputs. -/
private theorem pow_posSemidef_of_isPositiveMap (hPos : IsPositiveMap T)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) (m : ℕ) :
    ((T ^ m) X).PosSemidef := by
  induction m with
  | zero => simpa using hX
  | succ m ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
      exact hPos _ ih

/-- The peripheral spectral projection `T_φ` of a positive trace-preserving
map is positive: it is a pointwise limit of the positive maps `T ^ (n i)`, and
the positive-semidefinite cone is closed. -/
theorem peripheralProjection_isPositiveMap
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    IsPositiveMap T.peripheralProjection := by
  intro X hX
  obtain ⟨n, -, -, hn⟩ := hPos.exists_strictMono_tendsto_pow_peripheralProjection hTP
  exact isClosed_posSemidef.mem_of_tendsto (hn X)
    (Filter.Eventually.of_forall fun i ↦ pow_posSemidef_of_isPositiveMap hPos hX (n i))

/-- The peripheral spectral projection `T_φ` of a positive trace-preserving
map is trace-preserving: every iterate preserves the trace, and continuity of
the trace passes the identity to the limit. -/
theorem peripheralProjection_isTracePreservingMap
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    IsTracePreservingMap T.peripheralProjection := by
  intro X
  obtain ⟨n, -, -, hn⟩ := hPos.exists_strictMono_tendsto_pow_peripheralProjection hTP
  have htr : ∀ m : ℕ, Matrix.trace ((T ^ m) X) = Matrix.trace X := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, hTP, ih]
  have hlim : Tendsto (fun i : ℕ ↦ Matrix.trace ((T ^ n i) X)) atTop
      (𝓝 (Matrix.trace (T.peripheralProjection X))) :=
    ((Matrix.traceLinearMap (Fin D) ℂ ℂ).continuous_of_finiteDimensional.tendsto
      (T.peripheralProjection X)).comp (hn X)
  have hconst : (fun i : ℕ ↦ Matrix.trace ((T ^ n i) X)) = fun _ ↦ Matrix.trace X :=
    funext fun i ↦ htr (n i)
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The peripheral spectral projection `T_φ` of a completely positive
trace-preserving map is completely positive: in finite dimension the set of
completely positive maps is closed, and along the recurrent subsequence the
powers converge to `T_φ` in the operator norm. -/
theorem peripheralProjection_isCPMap
    (hCP : IsCPMap T) (hTP : IsTracePreservingMap T) :
    IsCPMap T.peripheralProjection := by
  obtain ⟨n, hnmono, -, hn⟩ :=
    hCP.isPositiveMap.exists_strictMono_tendsto_pow_peripheralProjection hTP
  exact IsCPMap.of_tendsto_toCLM (fun i ↦ IsCPMap.pow hCP (n i))
    (ContinuousLinearMap.tendsto_of_tendsto_apply_of_finiteDimensional hn)

/-- **Wolf Proposition 6.3(i), combined form.**  Along one and the same
Dirichlet recurrent subsequence, the powers converge to `T_φ` both pointwise
and in the operator norm. -/
theorem exists_strictMono_tendsto_pow_peripheralProjection_clm
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧
      (∀ X, Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop (𝓝 (T.peripheralProjection X))) ∧
        Tendsto (fun i : ℕ ↦ endEquiv (T ^ n i)) atTop
          (𝓝 (endEquiv T.peripheralProjection)) := by
  obtain ⟨n, hnmono, hn0, hn⟩ := exists_dirichlet_recurrent_subsequence (T := T)
  exact ⟨n, hnmono, hn0,
    fun X ↦ hPos.tendsto_pow_apply_peripheralProjection hTP hnmono hn X,
    hPos.tendsto_endEquiv_pow_peripheralProjection hTP hnmono hn⟩

/-- The phase-weighted peripheral projection `T_φ' = T ∘ T_φ` of a positive
trace-preserving map is positive: the positive-only case of the preservation
assertion in Wolf Proposition 6.3(ii) (no complete positivity needed, since
positive maps are closed under composition). -/
theorem peripheralWeightedProjection_isPositiveMap
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    IsPositiveMap T.peripheralWeightedProjection := by
  intro X hX
  rw [Module.End.peripheralWeightedProjection, LinearMap.comp_apply]
  exact hPos _ ((hPos.peripheralProjection_isPositiveMap hTP) _ hX)

/-- The phase-weighted peripheral projection `T_φ' = T ∘ T_φ` of a positive
trace-preserving map is trace-preserving: both factors preserve the trace.
This is the positive-only case for `T_φ'` of the preservation assertion in
Wolf, Proposition 6.3
(`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--229). -/
theorem peripheralWeightedProjection_isTracePreservingMap
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    IsTracePreservingMap T.peripheralWeightedProjection := by
  intro X
  rw [Module.End.peripheralWeightedProjection, LinearMap.comp_apply, hTP,
    hPos.peripheralProjection_isTracePreservingMap hTP]

end IsPositiveMap

/-! ### Channel packaging and the mean-ergodic absorption identity -/

namespace IsChannel

variable {D : ℕ} [NeZero D]
  {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- The peripheral spectral projection of a channel is again a channel. -/
theorem peripheralProjection (hT : IsChannel T) :
    IsChannel T.peripheralProjection where
  cp := IsPositiveMap.peripheralProjection_isCPMap hT.cp hT.tp
  tp := IsPositiveMap.peripheralProjection_isTracePreservingMap hT.cp.isPositiveMap hT.tp

/-- The phase-weighted peripheral projection `T_φ' = T ∘ T_φ` of a channel is
again a channel.  This packages Wolf Equation (6.13). -/
theorem peripheralWeightedProjection (hT : IsChannel T) :
    IsChannel T.peripheralWeightedProjection := by
  have hP := peripheralProjection hT
  constructor
  · exact hT.cp.comp hP.cp
  · intro X
    rw [Module.End.peripheralWeightedProjection, LinearMap.comp_apply, hT.tp, hP.tp]

end IsChannel

namespace IsPositiveMap

variable {D : ℕ} [NeZero D]
  {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- The peripheral projection absorbs the mean-ergodic projection:
`T_φ T_∞ = T_∞`.  This is the projection identity adjacent to Wolf Equation
(6.14). -/
theorem peripheralProjection_comp_meanErgodicProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    T.peripheralProjection.comp
        (LinearMap.meanErgodicProjection T (hPos.hasBoundedOrbits_of_tracePreserving hTP)) =
      LinearMap.meanErgodicProjection T (hPos.hasBoundedOrbits_of_tracePreserving hTP) := by
  let hb := hPos.hasBoundedOrbits_of_tracePreserving hTP
  let P := LinearMap.meanErgodicProjection T hb
  obtain ⟨n, -, -, hn⟩ := hPos.exists_strictMono_tendsto_pow_peripheralProjection hTP
  apply LinearMap.ext
  intro X
  change T.peripheralProjection (P X) = P X
  have hfixed : T (P X) = P X := by
    have h := LinearMap.congr_fun hb.comp_meanErgodicProjection X
    simpa only [LinearMap.comp_apply] using h
  have hpow : ∀ m : ℕ, (T ^ m) (P X) = P X := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hfixed]
  exact tendsto_nhds_unique (hn (P X)) <|
    (tendsto_const_nhds.congr' <| Filter.Eventually.of_forall fun i ↦ (hpow (n i)).symm)

end IsPositiveMap
