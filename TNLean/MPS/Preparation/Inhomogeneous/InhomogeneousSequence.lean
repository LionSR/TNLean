/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.Inhomogeneous.PartialIsometryPreparation
import TNLean.MPS.Preparation.Circuit.ShortChainPreparation
import TNLean.MPS.Tensor.InjectivityCutoff

/-!
# Inhomogeneous preparation with finitely many short rings

A positive logarithmic lower bound on the block lengths makes every block at least `3D`
for all sufficiently large rings. Every exceptional ring is prepared exactly by the finite
unitary synthesis of `exists_isPreparedInDepth_of_norm_eq_one`; its depth is absorbed into
one constant independent of the ring and its tensors. A one-site state is already a product.

The approximation hypotheses are those of `VaryingBondChain.IsPairApproximable`, with no
injectivity assumption.

**Scope restriction (positive block growth):** the positive logarithmic lower bound is an
explicit extra hypothesis: an upper bound `q = O(log N)` alone does not imply growth.
The conclusion is depth `O(L_N)` and error at most `δ_N`. It does not assert an
accuracy-dependent depth `O(log(N/ε))` from
`δ_N → 0` without a uniform error rate. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Main results

* `exists_isPreparedInDepth_inhomogeneous_of_log_lower`: one uniform depth bound for every
  positive ring length, with exact preparation below a fixed threshold.
* `exists_isPreparedInDepth_inhomogeneous_sequence`: logarithmic-depth sequence preparation
  with errors tending to zero.
* `MPSPreparation.exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate_from`,
  `MPSPreparation.exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate`: accuracy-dependent
  inhomogeneous preparation under a uniform decay rate.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
* `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`, block-length elimination argument.

## Exact linear-depth preparation of inhomogeneous matrix product states

A nonzero inhomogeneous state with fixed bond bound `D` can be prepared exactly in depth
`O(N)`. Treat the entire ring as one block, normalize its positive-part state, and regard
that `D²`-dimensional vector as one entangled pair. The isometric extension of the polar
factor prepares the target exactly. No injectivity or spectral assumption is required.

This controls the short-chain branch `N < q` when an accuracy-dependent blocking length
exceeds the whole ring. Generic finite-dimensional synthesis is used only for the fixed
finite set `N < 3D`, not for arbitrarily long chains.

### Main result

* `exists_isPreparedInDepth_normalizedChainState`: exact preparation in depth at most `C N`,
  uniformly over all nonzero chains of fixed bond dimension.

### References

* arXiv:2307.01696, paragraphs "The sequential-RG circuit" (including its footnote on
  non-injective tensors) and "Inhomogeneous short-range correlated MPS".
-/

section InhomogeneousSequence

section

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- A logarithmic lower bound with positive coefficient eventually exceeds the register
length `3D`. The threshold depends only on `D` and the coefficient, not on the block schedule. -/
theorem exists_threshold_three_mul_le_of_log (D : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N q : ℕ, N₀ ≤ N → c * Real.log N ≤ q → 3 * D ≤ q := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp ((3 * D : ℝ) / c))
  refine ⟨N₀, fun N q hN hq => ?_⟩
  have hN' : Real.exp ((3 * D : ℝ) / c) < N :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans hN'
  have hlog := (Real.le_log_iff_exp_le hNpos).2 hN'.le
  have hbound : (3 * D : ℝ) ≤ c * Real.log N := by
    have := (div_le_iff₀ hc).1 hlog
    nlinarith
  exact_mod_cast hbound.trans hq

/-- Every vector on one site is a product vector, so no gates are needed. -/
theorem isPreparedInDepth_zero_one_site {d : ℕ} (ψ : Cfg d 1 → ℂ) :
    IsPreparedInDepth (Geometry.ring 1) 0 ψ := by
  refine ⟨1, IsUnitaryCircuit.one _ _ 0, fun _ a => ψ (fun _ => a), funext fun s => ?_⟩
  simp only [Matrix.one_mulVec, Fin.prod_univ_one]
  exact congrArg ψ (funext fun i => congrArg s (Subsingleton.elim _ _))

/-- **All positive ring lengths with logarithmically growing blocks.** There are a threshold
`N₀` and a depth constant `C`, depending only on `d`, `D` and `c > 0`, such that any ring
whose block lengths satisfy `c log N ≤ ℓ k ≤ L` and whose positive parts are approximable
by pairs with error `δ` admits a unit state of depth at most `C L` and error at most `δ`.
For `N < N₀` the prepared state is exactly the normalized target state.

The exceptional rings use bounded finite-dimensional unitary synthesis, not an assumption of
exact preparation. No blocked-tensor injectivity is required. This is the finite-exception
argument for the inhomogeneous paragraph of arXiv:2307.01696 under the positive lower-growth
hypothesis recorded in the module docstring. -/
theorem exists_isPreparedInDepth_inhomogeneous_of_log_lower (d D : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) :
    ∃ C N₀ : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (A : VaryingBondChain d D N) (L : ℕ) (δ : ℝ),
      (∀ k, c * Real.log N ≤ ℓ k) → (∀ k, ℓ k ≤ L) → IsPairApproximable A hN δ →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ T ≤ C * L ∧
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ δ ∧
        (N < N₀ → ψ = (‖state A‖ : ℂ)⁻¹ • state A) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_threshold_three_mul_le_of_log D hc
  obtain ⟨K, hK⟩ := exists_isPreparedInDepth_of_norm_eq_one hd N₀
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_of_isPairApproximable d D
  refine ⟨max C K, N₀, fun ℓ N _ hN A L δ hlog hL hA => ?_⟩
  have hLpos : 0 < L := by
    by_contra h
    have hzero : ∀ k, ℓ k = 0 := fun k => Nat.eq_zero_of_le_zero (by have := hL k; omega)
    simp only [hzero, Finset.sum_const_zero] at hN
    exact NeZero.ne N hN.symm
  by_cases hshort : N < N₀
  · obtain ⟨hne, ω, hω, hδ⟩ := hA
    have hn : ‖state A‖ ≠ 0 := by
      rw [state_eq_chainState, norm_chainState_eq _ hN]
      exact norm_ne_zero_iff.mpr hne
    have hunit : ‖(‖state A‖ : ℂ)⁻¹ • state A‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ hn]
    have hδ0 : 0 ≤ δ := by
      have hu : ‖(‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ •
          chainPosState (zeroPad A) hN‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
      have hle := norm_inner_le_norm (𝕜 := ℂ) (pairFamilyVector (padPairs A ℓ ω))
        ((‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ • chainPosState (zeroPad A) hN)
      rw [hu, norm_pairFamilyVector (sum_star_padPairs_mul_self A ℓ hω), mul_one] at hle
      linarith
    have herr : 1 - ‖⟪(‖state A‖ : ℂ)⁻¹ • state A,
        (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ δ := by
      rw [inner_self_eq_norm_sq_to_K, hunit]
      simpa using hδ0
    by_cases hN1 : N = 1
    · subst hN1
      refine ⟨_, 0, hunit, Nat.zero_le _, ?_, herr, fun _ => rfl⟩
      exact isPreparedInDepth_zero_one_site (d := d)
        (fun s => ((‖state A‖ : ℂ)⁻¹ • state A) s)
    · refine ⟨_, K, hunit, ?_, hK N (by have := NeZero.ne N; omega) hshort.le _ hunit,
        herr, fun _ => rfl⟩
      exact (le_max_right C K).trans (Nat.le_mul_of_pos_right _ hLpos)
  · obtain ⟨ψ, hψ, hprep, herr⟩ := hC ℓ hN A L δ
      (fun k => hN₀ N (ℓ k) (by omega) (hlog k)) hL hA
    exact ⟨ψ, C * L, hψ, Nat.mul_le_mul_right L (le_max_left C K), hprep, herr,
      fun h => (hshort h).elim⟩

/-- **Vanishing error for an inhomogeneous sequence, including every short ring.**
For rings of `n + 1` sites whose block lengths have a positive logarithmic lower bound,
pair approximation with errors `δ n → 0` gives prepared unit states with errors tending to
zero and depths at most `C * L n`, for one constant `C`. Below one fixed threshold the states
are prepared exactly. A logarithmic upper bound on `L` gives logarithmic preparation depth,
without discarding finitely many members of the sequence.

The error rate is left as supplied by the sequence; no uniform exponential rate in the block
length is inferred from convergence alone. -/
theorem exists_isPreparedInDepth_inhomogeneous_sequence (d D : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) (M L : ℕ → ℕ) [∀ n, NeZero (M n)]
    (ℓ : ∀ n, Fin (M n) → ℕ) (hN : ∀ n, ∑ k, ℓ n k = n + 1)
    (A : ∀ n, VaryingBondChain d D (n + 1)) (δ : ℕ → ℝ)
    (hlower : ∀ n k, c * Real.log (n + 1 : ℕ) ≤ ℓ n k)
    (hupper : ∀ n k, ℓ n k ≤ L n)
    (happrox : ∀ n, IsPairApproximable (A n) (hN n) (δ n))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hL : Asymptotics.IsBigO Filter.atTop (fun n => (L n : ℝ))
      (fun n => Real.log (n + 1 : ℕ))) :
    ∃ (C N₀ : ℕ) (ψ : ∀ n, MPVSpace d (n + 1)) (T : ℕ → ℕ),
      (∀ n, ‖ψ n‖ = 1 ∧ T n ≤ C * L n ∧
        IsPreparedInDepth (Geometry.ring (n + 1)) (T n) (fun s => ψ n s) ∧
        1 - ‖⟪ψ n, (‖state (A n)‖ : ℂ)⁻¹ • state (A n)⟫_ℂ‖ ≤ δ n ∧
        (n + 1 < N₀ → ψ n = (‖state (A n)‖ : ℂ)⁻¹ • state (A n))) ∧
      Filter.Tendsto
        (fun n => 1 - ‖⟪ψ n, (‖state (A n)‖ : ℂ)⁻¹ • state (A n)⟫_ℂ‖)
        Filter.atTop (nhds 0) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
        (fun n => Real.log (n + 1 : ℕ)) := by
  classical
  obtain ⟨C, N₀, hC⟩ := exists_isPreparedInDepth_inhomogeneous_of_log_lower d D hd hc
  choose ψ T hψ using fun n =>
    hC (ℓ n) (hN n) (A n) (L n) (δ n) (hlower n) (hupper n) (happrox n)
  have hdepth : Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
      (fun n => (L n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun n => ?_)
    simp only [Real.norm_natCast]
    exact_mod_cast (hψ n).2.1
  refine ⟨C, N₀, ψ, T, hψ, ?_, hdepth.trans hL⟩
  refine squeeze_zero (fun n => ?_) (fun n => (hψ n).2.2.2.1) hδ
  have hn : ‖state (A n)‖ ≠ 0 := by
    rw [state_eq_chainState, norm_chainState_eq _ (hN n)]
    exact norm_ne_zero_iff.mpr (happrox n).1
  have hu : ‖(‖state (A n)‖ : ℂ)⁻¹ • state (A n)‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hn]
  have hle := norm_inner_le_norm (𝕜 := ℂ) (ψ n)
    ((‖state (A n)‖ : ℂ)⁻¹ • state (A n))
  rw [(hψ n).1, hu, mul_one] at hle
  exact sub_nonneg.mpr hle

end MPSPreparation

end

section

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- **Exact preparation in linear depth.** For fixed physical dimension `d ≥ 1` and bond
bound `D`, there is `C` such that every nonzero inhomogeneous chain state on a positive ring
of `N` sites has a normalized state prepared in depth at most `C N`. No injectivity is assumed.

The sequential circuit of arXiv:2307.01696 is applied to one block covering the ring, with
its normalized positive-part state as the initial pair. -/
theorem exists_isPreparedInDepth_normalizedChainState (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (N : ℕ) [NeZero N] (A : MPSChainTensor d D N), chainState A ≠ 0 →
      ∃ T : ℕ, T ≤ C * N ∧
        IsPreparedInDepth (Geometry.ring N) T
          (fun s => ((‖chainState A‖ : ℂ)⁻¹ • chainState A) s) := by
  classical
  by_cases hd1 : d ≤ 1
  · exact ⟨0, fun N _ A _ => ⟨0, by simp, isPreparedInDepth_zero_of_le_one hd1 _⟩⟩
  have hd2 : 2 ≤ d := by omega
  have hDD : D * D ≤ d ^ (3 * D) := by
    have h : D ≤ d ^ D := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hd2 D)
    calc D * D ≤ d ^ D * d ^ D := Nat.mul_le_mul h h
      _ = d ^ (2 * D) := by rw [← pow_add]; ring_nf
      _ ≤ d ^ (3 * D) := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_blockMatVector d D hDD
  obtain ⟨K, hK⟩ := exists_isPreparedInDepth_of_norm_eq_one hd (3 * D)
  refine ⟨max C K, fun N _ A hA => ?_⟩
  have hunit : ‖(‖chainState A‖ : ℂ)⁻¹ • chainState A‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]
  by_cases hN : 3 * D ≤ N
  · have hsum : ∑ _ : Fin 1, N = N := by simp
    let Y : MPVSpace (D * D) 1 := (‖chainState A‖ : ℂ)⁻¹ • chainPosState A hsum
    have hY : ‖Y‖ = 1 := by
      dsimp only [Y]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        ← norm_chainState_eq A hsum, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]
    let e : Fin D × Fin D ≃ Cfg (D * D) 1 :=
      (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (Equiv.funUnique (Fin 1) _).symm)
    let ω : Fin D × Fin D → ℂ := fun p => Y (e p)
    have hω : ∑ p, star (ω p) * ω p = 1 := by
      change ∑ p, star (Y (e p)) * Y (e p) = 1
      rw [e.sum_comp (fun τ => star (Y τ) * Y τ), sum_star_mul_self_eq_norm_sq, hY]
      norm_num
    have hpair : pairFamilyVector (fun _ : Fin 1 => ω) = Y := by
      ext τ
      rw [pairFamilyVector_apply]
      simp only [pairFamilyState, Fin.prod_univ_one]
      have h1 : finRotate 1 0 = 0 := Subsingleton.elim _ _
      have he : e ((finProdFinEquiv.symm (τ 0)).2,
          (finProdFinEquiv.symm (τ 0)).1) = τ := by
        funext k
        rw [Subsingleton.elim k 0]
        change finProdFinEquiv (finProdFinEquiv.symm (τ 0)) = τ 0
        exact Equiv.apply_symm_apply _ _
      rw [h1]
      exact congrArg Y he
    obtain ⟨W, _, hW, hprep⟩ := hC (fun _ : Fin 1 => N) hsum A (fun _ => ω)
      (fun _ => hω) N (fun _ => hN) (fun _ => le_rfl)
    rw [hpair] at hprep
    dsimp only [Y] at hprep
    rw [blockMatVector_smul, ← chainState_eq_blockMatVector hsum hW] at hprep
    exact ⟨C * N, Nat.mul_le_mul_right N (le_max_left C K), hprep⟩
  · by_cases hN1 : N = 1
    · subst hN1
      refine ⟨0, Nat.zero_le _, ?_⟩
      exact isPreparedInDepth_zero_one_site (d := d)
        (fun s => ((‖chainState A‖ : ℂ)⁻¹ • chainState A) s)
    · refine ⟨K, ?_, hK N (by have := NeZero.ne N; omega) (by omega) _ hunit⟩
      exact (le_max_right C K).trans
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne N)))

end MPSPreparation

end

end InhomogeneousSequence

section InhomogeneousUniformRate

/-!
## Accuracy-dependent inhomogeneous preparation under a uniform decay rate

An explicit pair-approximation bound `K N^k exp(-r q)`, with constants independent of the
ring length, gives preparation depth `O(log(N/ε))` at every positive ring length and every
`0 < ε ≤ 1`. Blocks have lengths between `q` and `2q`, so no divisibility assumption is
needed. If the chosen `q` exceeds `N`, exact linear-depth inhomogeneous preparation applies.

**Scope restriction (uniform rate):** arXiv:2307.01696 defines the inhomogeneous sequence by
convergence of its pair-approximation errors, without deriving the uniform exponential bound
assumed here. This is a conditional accuracy-dependent theorem, not a proof of that bound
from the source's finite-correlation definition. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

### Main result

* `exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate`: the conditional
  accuracy-dependent depth bound, including every positive ring length.

### References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" and the choice of
  logarithmic blocking after Lemma 1 in the translation-invariant case.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- A uniform pair-approximation rate on the original family for lengths `N ≥ N₀`
gives physical depth `O(log(N/ε))` on that same range. Short blocking scales still use
the exact preparation branch, without altering any member of the family.

The rate is an additional quantitative hypothesis in arXiv:2307.01696's inhomogeneous
setting; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate_from
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, VaryingBondChain d D N)
    (K r : ℝ) (k : ℕ) (hK : 0 < K) (hr : 0 < r) (N₀ : ℕ)
    (hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N → N₀ ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (A N) hN (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖state (A N)‖ : ℂ)⁻¹ • state (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_of_isPairApproximable d D
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedChainState d D hd
  let a : ℝ := max (k : ℝ) 1 / r
  let b : ℝ := max (Real.log K) 0 / r + 3 * D + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 1 ≤ b := by
    have : 0 ≤ max (Real.log K) 0 / r + 3 * D := by positivity
    dsimp [b]
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let c₀ := a + b / Real.log 2
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hc : 0 ≤ 4 * Cb * c₀ + Ce * c₀ := by positivity
  refine ⟨4 * Cb * c₀ + Ce * c₀, fun ε hε hε1 N _ hN₀ => ?_⟩
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hn : ‖state (A N)‖ ≠ 0 := by
    obtain ⟨M, _, ℓ, hsum, _, _, hA⟩ := hrate N N hNpos le_rfl hN₀
    rw [state_eq_chainState, norm_chainState_eq _ hsum]
    exact norm_ne_zero_iff.mpr hA.1
  have hu : ‖(‖state (A N)‖ : ℂ)⁻¹ • state (A N)‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hn]
  have hself : 1 - ‖⟪(‖state (A N)‖ : ℂ)⁻¹ • state (A N),
      (‖state (A N)‖ : ℂ)⁻¹ • state (A N)⟫_ℂ‖ ≤ ε := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    simpa using hε.le
  by_cases hN1 : N = 1
  · subst N
    refine ⟨_, 0, hu, ?_, isPreparedInDepth_zero_one_site _, hself⟩
    have hlog : 0 ≤ Real.log ((1 : ℝ) / ε) :=
      Real.log_nonneg ((one_le_div hε).2 hε1)
    simpa using mul_nonneg hc hlog
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  let Q := a * Real.log (N / ε) + b
  have hQ1 : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hQc : Q ≤ c₀ * Real.log (N / ε) := by
    have hbl : b ≤ b / Real.log 2 * Real.log (N / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlog (zero_le_one.trans hb)
    dsimp [Q, c₀]
    rw [add_mul]
    linarith
  let q := ⌈Q⌉₊
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hq0 : 0 < q := by exact_mod_cast (show (0 : ℝ) < q by linarith)
  by_cases hqN : q ≤ N
  · obtain ⟨M, hM, ℓ, hsum, hℓq, hℓ2q, happ⟩ := hrate N q hq0 hqN hN₀
    let : NeZero M := ⟨hM.ne'⟩
    have h3Dq : 3 * D ≤ q := by
      have hbD : (3 * D : ℝ) ≤ b := by
        have : 0 ≤ max (Real.log K) 0 / r := by positivity
        dsimp [b]
        linarith
      have hDq : (3 * D : ℝ) ≤ q := by dsimp [Q] at hQq; nlinarith
      exact_mod_cast hDq
    obtain ⟨ψ, hψ, hprep, herr⟩ := hCb ℓ hsum (A N) (2 * q)
      (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))
      (fun j => h3Dq.trans (hℓq j)) hℓ2q happ
    refine ⟨ψ, Cb * (2 * q), hψ, ?_, hprep, herr.trans ?_⟩
    · push_cast
      have hCb0 : (0 : ℝ) ≤ Cb := Nat.cast_nonneg _
      have hCe : 0 ≤ Ce * c₀ * Real.log (N / ε) := by positivity
      calc (Cb : ℝ) * (2 * q) ≤ 4 * Cb * Q := by nlinarith
        _ ≤ 4 * Cb * (c₀ * Real.log (N / ε)) := by gcongr
        _ ≤ (4 * Cb * c₀ + Ce * c₀) * Real.log (N / ε) := by nlinarith
    · exact mul_pow_mul_exp_neg_le_of_le hK hr (by linarith) hε hε1
        (le_refl a) (by dsimp [b]; have := Nat.cast_nonneg (α := ℝ) D; linarith) hQq
  · obtain ⟨T, hT, hprep⟩ := hCe N (zeroPad (A N)) (by
      rw [← state_eq_chainState]
      exact norm_ne_zero_iff.mp hn)
    refine ⟨_, T, hu, ?_, ?_, hself⟩
    · have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
      have hT' : (T : ℝ) ≤ Ce * N := by exact_mod_cast hT
      have hCe0 : (0 : ℝ) ≤ Ce := Nat.cast_nonneg _
      have hCextra : 0 ≤ 4 * Cb * c₀ * Real.log (N / ε) := by positivity
      calc (T : ℝ) ≤ Ce * N := hT'
        _ ≤ Ce * Q := by gcongr
        _ ≤ Ce * (c₀ * Real.log (N / ε)) := by gcongr
        _ ≤ (4 * Cb * c₀ + Ce * c₀) * Real.log (N / ε) := by nlinarith
    · simpa only [← state_eq_chainState] using hprep

/-- **Depth `O(log(N/ε))` under a uniform exponential pair-approximation rate.**
Suppose at every scale `1 ≤ q ≤ N` one family of inhomogeneous chains has a partition
with block lengths between `q` and `2q` and pair-approximation error at most
`K N^k exp(-r q)`, where `K,r > 0` and `k` are independent of the ring length. Then every
normalized target state has an approximation of error at most `ε` prepared in depth at most
`C log(N/ε)`, for one
constant `C` and all positive ring lengths and `0 < ε ≤ 1`.

The uniform rate is an additional hypothesis, not a consequence proved here of the source's
finite-correlation assumption. See the scope restriction in the module docstring. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, VaryingBondChain d D N)
    (K r : ℝ) (k : ℕ) (hK : 0 < K) (hr : 0 < r)
    (hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (A N) hN (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖state (A N)‖ : ℂ)⁻¹ • state (A N)⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate_from
    d D hd A K r k hK hr 0 (fun N _ q hq hqN _ => hrate N q hq hqN)
  exact ⟨C, fun ε hε hε1 N _ => hC ε hε hε1 N (Nat.zero_le N)⟩

end MPSPreparation

end InhomogeneousUniformRate
