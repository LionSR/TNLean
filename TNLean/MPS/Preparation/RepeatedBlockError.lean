/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrthogonalBlockError
import TNLean.MPS.Preparation.RepeatedBlockSum

/-!
# The approximation error for orthogonal blocks with multiplicities

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound
the error of the approximating state of eq. (S7) for a tensor
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` that is not normal by
`ε = O((N/q) e^{-γ q/ξ_diag})` for `q = o(N)`. For a block of multiplicity `m_j ≥ 2` the state
of eq. (S7) does not approximate the target (`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`).

This file proves the bound for the corrected state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` of
`TNLean.MPS.Preparation.RepeatedBlockSum`, with `αⱼ = βⱼ / (∑ₗ |βₗ|²)^{1/2}` and
`βⱼ = ∑ₖ μ_{j,k}^N` as in the source, for arbitrary multiplicities and complex weights, when the
`q`-site states of distinct blocks are orthogonal: there is `C` such that `ε ≤ C y e^{C y}` with
`y = (N/q) e^{-γ q/ξ}` for every block length `q` at which the blocks are orthogonal and every
number of blocks `M ≥ 1` with the weights `βⱼ` not all zero
(`exists_approximationError_le_repeatedBlockSum`); in
`O`-form, `ε ≤ C y` (`exists_approximationError_le_mul_repeatedBlockSum`). As for multiplicity
one, no condition `q = o(N)` is needed.

The weights enter only through `pⱼ = |βⱼ|²`: after `V^{⊗M}` the corrected state is
`∑ⱼ αⱼ |φ_M(V_j P_{j,∞})⟩` and the target is `∑ⱼ βⱼ |φ_N(A_j)⟩`, and the estimate of the
multiplicity-one case applies block by block (`MPSTensor.one_sub_norm_sum_div_le`).

**Local fix (corrected fixed-point state):** the approximating state is the corrected state of
`TNLean.MPS.Preparation.RepeatedBlockSum`, not the state of eq. (S7), which fails for `m_j ≥ 2`.
Documented in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

**Scope restriction (orthogonal blocks):** Lemma 1'(ii) is proved for blocks whose `q`-site
states are orthogonal, a hypothesis the source does not state and without which the statement
fails. Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.copyApproxOverlap` — the overlap of the corrected approximating state with `φ_N`.
* `MPSTensor.norm_overlap_of_orthogonal` — the overlap of two weighted combinations of
  orthogonal families.
* `MPSTensor.norm_copyApproxOverlap_repeatedBlockSum` — the overlap as a weighted combination of
  the block overlaps.
* `MPSTensor.exists_approximationError_le_repeatedBlockSum`,
  `MPSTensor.exists_approximationError_le_mul_repeatedBlockSum` — Lemma 1'(ii) for the corrected
  state and orthogonal blocks with multiplicities.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, Lemma 1'(ii) (`eq:fid_err_gen_non_normal`).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}

/-! ### The overlap -/

/-- The overlap `⟨φ~_N|φ_N⟩` of the normalized corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` with the normalized periodic state `φ_N` of `A` on `N = qM` sites
read as `M` blocks of `q` sites; the error of arXiv:2307.01696, Supplemental Material,
Lemma 1', is `ε = 1 - |⟨φ~_N|φ_N⟩|`. -/
noncomputable def copyApproxOverlap (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) : ℂ :=
  ∑ τ, star (((Real.sqrt (∑ τ', ‖copyApproxVector A q M α L σ τ'‖ ^ 2) : ℂ)⁻¹) *
      copyApproxVector A q M α L σ τ) *
    normalizedMPVState A (M * q) (blockedConfigEquiv d M q τ)

/-- The overlap is the unnormalized overlap divided by the two norms. -/
theorem copyApproxOverlap_eq (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    copyApproxOverlap A q M α L σ =
      ((Real.sqrt (∑ τ, ‖copyApproxVector A q M α L σ τ‖ ^ 2) : ℂ)⁻¹ *
        (‖mpvState A (M * q)‖ : ℂ)⁻¹) *
        ∑ τ, star (copyApproxVector A q M α L σ τ) * mpv A (blockedConfigEquiv d M q τ) := by
  rw [copyApproxOverlap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [normalizedMPVState, star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal,
    PiLp.smul_apply, smul_eq_mul, mpvState_apply]
  ring

/-- **The overlap of two combinations of orthogonal families.** Let `sⱼ`, `tⱼ` be families with
`⟨sⱼ|s_{j'}⟩ = δ_{jj'}`, `⟨sⱼ|t_{j'}⟩ = δ_{jj'} zⱼ`, `⟨tⱼ|t_{j'}⟩ = δ_{jj'} cⱼ`, and let `β ≠ 0`
with `αⱼ = βⱼ / (∑ₗ |βₗ|²)^{1/2}`. Then the normalized overlap of `∑ⱼ αⱼ sⱼ` with `∑ⱼ βⱼ tⱼ` has
modulus `|∑ⱼ pⱼ zⱼ| / ((∑ⱼ pⱼ)^{1/2} (∑ⱼ pⱼ cⱼ)^{1/2})` with `pⱼ = |βⱼ|²`: arXiv:2307.01696,
Supplemental Material, proof of Lemma 1'(ii), with the cross terms equal to zero. -/
theorem norm_overlap_of_orthogonal {τs : Type*} [Fintype τs] {β : Fin b → ℂ} (hβ : β ≠ 0)
    (s t : Fin b → τs → ℂ) (z : Fin b → ℂ) (c : Fin b → ℝ)
    (hss : ∀ j j', ∑ τ, star (s j τ) * s j' τ = if j = j' then 1 else 0)
    (hst : ∀ j j', ∑ τ, star (s j τ) * t j' τ = if j = j' then z j else 0)
    (htt : ∀ j j', ∑ τ, star (t j τ) * t j' τ = if j = j' then (c j : ℂ) else 0) :
    ‖((Real.sqrt (∑ τ, ‖∑ j, ghzAmplitude β j * s j τ‖ ^ 2) : ℂ)⁻¹ *
        (Real.sqrt (∑ τ, ‖∑ j, β j * t j τ‖ ^ 2) : ℂ)⁻¹) *
        ∑ τ, star (∑ j, ghzAmplitude β j * s j τ) * ∑ j, β j * t j τ‖ =
      ‖∑ j, ((‖β j‖ ^ 2 : ℝ) : ℂ) * z j‖ /
        (Real.sqrt (∑ j, ‖β j‖ ^ 2) * Real.sqrt (∑ j, ‖β j‖ ^ 2 * c j)) := by
  set r : ℝ := Real.sqrt (∑ l, ‖β l‖ ^ 2)
  have hX : ∑ τ, ‖∑ j, ghzAmplitude β j * s j τ‖ ^ 2 = 1 := by
    have h := ofReal_sum_norm_sq fun τ => ∑ j, ghzAmplitude β j * s j τ
    rw [sum_star_sum_mul_sum_of_orthogonal _ _ (fun _ => 1) s s hss] at h
    simp only [mul_one, ghzAmplitude_norm_sq hβ] at h
    exact_mod_cast h
  have hY : ∑ τ, ‖∑ j, β j * t j τ‖ ^ 2 = ∑ j, ‖β j‖ ^ 2 * c j := by
    have h := ofReal_sum_norm_sq fun τ => ∑ j, β j * t j τ
    rw [sum_star_sum_mul_sum_of_orthogonal _ _ _ t t htt] at h
    refine Complex.ofReal_injective (h.trans ?_)
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have hZ : ∑ τ, star (∑ j, ghzAmplitude β j * s j τ) * ∑ j, β j * t j τ =
      (r : ℂ)⁻¹ * ∑ j, ((‖β j‖ ^ 2 : ℝ) : ℂ) * z j := by
    rw [sum_star_sum_mul_sum_of_orthogonal _ _ _ s t hst, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ghzAmplitude, star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div,
      Complex.conj_mul']
    push_cast
    ring
  rw [hX, hY, hZ, Real.sqrt_one]
  simp only [Complex.ofReal_one, inv_one, one_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [div_eq_inv_mul, mul_inv]
  ring

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- The overlap of the corrected approximating state with the target, for orthogonal blocks with
some nonzero weight whose blocked tensors are injective: with `pⱼ = |βⱼ|²`,
`zⱼ = ⟨φ_M(P_{j,∞})|φ_M(P_{j,q})⟩` and `cⱼ = ‖φ_N(A_j)‖²`,
`|⟨φ~_N|φ_N⟩| = |∑ⱼ pⱼ zⱼ| / ((∑ⱼ pⱼ)^{1/2} (∑ⱼ pⱼ cⱼ)^{1/2})`, whenever `β ≠ 0`. -/
theorem norm_copyApproxOverlap_repeatedBlockSum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} (hμ : ∀ j, μ j ≠ 0)
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1) {q : ℕ} (hq : q ≠ 0)
    (hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) (M : ℕ) [NeZero M]
    (hβ : bntWeight μ (M * q) ≠ 0) :
    ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M (ghzAmplitude (bntWeight μ (M * q)))
        (copyIsometry ι μ q) σ‖ =
      ‖∑ j, ((‖bntWeight μ (M * q) j‖ ^ 2 : ℝ) : ℂ) *
          mpvOverlap (polarPosTensor (blockTensor (Aj j) q)) (fixedPointTensor (σ j)) M‖ /
        (Real.sqrt (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2) *
          Real.sqrt (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2 * ‖mpvState (Aj j) (M * q)‖ ^ 2)) := by
  have : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  set N := M * q
  have hN : N ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hq
  set β := bntWeight μ N
  set A := repeatedBlockSum Aj ι μ
  set s : (j : Fin b) → (Fin M → Fin (blockPhysDim d q)) → ℂ :=
    fun j τ => mpv (approximatingTensor (blockTensor (Aj j) q) (σ j)) τ
  set t : (j : Fin b) → (Fin M → Fin (blockPhysDim d q)) → ℂ :=
    fun j τ => mpv (Aj j) (blockedConfigEquiv d M q τ)
  have hS : ∀ τ, copyApproxVector A q M (ghzAmplitude β) (copyIsometry ι μ q) σ τ =
      ∑ j, ghzAmplitude β j * s j τ := fun τ =>
    copyApproxVector_repeatedBlockSum hι hdisj hμ hq horth σ M _ τ
  have hT : ∀ τ, mpv A (blockedConfigEquiv d M q τ) = ∑ j, β j * t j τ := fun τ =>
    mpv_repeatedBlockSum hι hdisj μ hN _
  -- Cross terms vanish.
  have hss : ∀ j j', ∑ τ, star (s j τ) * s j' τ = if j = j' then 1 else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact mpv_approximatingTensor_norm_sq (hB j) (hσ j) (htr j)
    · have := mpvOverlap_eq_zero (X := approximatingTensor (blockTensor (Aj j') q) (σ j'))
        (Y := approximatingTensor (blockTensor (Aj j) q) (σ j))
        (conjTranspose_physicalMatrix_approximatingTensor_mul (horth j j' h) _ _)
        (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  have hst : ∀ j j', ∑ τ, star (s j τ) * t j' τ = if j = j' then
      mpvOverlap (polarPosTensor (blockTensor (Aj j) q)) (fixedPointTensor (σ j)) M
      else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact sum_star_mpv_approximatingTensor_mul_mpv (Aj j) (hB j) (σ j) M
    · have := mpvOverlap_eq_zero (X := blockTensor (Aj j') q)
        (Y := approximatingTensor (blockTensor (Aj j) q) (σ j))
        (conjTranspose_physicalMatrix_approximatingTensor_mul_blocked (horth j j' h) _)
        (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => by
        rw [mul_comm]; simp only [s, t, mpv_blockedConfigEquiv]
  have htt : ∀ j j', ∑ τ, star (t j τ) * t j' τ = if j = j' then
      ((‖mpvState (Aj j) N‖ ^ 2 : ℝ) : ℂ) else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact sum_star_mpv_blockedConfigEquiv (Aj j) q M
    · have := mpvOverlap_eq_zero (X := blockTensor (Aj j') q) (Y := blockTensor (Aj j) q)
        (horth j j' h) (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => by
        rw [mul_comm]; simp only [t, mpv_blockedConfigEquiv]
  -- The norm of the target, read in blocks.
  have hnorm : ‖mpvState A N‖ = Real.sqrt (∑ τ, ‖∑ j, β j * t j τ‖ ^ 2) := by
    have h := sum_star_mpv_blockedConfigEquiv A q M
    rw [← ofReal_sum_norm_sq (fun τ => mpv A (blockedConfigEquiv d M q τ))] at h
    rw [Complex.ofReal_injective h, Real.sqrt_sq (norm_nonneg _)]
    simp only [hT]
  rw [copyApproxOverlap_eq, hnorm]
  simp only [hS, hT]
  exact norm_overlap_of_orthogonal hβ s t _ _ hss hst htt

/-! ### The error bound -/

/-- **Approximation error for orthogonal blocks with multiplicities** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected approximating state and in the
scope of the module docstring). Let `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)), the
copy `k` of block `j` placed on the bond coordinates `ι_{j,k}`, with some nonzero weight in every
block, let every block `A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`,
`σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound the moduli of the eigenvalues other than `1` of
every transfer map `E_{A_j}`, so that `ξ = -1/log|λ₂|` bounds the correlation lengths `ξ_jj`, and
let `0 < γ < 1/2`. There is `C > 0` such that for every block length `q` at which the `q`-site
states of distinct blocks are orthogonal, `B_jᴴ B_{j'} = 0`, and every number of blocks
`M ≥ 1` with `N = qM` and `βⱼ = ∑ₖ μ_{j,k}^N` not all zero (eq. (S4)), the
error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` satisfies `ε ≤ C y e^{C y}` with `y = (N/q) e^{-γ q/ξ}`. -/
theorem exists_approximationError_le_repeatedBlockSum [NeZero b]
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} (hμ : ∀ j, μ j ≠ 0)
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  choose C₁ hC₁ hover using fun j =>
    exists_norm_mpvOverlap_polarPosTensor_sub_one_le (Aj j) (hN j) (hA j) (hσ j) (htr j)
      (hfix j) (hlam j) hγ0 hγ
  choose K₅ hK₅ hc using fun j =>
    exists_abs_norm_mpvState_sq_sub_one_le (Aj j) (hN j) (hA j) (hσ j) (htr j) (hfix j)
      (hlam j) hγ0 hγ
  choose L hLpos hL using hN
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx : 0 < x := Real.exp_pos _
  set S₁ := ∑ j, C₁ j
  set S₂ := ∑ j, K₅ j
  set S₃ := ∑ j, (x ^ L j)⁻¹
  have hS₁ : 0 ≤ S₁ := Finset.sum_nonneg fun j _ => (hC₁ j).le
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg fun j _ => hK₅ j
  have hS₃ : 0 ≤ S₃ := Finset.sum_nonneg fun j _ => by positivity
  set C := 2 * (S₁ + S₂) + S₃ + 1
  refine ⟨C, by positivity, fun q M _ horth hβ => ?_⟩
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hu : 0 ≤ u := by positivity
  have hexp : 1 ≤ Real.exp (C * u) := Real.one_le_exp (by positivity)
  set ov := copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
    (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ
  have hε1 : 1 - ‖ov‖ ≤ 1 := by linarith [norm_nonneg ov]
  by_cases hbig : 1 ≤ C * u
  · exact hε1.trans (hbig.trans (le_mul_of_one_le_right (by positivity) hexp))
  rw [not_le] at hbig
  have hx1 : x < 1 := by
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ u := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ h)
    have : 1 ≤ C := by linarith
    nlinarith
  have hLq : ∀ j, L j ≤ q := fun j => by
    by_contra h
    rw [not_le] at h
    have hxLq : x ^ L j ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le h.le
    have h1 : x ^ L j ≤ u := hxLq.trans (le_mul_of_one_le_left (by positivity) hM)
    have h2 : 1 ≤ (x ^ L j)⁻¹ * u := by
      rw [← inv_mul_cancel₀ (by positivity : x ^ L j ≠ 0)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (x ^ L j)⁻¹ ≤ S₃ :=
      Finset.single_le_sum (f := fun j => (x ^ L j)⁻¹) (fun j _ => by positivity)
        (Finset.mem_univ j)
    have h4 : (x ^ L j)⁻¹ * u ≤ C * u := mul_le_mul_of_nonneg_right (by linarith) hu
    linarith
  have hq : q ≠ 0 := fun h => by have := hLq 0; have := hLpos 0; omega
  have hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q) := fun j =>
    (isNBlkInjective_iff_blockTensor_isInjective (Aj j) q).1
      (isNBlkInjective_of_le (hLpos j) (hL j) (hLq j))
  have hnorm := norm_copyApproxOverlap_repeatedBlockSum hι hdisj hμ
    (fun j => (hσ j).posSemidef) htr hq hB horth M hβ
  change ‖ov‖ = _ at hnorm
  have hp : 0 < ∑ j, ‖bntWeight μ (M * q) j‖ ^ 2 := by
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hβ
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hl) 2)
      (Finset.single_le_sum (f := fun j => ‖bntWeight μ (M * q) j‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ l))
  have hmain := one_sub_norm_sum_div_le (fun j => ‖bntWeight μ (M * q) j‖ ^ 2)
    (fun j => by positivity) hp
    (fun j => mpvOverlap (polarPosTensor (blockTensor (Aj j) q)) (fixedPointTensor (σ j)) M)
    (fun j => ‖mpvState (Aj j) (M * q)‖ ^ 2)
  rw [← hnorm] at hmain
  refine hmain.trans ?_
  -- Each block contributes at most `C₁ u e^{C₁ u} + K₅ u`.
  have hblock : ∀ j, ‖mpvOverlap (polarPosTensor (blockTensor (Aj j) q))
      (fixedPointTensor (σ j)) M - 1‖ + |‖mpvState (Aj j) (M * q)‖ ^ 2 - 1| ≤
      C₁ j * u * Real.exp (S₁ * u) + K₅ j * u := fun j => by
    have h1 := hover j q M
    rw [hxq] at h1
    have h1' : C₁ j * u * Real.exp (C₁ j * u) ≤ C₁ j * u * Real.exp (S₁ * u) := by
      have : C₁ j ≤ S₁ := Finset.single_le_sum (f := C₁) (fun j _ => (hC₁ j).le)
        (Finset.mem_univ j)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right this hu))
        (mul_nonneg (hC₁ j).le hu)
    have h2 : |‖mpvState (Aj j) (M * q)‖ ^ 2 - 1| ≤ K₅ j * u := by
      refine (hc j (M * q)).trans (mul_le_mul_of_nonneg_left ?_ (hK₅ j))
      calc (x ^ 2) ^ (M * q) = x ^ (2 * (M * q)) := (pow_mul _ _ _).symm
        _ ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le (by
            have := Nat.one_le_iff_ne_zero.2 (NeZero.ne M); nlinarith)
        _ ≤ u := le_mul_of_one_le_left (by positivity) hM
    linarith
  calc 2 * ∑ j, (‖mpvOverlap (polarPosTensor (blockTensor (Aj j) q))
        (fixedPointTensor (σ j)) M - 1‖ + |‖mpvState (Aj j) (M * q)‖ ^ 2 - 1|)
      ≤ 2 * ∑ j, (C₁ j * u * Real.exp (S₁ * u) + K₅ j * u) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hblock j) (by norm_num)
    _ = 2 * (S₁ * u * Real.exp (S₁ * u) + S₂ * u) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ C * u * Real.exp (C * u) := by
        have hS₁C : S₁ ≤ C := by linarith
        have he : Real.exp (S₁ * u) ≤ Real.exp (C * u) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hS₁C hu)
        have h1 : S₁ * u * Real.exp (S₁ * u) ≤ S₁ * u * Real.exp (C * u) := by gcongr
        have h2 : S₂ * u ≤ S₂ * u * Real.exp (C * u) :=
          le_mul_of_one_le_right (by positivity) hexp
        have h3 : 2 * (S₁ + S₂) * u * Real.exp (C * u) ≤ C * u * Real.exp (C * u) := by
          gcongr; linarith
        nlinarith

/-- **Approximation error for orthogonal blocks with multiplicities, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected
approximating state): in the setting of `exists_approximationError_le_repeatedBlockSum`, there is
`C` with `ε ≤ C (N/q) e^{-γ q/ξ}` for every block length `q` at which the `q`-site states of
distinct blocks are orthogonal and every number of blocks `M ≥ 1` with the weights `βⱼ` not all
zero. -/
theorem exists_approximationError_le_mul_repeatedBlockSum [NeZero b]
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} (hμ : ∀ j, μ j ≠ 0)
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedBlockSum hι hdisj hμ hN hA hσ htr
    hfix hlam hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ horth hβ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M horth hβ) ?_
  linarith [norm_nonneg (copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
    (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ)]

end MPSTensor
