/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.PrimeLengthNormalBlocks
import TNLean.MPS.ParentHamiltonian.FiniteVolumeConstraintPropagation
import TNLean.MPS.ParentHamiltonian.Nonvanishing

/-!
# A quantitative prime-length bond-dimension dichotomy

For one fixed positive local interaction with a one-dimensional zero-energy
space at every permitted volume, one sufficiently small prime-length MPS
representation supplies a single fixed tensor generating the ground space
at every sufficiently large volume. Otherwise every nonzero prime-length
representation obeys the explicit fifth-degree obstruction.

All periodic/canonical reduction, phase grouping, block injectivity, local
annihilation, future-volume equations and eventual nonvanishing are derived.
**Scope restriction (eventual uniform branch):** the fixed tensor generates
all sufficiently large ground spaces. The finite-prefix representation step
for a literal all-volume uniform-dimension formulation is separate. See
`docs/paper-gaps/spwc10_ground_state_dichotomy_quantifiers.tex`.

Source: SPWC10, arXiv:0909.5347, Theorem 5 and proof, lines 850–880 of
`Papers/0909.5347/main.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d L : ℕ}

/-- A small prime-length ground-state representation yields a single fixed
normal MPS tensor, its actual local-kernel inclusion, and its generation
of the ground space at all sufficiently large volumes. The explicit threshold
uses the general Wielandt length \((D^2+1)^2\).
Source: SPWC10, Theorem 5 proof, lines 858–880. -/
theorem exists_normal_eventual_ground_data_of_prime_length_bound
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hUnique : ∀ M, L ≤ M →
      Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1)
    {D N : ℕ} (A : MPSTensor d D) (hPrime : N.Prime)
    (hBound : L + max ((D ^ 2 + 1) ^ 2)
      (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) ≤ N)
    (hA : mpvState A N ≠ 0)
    (hzero : periodicInteractionHamiltonianES h N (mpvState A N) = 0) :
    ∃ D₀ : ℕ, 0 < D₀ ∧ D₀ ≤ D ∧ ∃ B : MPSTensor d D₀,
      Kraus.IsNormal B ∧ groundSpaceES B L ≤ LinearMap.ker h ∧ ∃ M₀ : ℕ,
      ∀ M, M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M := by
  classical
  let q : ℕ := (D ^ 2 + 1) ^ 2
  change L + max q (3 * (D - 1) * (q + 1)) ≤ N at hBound
  have hq : 0 < q := by dsimp [q]; positivity
  have hDq : D < q := by
    have h₁ := Nat.le_self_pow (by decide : 2 ≠ 0) D
    have h₂ := Nat.le_self_pow (by decide : 2 ≠ 0) (D ^ 2 + 1)
    dsimp [q]
    omega
  have hDN : D < N := hDq.trans_le ((le_max_left _ _).trans (by omega))
  obtain ⟨r, dim, B, c, hdim, hdimD, hrD, hunital, hDual, hIrr,
      hC1, hDistinct, hc, hdecomp⟩ :=
    exists_normal_blocks_of_no_small_divisor A hPrime.two_le
      (fun m hm2 hmD hdiv =>
        (hPrime.eq_one_or_self_of_dvd m hdiv).elim (by omega) (by omega))
  have hsum : mpvState A N = ∑ j, c j • mpvState (B j) N := by
    apply PiLp.ext
    intro σ
    simpa only [mpvState_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul] using hdecomp σ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Fin.sum_univ_zero] at hsum
    exact (hA hsum).elim
  · have hSep : 3 * (r - 1) * (q + 1) ≤ 3 * (D - 1) * (q + 1) :=
      Nat.mul_le_mul_right (q + 1) (Nat.mul_le_mul_left 3 (Nat.sub_le_sub_right hrD 1))
    have hSpan : WordTupleSpanTop B (N - L) :=
      wordTupleSpanTop_of_ge_of_isNBlkInjective B hdim hunital hDual hIrr hq
        hC1 hDistinct (by omega)
    have hker := groundSpaceES_le_ker_of_periodicInteractionHamiltonianES_eq_zero
      B c hc h hh hPrime.pos (by omega) hSpan (by rwa [← hsum])
    let j : Fin r := ⟨0, hr⟩
    let : NeZero (dim j) := ⟨(hdim j).ne'⟩
    refine ⟨dim j, hdim j, hdimD j, B j, ⟨q, hq, hC1 j⟩, hker j,
      max L (q + 1), ?_⟩
    intro M hM
    have hLM : L ≤ M := (le_max_left _ _).trans hM
    have hqM : q + 1 ≤ M := (le_max_right _ _).trans hM
    have hnonzero : mpvState (B j) M ≠ 0 := by
      intro hMzero
      apply mpv_ne_zero_of_isNBlkInjective (hC1 j) hq hqM
      funext σ
      simpa only [mpvState_apply, PiLp.zero_apply] using
        congrArg (fun v : MPVSpace d M => v σ) hMzero
    have hGround := periodicInteractionHamiltonianES_mpvState_eq_zero_of_groundSpaceES_le_ker
      (B j) h (hker j) hLM
    exact ⟨hnonzero, eq_span_singleton_of_mem_of_finrank_eq_one
      (hUnique M hLM) hGround hnonzero⟩

/-- A small prime-length ground-state representation yields a single fixed
MPS tensor generating the ground space at all sufficiently large volumes.
The explicit threshold uses the general Wielandt length \((D^2+1)^2\).
Source: SPWC10, Theorem 5 proof, lines 858–880. -/
theorem exists_eventually_fixed_mps_of_prime_length_bound
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hUnique : ∀ M, L ≤ M →
      Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1)
    {D N : ℕ} (A : MPSTensor d D) (hPrime : N.Prime)
    (hBound : L + max ((D ^ 2 + 1) ^ 2)
      (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) ≤ N)
    (hA : mpvState A N ≠ 0)
    (hzero : periodicInteractionHamiltonianES h N (mpvState A N) = 0) :
    ∃ D₀ : ℕ, 0 < D₀ ∧ D₀ ≤ D ∧ ∃ B : MPSTensor d D₀, ∃ M₀ : ℕ,
      ∀ M, M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M := by
  obtain ⟨D₀, hD₀, hD, B, _, _, M₀, hB⟩ :=
    exists_normal_eventual_ground_data_of_prime_length_bound h hh hUnique A hPrime hBound hA hzero
  exact ⟨D₀, hD₀, hD, B, M₀, hB⟩

/-- Either one fixed tensor generates the eventual ground spaces, or every
prime-length nonzero MPS ground-state representation obeys the explicit
fifth-degree bound \(N<L+\max\{(D^2+1)^2,3(D-1)((D^2+1)^2+1)\}\).
The local interaction and all constants are fixed independently of the prime
and of the representing tensor. Source: SPWC10, Theorem 5, lines 850–880. -/
theorem eventually_fixed_mps_or_prime_length_bound
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hUnique : ∀ M, L ≤ M →
      Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1) :
    (∃ (D₀ : ℕ) (B : MPSTensor d D₀) (M₀ : ℕ),
      ∀ M, M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M) ∨
    (∀ (N : ℕ), N.Prime → ∀ (D : ℕ) (A : MPSTensor d D),
      mpvState A N ≠ 0 → periodicInteractionHamiltonianES h N (mpvState A N) = 0 →
        N < L + max ((D ^ 2 + 1) ^ 2)
          (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))) := by
  classical
  by_cases hFixed : ∃ (D₀ : ℕ) (B : MPSTensor d D₀) (M₀ : ℕ),
      ∀ M, M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M
  · exact Or.inl hFixed
  · right
    intro N hPrime D A hA hzero
    by_contra hBound
    obtain ⟨D₀, _, _, B, M₀, hB⟩ :=
      exists_eventually_fixed_mps_of_prime_length_bound h hh hUnique A hPrime
        (Nat.le_of_not_gt hBound) hA hzero
    exact hFixed ⟨D₀, B, M₀, hB⟩

end MPSTensor
