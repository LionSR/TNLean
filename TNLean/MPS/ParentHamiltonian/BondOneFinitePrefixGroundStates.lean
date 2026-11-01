/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BondOneVector
import TNLean.MPS.ParentHamiltonian.FinitePrefixUniformBond
import TNLean.MPS.Symmetry.GaugeUniqueness

/-!
# The finite-prefix ground-state construction for the product branch

For a normal bond-one tensor, actual periodic product amplitudes are
nonzero at every positive volume. A local MPS-space inclusion in the
kernel of the fixed interaction therefore supplies an actual
zero-momentum ground vector at every permitted short volume as well.
Global uniqueness then gives the same single bond-one ground family at
all positive lengths, with no short-vector representation premise.

**Scope restriction (bond-one branch):** this discharges the finite-prefix
step when the normal tensor derived in the eventual branch has bond one.
For larger bond dimension, full all-volume frustration-free uniqueness
has not yet been shown to supply every short zero-momentum vector. See
`docs/paper-gaps/spwc10_ground_state_dichotomy_quantifiers.tex`.
The local-kernel inclusion here is the actual one derived by the
prime-length construction; it is not inferred from an arbitrary invariant
line or supplied as an all-volume nonvanishing condition.

Source: SPWC10, arXiv:0909.5347, Theorem 5 and proof, main.tex lines 850--880.
-/

open scoped Matrix

namespace MPSTensor

variable {d L : ℕ}

/-- Normality supplies a nonzero letter; the bond-one product formula
then proves actual state nonvanishing at every positive length.
Source: SPWC10, Theorem 5, lines 850--880, product-branch specialization. -/
theorem mpvState_ne_zero_of_normal_bondOne (B : MPSTensor d 1)
    (hB : Kraus.IsNormal B) (M : ℕ) (hM : 0 < M) : mpvState B M ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_mpv_ne_zero_of_bondOne B (exists_apply_ne_zero_of_isNormal hB) hM
  intro hzero
  apply hσ
  simpa only [mpvState_apply, PiLp.zero_apply] using congrArg (fun v : MPVSpace d M ↦ v σ) hzero

/-- The actual derived local-kernel inclusion gives nonzero
zero-momentum ground vectors at every permitted positive length in the
normal bond-one branch. In particular it covers the entire finite prefix.
Source: SPWC10, Theorem 5 proof, lines 873--880, product-branch specialization. -/
theorem exists_cyclic_ground_of_normal_bondOne_local_kernel
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (B : MPSTensor d 1)
    (hB : Kraus.IsNormal B) (hker : groundSpaceES B L ≤ LinearMap.ker h)
    (M : ℕ) (hM : 0 < M) (hLM : L ≤ M) :
    ∃ ψ : MPVSpace d M, ψ ≠ 0 ∧ periodicInteractionHamiltonianES h M ψ = 0 ∧
      ∀ (s : Fin M) (σ : Fin M → Fin d), ψ (fun k ↦ σ (k + s)) = ψ σ := by
  exact ⟨mpvState B M, mpvState_ne_zero_of_normal_bondOne B hB M hM,
    periodicInteractionHamiltonianES_mpvState_eq_zero_of_groundSpaceES_le_ker B h hker hLM,
    mpvState_cyclic_invariant B⟩

/-- All-volume uniqueness identifies the actual product vectors as
one uniform bond-one family, including every positive short volume.
No short MPS representation or zero-momentum premise is assumed.
Source: SPWC10, Theorem 5, lines 850--880, normal bond-one branch. -/
theorem uniform_bondOne_ground_family_of_normal_local_kernel
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L)
    (hUnique : ∀ M, L ≤ M →
      Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1)
    (B : MPSTensor d 1) (hB : Kraus.IsNormal B)
    (hker : groundSpaceES B L ≤ LinearMap.ker h) :
    ∀ M, 0 < M → L ≤ M → mpvState B M ≠ 0 ∧
      LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M := by
  intro M hM hLM
  have hnonzero := mpvState_ne_zero_of_normal_bondOne B hB M hM
  have hzero := periodicInteractionHamiltonianES_mpvState_eq_zero_of_groundSpaceES_le_ker
    B h hker hLM
  exact ⟨hnonzero, eq_span_singleton_of_mem_of_finrank_eq_one (hUnique M hLM) hzero hnonzero⟩

/-- A bond-one ground representation at one sufficiently long prime
volume supplies the same bond-one ground family at every permitted
positive volume. The normal tensor and local-kernel inclusion are derived
by the actual prime-length reduction, not assumed as hypotheses.
Source: SPWC10, Theorem 5 proof, lines 861--880, bond-one input branch. -/
theorem exists_uniform_bondOne_ground_family_of_prime_length_bound
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hUnique : ∀ M, L ≤ M →
      Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h M)) = 1)
    {N : ℕ} (A : MPSTensor d 1) (hPrime : N.Prime) (hBound : L + 4 ≤ N)
    (hA : mpvState A N ≠ 0)
    (hzero : periodicInteractionHamiltonianES h N (mpvState A N) = 0) :
    ∃ B : MPSTensor d 1, ∀ M, 0 < M → L ≤ M → mpvState B M ≠ 0 ∧
      LinearMap.ker (periodicInteractionHamiltonianES h M) = ℂ ∙ mpvState B M := by
  have hthreshold : max (((1 : ℕ) ^ 2 + 1) ^ 2)
      (3 * (1 - 1) * (((1 : ℕ) ^ 2 + 1) ^ 2 + 1)) = 4 := by norm_num
  obtain ⟨D₀, hD₀, hD, B, hnormal, hker, _, _⟩ :=
    exists_normal_eventual_ground_data_of_prime_length_bound h hh hUnique A hPrime
      (by simpa only [hthreshold] using hBound) hA hzero
  have hdim : D₀ = 1 := by omega
  subst D₀
  exact ⟨B, uniform_bondOne_ground_family_of_normal_local_kernel h hUnique B hnormal hker⟩

end MPSTensor
