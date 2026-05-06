/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumGroundSpace
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Direct-sum uniqueness input

This file records the equal-size branch of the two-block direct-sum argument
from David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`.

The preceding direct-sum files prove the trace-dual and finite-dimensional
steps: a homogeneous three-block relation forces equality of bond dimensions
and equality of the length-`L` local image spaces.  The remaining equal-size
contradiction in the source uses the uniqueness of injective parent ground
spaces: if the local image spaces are equal, then the periodic ground-state
line is the same.  Therefore distinct injective block states rule out the
equal-size collapse.

## References

* [David--Perez-Garcia--Schuch--Wolf 2006, Lemma `lem:direct-sum`]

## Tags

matrix product states, canonical form, direct sum, parent Hamiltonian
-/

open scoped Matrix

namespace MPSTensor

variable {d D₁ D₂ L N : ℕ}

/-- Equal local image spaces impose the same periodic-chain constraints. -/
theorem chainGroundSpace_eq_of_groundSpace_eq
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hG : groundSpace A L = groundSpace B L) :
    chainGroundSpace A L N = chainGroundSpace B L N := by
  rw [chainGroundSpace, chainGroundSpace]
  by_cases h : 0 < N ∧ L ≤ N
  · simp [h, hG]
  · simp [h]

/-- Non-proportional MPV states have distinct MPV lines. -/
theorem mpvSubmodule_ne_of_not_exists_mpv_eq_smul
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hDistinct :
      ¬ ∃ c : ℂ, (mpv A : NSiteSpace d N) = c • (mpv B : NSiteSpace d N)) :
    mpvSubmodule A N ≠ mpvSubmodule B N := by
  intro hEq
  apply hDistinct
  have hmem : (mpv A : NSiteSpace d N) ∈ mpvSubmodule B N := by
    rw [← hEq, mpvSubmodule, Submodule.mem_span_singleton]
    exact ⟨1, by simp⟩
  rw [mpvSubmodule, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

/-- Pointwise non-proportionality implies non-proportionality of the bundled
MPV states. -/
theorem not_exists_mpv_eq_smul_of_not_exists_forall_mpv_eq_mul
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hDistinct :
      ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ) :
    ¬ ∃ c : ℂ, (mpv A : NSiteSpace d N) = c • (mpv B : NSiteSpace d N) := by
  rintro ⟨c, hc⟩
  apply hDistinct
  refine ⟨c, ?_⟩
  intro σ
  simpa [Pi.smul_apply, smul_eq_mul] using congrFun hc σ

/-- A pointwise non-proportional MPV state has a distinct MPV line. -/
theorem mpvSubmodule_ne_of_not_exists_forall_mpv_eq_mul
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hDistinct :
      ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ) :
    mpvSubmodule A N ≠ mpvSubmodule B N :=
  mpvSubmodule_ne_of_not_exists_mpv_eq_smul
    (not_exists_mpv_eq_smul_of_not_exists_forall_mpv_eq_mul hDistinct)

/-- Distinct periodic MPV lines rule out the equal-size local-image collapse.

This is the parent-Hamiltonian uniqueness input used in the equal-size branch
of the two-block direct-sum proof.  It is intentionally stated with the
external distinctness hypothesis on the MPV lines: later BNT-level arguments
must supply that hypothesis from the paper's pairwise-different block states. -/
theorem not_bondDim_eq_and_groundSpace_eq_of_mpvSubmodule_ne
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hA : IsInjective A) (hB : IsInjective B)
    (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N)
    (hDistinct : mpvSubmodule A N ≠ mpvSubmodule B N) :
    ¬ (D₁ = D₂ ∧ groundSpace A L = groundSpace B L) := by
  rintro ⟨hD, hG⟩
  subst hD
  have hChain : chainGroundSpace A L N = chainGroundSpace B L N :=
    chainGroundSpace_eq_of_groundSpace_eq hG
  have hAeq : chainGroundSpace A L N = mpvSubmodule A N :=
    chainGroundSpace_eq_mpvSubmodule hA hN hL hLN
  have hBeq : chainGroundSpace B L N = mpvSubmodule B N :=
    chainGroundSpace_eq_mpvSubmodule hB hN hL hLN
  apply hDistinct
  calc
    mpvSubmodule A N = chainGroundSpace A L N := hAeq.symm
    _ = chainGroundSpace B L N := hChain
    _ = mpvSubmodule B N := hBeq

/-- Non-proportional periodic MPV states rule out the equal-size local-image
collapse. -/
theorem not_bondDim_eq_and_groundSpace_eq_of_not_exists_mpv_eq_smul
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hA : IsInjective A) (hB : IsInjective B)
    (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N)
    (hDistinct :
      ¬ ∃ c : ℂ, (mpv A : NSiteSpace d N) = c • (mpv B : NSiteSpace d N)) :
    ¬ (D₁ = D₂ ∧ groundSpace A L = groundSpace B L) := by
  exact not_bondDim_eq_and_groundSpace_eq_of_mpvSubmodule_ne hA hB hN hL hLN
    (mpvSubmodule_ne_of_not_exists_mpv_eq_smul hDistinct)

/-- A sufficiently long non-proportional MPV state rules out the equal-size
local-image collapse. -/
theorem not_bondDim_eq_and_groundSpace_eq_of_exists_not_mpv_eq_smul
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hA : IsInjective A) (hB : IsInjective B) (hL : 1 < L)
    (hDistinct :
      ∃ N : ℕ, 2 ≤ N ∧ L ≤ N ∧
        ¬ ∃ c : ℂ, (mpv A : NSiteSpace d N) = c • (mpv B : NSiteSpace d N)) :
    ¬ (D₁ = D₂ ∧ groundSpace A L = groundSpace B L) := by
  rcases hDistinct with ⟨N, hN, hLN, hSep⟩
  exact not_bondDim_eq_and_groundSpace_eq_of_not_exists_mpv_eq_smul
    hA hB hN hL hLN hSep

/-- A sufficiently long pointwise non-proportional MPV state rules out the
equal-size local-image collapse. -/
theorem not_bondDim_eq_and_groundSpace_eq_of_exists_not_forall_mpv_eq_mul
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hA : IsInjective A) (hB : IsInjective B) (hL : 1 < L)
    (hDistinct :
      ∃ N : ℕ, 2 ≤ N ∧ L ≤ N ∧
        ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ) :
    ¬ (D₁ = D₂ ∧ groundSpace A L = groundSpace B L) := by
  rcases hDistinct with ⟨N, hN, hLN, hSep⟩
  exact not_bondDim_eq_and_groundSpace_eq_of_not_exists_mpv_eq_smul
    hA hB hN hL hLN
    (not_exists_mpv_eq_smul_of_not_exists_forall_mpv_eq_mul hSep)

/-- Two-block directness with the equal-size branch discharged by distinct MPV
lines.

The hypotheses mirror the already-formalized finite-dimensional step together
with the source-paper uniqueness input: block injectivity controls the
three-block trace relation, while injective parent-Hamiltonian uniqueness and a
distinct MPV-line hypothesis exclude the equal-size collapse. -/
theorem groundSpace_inf_eq_bot_of_mpvSubmodule_ne_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hAblk : IsNBlkInjective A L) (hBblk : IsNBlkInjective B L)
    (hA : IsInjective A) (hB : IsInjective B)
    (hD : D₂ ≤ D₁) (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N)
    (hDistinct : mpvSubmodule A N ≠ mpvSubmodule B N) :
    groundSpace A (L + (L + L)) ⊓ groundSpace B (L + (L + L)) = ⊥ := by
  exact groundSpace_inf_eq_bot_of_not_bondDim_eq_and_groundSpace_eq_of_dim_ge
    hAblk hBblk hD
    (not_bondDim_eq_and_groundSpace_eq_of_mpvSubmodule_ne hA hB hN hL hLN hDistinct)

/-- Two-block directness with the equal-size branch discharged by
non-proportional MPV states. -/
theorem groundSpace_inf_eq_bot_of_not_exists_mpv_eq_smul_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hAblk : IsNBlkInjective A L) (hBblk : IsNBlkInjective B L)
    (hA : IsInjective A) (hB : IsInjective B)
    (hD : D₂ ≤ D₁) (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N)
    (hDistinct :
      ¬ ∃ c : ℂ, (mpv A : NSiteSpace d N) = c • (mpv B : NSiteSpace d N)) :
    groundSpace A (L + (L + L)) ⊓ groundSpace B (L + (L + L)) = ⊥ := by
  exact groundSpace_inf_eq_bot_of_mpvSubmodule_ne_of_dim_ge
    hAblk hBblk hA hB hD hN hL hLN
    (mpvSubmodule_ne_of_not_exists_mpv_eq_smul hDistinct)

/-- Two-block directness from a sufficiently long non-proportional MPV state. -/
theorem groundSpace_inf_eq_bot_of_exists_not_mpv_eq_smul_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hAblk : IsNBlkInjective A L) (hBblk : IsNBlkInjective B L)
    (hA : IsInjective A) (hB : IsInjective B) (hD : D₂ ≤ D₁) (hL : 1 < L)
    (hDistinct :
      ∃ N : ℕ, 2 ≤ N ∧ L ≤ N ∧
        ¬ ∃ c : ℂ, (mpv A : NSiteSpace d N) = c • (mpv B : NSiteSpace d N)) :
    groundSpace A (L + (L + L)) ⊓ groundSpace B (L + (L + L)) = ⊥ := by
  exact groundSpace_inf_eq_bot_of_not_bondDim_eq_and_groundSpace_eq_of_dim_ge
    hAblk hBblk hD
    (not_bondDim_eq_and_groundSpace_eq_of_exists_not_mpv_eq_smul hA hB hL hDistinct)

/-- Two-block directness from a sufficiently long pointwise non-proportional
MPV state. -/
theorem groundSpace_inf_eq_bot_of_exists_not_forall_mpv_eq_mul_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} [NeZero D₁] [NeZero D₂]
    (hAblk : IsNBlkInjective A L) (hBblk : IsNBlkInjective B L)
    (hA : IsInjective A) (hB : IsInjective B) (hD : D₂ ≤ D₁) (hL : 1 < L)
    (hDistinct :
      ∃ N : ℕ, 2 ≤ N ∧ L ≤ N ∧
        ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ) :
    groundSpace A (L + (L + L)) ⊓ groundSpace B (L + (L + L)) = ⊥ := by
  exact groundSpace_inf_eq_bot_of_not_bondDim_eq_and_groundSpace_eq_of_dim_ge
    hAblk hBblk hD
    (not_bondDim_eq_and_groundSpace_eq_of_exists_not_forall_mpv_eq_mul
      hA hB hL hDistinct)

end MPSTensor
