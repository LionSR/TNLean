/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.CyclicChargeDetection

/-!
# Cyclic closure of actual global Weyl boundary spaces

At every degree at least seven, two actual global boundary vectors
agreeing across the cyclic cut must be scalar multiples of the periodic
trace vector. The coefficient is derived by eliminating every noncentral
charge with two actual phase-detecting words.

This module does not assume or prove that overlapping seven-site constraints
already yield the global boundary space. The separate open-chain reconstruction
and its actual periodic-kernel application are assembled in
`PeriodicKernel.lean`.
Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880;
see `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

/-- Actual global boundary vectors with cyclic agreement close to the
periodic trace line at every degree at least seven. -/
theorem exists_smul_mpv_of_cyclic_agreement {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    {n : ℕ} (hn : 6 ≤ n) (f g : NSiteSpace 3 (n + 1))
    (hf : f ∈ groundSpace (threeLetterTensor ζ) (n + 1))
    (hg : g ∈ groundSpace (threeLetterTensor ζ) (n + 1))
    (hfg : ∀ (i : Fin 3) (σ : Cfg 3 n), f (Fin.cons i σ) = g (Fin.snoc σ i)) :
    ∃ c : ℂ, f = c • (mpv (threeLetterTensor ζ) : NSiteSpace 3 (n + 1)) := by
  obtain ⟨F, G, hF, _, hcmp⟩ :=
    exists_charge_comparison_of_cyclic_agreement hζ f g hf hg hfg
  have hFzero (p : ZMod 5 × ZMod 5) (hp : p ≠ 0) : F p = 0 := by
    obtain ⟨i, j, σ, τ, hi, hj, hij⟩ := exists_distinct_cyclic_phases n hn p.1 p.2 hp
    have h₁ := hcmp i σ
    have h₂ := hcmp j τ
    rw [hi] at h₁
    rw [hj] at h₂
    by_contra hne
    apply hij
    apply rootCharacter_injective hζ
    exact mul_right_cancel₀ hne (h₁.symm.trans h₂)
  refine ⟨F 0 / 5, ?_⟩
  funext σ
  change f σ = (F 0 / 5) * (mpv (threeLetterTensor ζ) σ)
  rw [hF, mpv, coeff, evalWord_threeLetterTensor hζ.pow_eq_one]
  change _ = _ * Matrix.trace (_ : Matrix (ZMod 5) (ZMod 5) ℂ)
  rw [Matrix.trace_smul, smul_eq_mul, trace_chargedWeyl hζ]
  by_cases hcharge : wordCharge (List.ofFn σ) = 0
  · rw [hcharge, ite_eq_left rfl]
    ring
  · simp only [hFzero _ hcharge, ite_eq_right hcharge, mul_zero]

/-- One actual global boundary vector whose cyclic reordering is also a
global boundary vector lies in the periodic trace line. -/
theorem mem_mpvSubmodule_of_cyclic_local_membership {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {n : ℕ} (hn : 6 ≤ n)
    (f : NSiteSpace 3 (n + 1)) (hf : f ∈ groundSpace (threeLetterTensor ζ) (n + 1))
    (hrotate : (fun σ : Cfg 3 (n + 1) ↦ f (Fin.cons (σ (Fin.last n)) (Fin.init σ))) ∈
      groundSpace (threeLetterTensor ζ) (n + 1)) :
    f ∈ mpvSubmodule (threeLetterTensor ζ) (n + 1) := by
  obtain ⟨c, rfl⟩ := exists_smul_mpv_of_cyclic_agreement hζ hn f _ hf hrotate
    (fun i σ ↦ by simp only [Fin.snoc_last, Fin.init_snoc])
  exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))

end MPSTensor.ShortMomentum
