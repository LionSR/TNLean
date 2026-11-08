/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.CyclicPhases
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace

/-!
# No cyclic main-sector boundary state at degree seven

Two seven-site charged boundary vectors agreeing across the
cyclic cut are zero. Each nonzero virtual charge has two explicit
physical first letters with distinct cyclic phases. This is an
short local-space obstruction, not an all-volume kernel classification.

Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880;
see `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

/-- Every nonzero charge has two degree-seven words whose first
letters detect distinct cyclic phases. All witnesses are explicit finite
physical configurations; each displayed equality is checked by reduction. -/
theorem exists_distinct_seven_cyclic_phases (u v : ZMod 5) (hne : (u, v) ≠ 0) :
    ∃ (i j : Fin 3) (σ τ : Cfg 3 6),
      wordCharge (i :: List.ofFn σ) = (u, v) ∧
      wordCharge (j :: List.ofFn τ) = (u, v) ∧
      letterPairing i (u, v) ≠ letterPairing j (u, v) := by
  fin_cases u <;> fin_cases v
  · exact (hne rfl).elim
  · exact ⟨0, 1, ![0, 1, 1, 1, 2, 2], ![0, 0, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 1, 1], ![1, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 2, 2, 2], ![0, 0, 0, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![2, 2, 2, 2, 2, 2], ![0, 1, 1, 1, 1, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 1, 2, 2], ![0, 0, 0, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![1, 2, 2, 2, 2, 2], ![0, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 0, 0, 2, 2, 2], ![0, 0, 0, 0, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 1, 1, 1, 1, 2], ![0, 0, 1, 1, 1, 2], by decide⟩
  · exact ⟨1, 2, ![1, 1, 2, 2, 2, 2], ![1, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 2, 2, 2, 2, 2], ![0, 0, 1, 1, 1, 1], by decide⟩
  · exact ⟨1, 2, ![1, 1, 1, 2, 2, 2], ![1, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 1, 1, 2], ![0, 0, 0, 1, 1, 2], by decide⟩
  · exact ⟨0, 2, ![1, 1, 2, 2, 2, 2], ![0, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 2, 2], ![0, 0, 0, 0, 2, 2], by decide⟩
  · exact ⟨0, 1, ![1, 1, 1, 2, 2, 2], ![0, 1, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 1, 2], by decide⟩
  · exact ⟨0, 2, ![0, 1, 2, 2, 2, 2], ![0, 0, 1, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 2, 2], ![1, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 0, 1, 2], ![2, 2, 2, 2, 2, 2], by decide⟩
  · exact ⟨0, 2, ![0, 0, 2, 2, 2, 2], ![0, 0, 0, 2, 2, 2], by decide⟩
  · exact ⟨0, 1, ![1, 1, 1, 1, 2, 2], ![0, 1, 1, 1, 2, 2], by decide⟩
  · exact ⟨0, 1, ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], by decide⟩
  · exact ⟨0, 1, ![0, 1, 1, 2, 2, 2], ![0, 0, 1, 2, 2, 2], by decide⟩

/-- The character separates any two distinct virtual residues. -/
theorem rootCharacter_injective {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    Function.Injective (rootCharacter ζ) := by
  intro a b h
  apply ZMod.val_injective 5
  exact hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h

/-- Local boundary vectors agreeing across the seven-site cyclic
cut vanish. There is no assumed boundary or local-kernel classification. -/
theorem eq_zero_of_seven_cyclic_agreement {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (f g : NSiteSpace 3 7)
    (hf : f ∈ groundSpace (threeLetterTensor ζ) 7)
    (hg : g ∈ groundSpace (threeLetterTensor ζ) 7)
    (hfg : ∀ (i : Fin 3) (σ : Cfg 3 6), f (Fin.cons i σ) = g (Fin.snoc σ i)) :
    f = 0 ∧ g = 0 := by
  obtain ⟨F, G, hF, _, hcmp⟩ :=
    exists_charge_comparison_of_cyclic_agreement hζ f g hf hg hfg
  have hFzero (p : ZMod 5 × ZMod 5) (hp : p ≠ 0) : F p = 0 := by
    obtain ⟨i, j, σ, τ, hi, hj, hij⟩ := exists_distinct_seven_cyclic_phases p.1 p.2 hp
    have h₁ := hcmp i σ
    have h₂ := hcmp j τ
    rw [hi] at h₁
    rw [hj] at h₂
    by_contra hne
    apply hij
    apply rootCharacter_injective hζ
    exact mul_right_cancel₀ hne (h₁.symm.trans h₂)
  have hfzero : f = 0 := by
    funext σ
    change f σ = 0
    rw [hF, hFzero _ (wordCharge_ne_zero_of_length_seven (List.length_ofFn)), mul_zero]
  refine ⟨hfzero, ?_⟩
  funext σ
  have h := hfg (σ (Fin.last 6)) (Fin.init σ)
  rw [hfzero] at h
  simpa only [Fin.snoc_init_self, Pi.zero_apply] using h.symm

/-- The seven-site main boundary space has zero intersection with the
space obtained by moving the last physical site to the front. -/
theorem eq_zero_of_seven_cyclic_local_membership {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (f : NSiteSpace 3 7) (hf : f ∈ groundSpace (threeLetterTensor ζ) 7)
    (hrotate : (fun σ : Cfg 3 7 ↦ f (Fin.cons (σ (Fin.last 6)) (Fin.init σ))) ∈
      groundSpace (threeLetterTensor ζ) 7) : f = 0 := by
  exact (eq_zero_of_seven_cyclic_agreement hζ f _ hf hrotate
    (fun i σ ↦ by simp only [Fin.snoc_last, Fin.init_snoc])).1

/-- The seven-site periodic main-sector parent space is zero.
Every cyclic local condition is used through the existing chain ground space. -/
theorem chainGroundSpace_threeLetterTensor_seven_eq_bot {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) : chainGroundSpace (threeLetterTensor ζ) 7 7 = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  rw [chainGroundSpace, dite_eq_left (by decide : 0 < 7 ∧ 7 ≤ 7)] at hf
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf
  have hcfg₀ (σ : Cfg 3 7) : cyclicCfg (by decide : 0 < 7) 7 0 σ 0 = σ := by
    funext k
    fin_cases k <;> rfl
  have hcfg₁ (σ : Cfg 3 7) : cyclicCfg (by decide : 0 < 7) 7 1 σ 0 =
      Fin.cons (σ (Fin.last 6)) (Fin.init σ) := by
    funext k
    fin_cases k <;> rfl
  have hlocal : f ∈ groundSpace (threeLetterTensor ζ) 7 := by
    convert hf 0 0 using 1
    funext σ
    simp only [cyclicRestrictₗ_apply, hcfg₀]
  have hrotate : (fun σ : Cfg 3 7 ↦ f (Fin.cons (σ (Fin.last 6)) (Fin.init σ))) ∈
      groundSpace (threeLetterTensor ζ) 7 := by
    convert hf 1 0 using 1
    funext σ
    simp only [cyclicRestrictₗ_apply, hcfg₁]
  exact eq_zero_of_seven_cyclic_local_membership hζ f hlocal hrotate

end MPSTensor.ShortMomentum
