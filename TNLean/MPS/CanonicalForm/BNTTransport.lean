/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions

/-!
# Transport of bases of normal tensors

This module records two invariances of the CPSV16 basis-of-normal-tensors predicate:
the represented tensor may be replaced by one with the same positive-length matrix product
vectors, and the finite family of normal tensors may be relabelled.

## Main results

* `MPSTensor.IsCPSVBasisOfNormalTensors.of_sameMPV₂Pos`: transport along equality of all
  positive-length matrix product vectors.
* `MPSTensor.IsCPSVBasisOfNormalTensors.reindex`: relabel a basis along an equivalence of finite
  label types.

These invariances concern the definition in arXiv:1606.00608, lines 271--274.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D₁ D₂ g g₁ g₂ : ℕ}

/-- A basis of normal tensors remains such after replacing the represented tensor by one with
the same matrix product vectors at every positive length.

This transports the spanning clause in arXiv:1606.00608, lines 271--274; normality and eventual
linear independence concern only the basis family and are unchanged. -/
theorem IsCPSVBasisOfNormalTensors.of_sameMPV₂Pos
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {basis : (j : Fin g) → Σ Dj : ℕ, MPSTensor d Dj}
    (hBNT : IsCPSVBasisOfNormalTensors A basis) (hAB : SameMPV₂Pos A B) :
    IsCPSVBasisOfNormalTensors B basis := by
  refine ⟨hBNT.blocks_normal, ?_, hBNT.eventually_li⟩
  intro N hN
  obtain ⟨c, hc⟩ := hBNT.spans_mpv N hN
  exact ⟨c, fun σ ↦ (hAB N hN σ).symm.trans (hc σ)⟩

/-- Relabelling a finite basis of normal tensors preserves its defining spanning and eventual
linear-independence properties.

This is the label-invariance of the definition in arXiv:1606.00608, lines 271--274. -/
theorem IsCPSVBasisOfNormalTensors.reindex
    {A : MPSTensor d D₁} {basis : (j : Fin g₂) → Σ Dj : ℕ, MPSTensor d Dj}
    (hBNT : IsCPSVBasisOfNormalTensors A basis) (e : Fin g₁ ≃ Fin g₂) :
    IsCPSVBasisOfNormalTensors A (fun j ↦ basis (e j)) := by
  refine ⟨fun j ↦ hBNT.blocks_normal (e j), ?_, ?_⟩
  · intro N hN
    obtain ⟨c, hc⟩ := hBNT.spans_mpv N hN
    refine ⟨c ∘ e, fun σ ↦ ?_⟩
    rw [hc σ]
    exact (Equiv.sum_comp e (fun j ↦ c j * mpv (basis j).2 σ)).symm
  · obtain ⟨N₀, hLI⟩ := hBNT.eventually_li
    refine ⟨N₀, fun N hN ↦ ?_⟩
    change LinearIndependent ℂ
      ((fun j : Fin g₂ ↦ mpvState (d := d) (basis j).2 N) ∘ e)
    exact (linearIndependent_equiv e).mpr (hLI N hN)

end MPSTensor
