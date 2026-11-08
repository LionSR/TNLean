/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ChainPaddingGroundState
import TNLean.MPS.AreaLaw.ViableSet.PrefixExtraction
import TNLean.MPS.AreaLaw.ViableSet.FinalMPS
import QICLean.Analysis.PhaseError

/-!
# An MPS in the actual retained prefix span

A viable family for a target with fixed right configuration contains a
normalized prefix vector with the same overlap. Choosing its phase gives
the corresponding squared vector error. Its MPS bound follows from the
actual finite retained family, without a separate approximation theorem.

Source: product-ancilla use of LVV13, arXiv:1307.5143v1, final successive
induction, lines 652--678.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A phase-aligned MPS is obtained in the actual retained prefix span.
The coefficient two converts overlap loss to squared vector distance. -/
theorem IsViable.exists_prefix_mps_of_paddedGroundVector {L N q b : ℕ}
    (hi : L ≤ N) (z : Fin q) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΓ : ‖Γ‖ = 1) {delta : ℝ} (hdelta : delta < 1)
    {S : Finset (LeftBlockVector N q L)}
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v)
    (hv : IsViable (paddedGroundVector hi z Γ) delta (S : Set (LeftBlockVector N q L))) :
    ∃ w ∈ Submodule.span ℂ (S : Set (LeftBlockVector N q L)), ‖w‖ = 1 ∧
      ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi)).symm w - Γ‖ ^ 2 ≤
        2 * delta ∧
      IsOpenMPS L q (S.card * max 1 b) (fun x ↦ w (leftConfigOfFin x)) := by
  classical
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hi)
  obtain ⟨w, hw, hwnorm, hoverlap⟩ := hv.exists_prefix_of_rightBasisExtension hdelta
  obtain ⟨θ, _, hθ⟩ := exists_isMinOn_norm_sub_exp_smul (e Γ) w
  let w' := Complex.exp ((θ : ℂ) * Complex.I) • w
  have hw' : w' ∈ Submodule.span ℂ (S : Set (LeftBlockVector N q L)) :=
    Submodule.smul_mem _ _ hw
  refine ⟨w', hw', ?_, ?_, isOpenMPS_leftChain_of_mem_span S hS hw'⟩
  · simp only [w', norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, hwnorm]
  · have hinner : ‖⟪e Γ, w⟫_ℂ‖ = ‖⟪w, e Γ⟫_ℂ‖ := norm_inner_symm _ _
    have hdist : ‖e.symm w' - Γ‖ = ‖w' - e Γ‖ := by
      rw [← e.norm_map (e.symm w' - Γ), map_sub, e.apply_symm_apply]
    change ‖e.symm w' - Γ‖ ^ 2 ≤ _
    rw [hdist, norm_sub_rev]
    change ‖e Γ - Complex.exp ((θ : ℂ) * Complex.I) • w‖ ^ 2 ≤ _
    rw [hθ, e.norm_map, hΓ, hwnorm, hinner]
    linarith

end TNLean.MPS.AreaLaw
