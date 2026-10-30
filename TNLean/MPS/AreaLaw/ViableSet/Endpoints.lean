/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates

/-!
# Initial and final cuts of a viable-set construction

The empty left block has a single scalar basis vector. Its singleton family is exactly
viable for every unit chain vector. At the opposite end, the right block is empty, so a
viable witness itself belongs to the span of the final family after identifying the full
left block with the chain.

These are the endpoint statements used in the induction of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 652–678. They do not supply the intermediate
size trimming, bond trimming or sampled error reduction.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The scalar basis vector on the empty left block (LVV13, `algo53.tex`, the initial
condition of the induction, lines 652–678). -/
noncomputable def emptyLeftVector (L q : ℕ) : LeftBlockVector L q 0 :=
  WithLp.toLp 2 fun _ ↦ 1

/-- Every chain vector is supported on the scalar basis of the empty left block.
Source: LVV13, `algo53.tex`, the initial condition, lines 652–678. -/
theorem mem_leftSupportSubmodule_emptyLeftVector
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    ψ ∈ leftSupportSubmodule {emptyLeftVector L q} := by
  classical
  intro b
  apply Submodule.mem_span_singleton.mpr
  refine ⟨cutColumn ψ 0 b default, ?_⟩
  ext a
  change cutColumn ψ 0 b default * 1 = cutColumn ψ 0 b a
  simpa only [mul_one] using congrArg (cutColumn ψ 0 b) (Subsingleton.elim default a)

/-- The scalar singleton is `(0,1,1,0)`-viable for every unit chain vector.
Source: LVV13, `algo53.tex`, the initial condition, lines 652–678. -/
theorem isViableMPS_emptyLeftVector {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΓ : ‖Γ‖ = 1) :
    IsViableMPS Γ 1 1 0 ({emptyLeftVector L q} : Finset (LeftBlockVector L q 0)) := by
  classical
  refine ⟨by simp, ?_, Γ, hΓ, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_singleton] at hv
    subst v
    exact isOpenMPS_of_internal_cutMatrix_rank_le
      (WithLp.toLp 2 fun x ↦ emptyLeftVector L q (leftConfigOfFin x))
      (fun k hk0 hkL ↦ by omega)
  · simp [inner_self_eq_norm_sq_to_K, hΓ]
  · simpa only [Finset.coe_singleton] using mem_leftSupportSubmodule_emptyLeftVector Γ

/-- The full left block is the whole chain, with the same Hilbert norm.
Source: LVV13, `algo53.tex`, the final cut of the induction, lines 652–678. -/
noncomputable def fullLeftEquiv (L q : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ] LeftBlockVector L q L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (le_refl L))

/-- At the final cut every cut column is the chain vector in full-left coordinates.
Source: LVV13, `algo53.tex`, the final cut of the induction, lines 652–678. -/
theorem cutColumn_full (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (b : (v : {v : Fin L // v ∉ leftBlock L L}) → Fin q) :
    cutColumn ψ L b = fullLeftEquiv L q ψ := by
  ext a
  change ψ ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L L)).symm (a, b)) =
    ψ ((leftConfigOfFinEquiv (le_refl L)).symm a)
  apply congrArg ψ
  funext v
  rw [Entropy.cutEquiv_symm_apply_mem _ _ (mem_leftBlock.mpr v.isLt)]
  rfl

/-- A viable final family contains a unit vector of the asserted overlap in its span.
Source: LVV13, `algo53.tex`, the final cut of the induction, lines 652–678. -/
theorem IsViable.exists_fullLeftVector {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    {δ : ℝ} {S : Set (LeftBlockVector L q L)} (h : IsViable Γ δ S) :
    ∃ v ∈ Submodule.span ℂ S, ‖v‖ = 1 ∧
      1 - δ ≤ ‖⟪v, fullLeftEquiv L q Γ⟫_ℂ‖ := by
  obtain ⟨φ, hφ, hoverlap, hsupport⟩ := h
  let b : (v : {v : Fin L // v ∉ leftBlock L L}) → Fin q :=
    fun v ↦ False.elim (v.2 (mem_leftBlock.mpr v.1.isLt))
  refine ⟨fullLeftEquiv L q φ, ?_, ?_, ?_⟩
  · simpa only [cutColumn_full] using hsupport b
  · simpa only [LinearIsometryEquiv.norm_map] using hφ
  · simpa only [LinearIsometryEquiv.inner_map_map] using hoverlap

end TNLean.MPS.AreaLaw
