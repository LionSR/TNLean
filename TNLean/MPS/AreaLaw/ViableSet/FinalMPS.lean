/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Span
import TNLean.MPS.AreaLaw.ViableSet.Endpoints

/-!
# A normalized matrix product state in the final viable span

Finite linear combinations add internal cut ranks. Consequently the span of a finite
family of left matrix product states has bond bound equal to the family cardinality
times its individual effective bond bound. At the final cut, a viable witness belongs
to precisely this span and is already normalized with the prescribed overlap.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Claim `c:2`,
lines 520--527, and the final cut of the induction, lines 652--678. The finite-span
argument is algebraic and does not use an independent area-law approximation theorem.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The span of a finite left MPS family has bond bound its cardinality times the
effective individual bond bound. This is the actual finite-sum rank estimate of LVV13,
`algo53.tex`, Claim `c:2`, lines 520--527, in left-chain coordinates. -/
theorem isOpenMPS_leftChain_of_mem_span {L q i b : ℕ}
    (S : Finset (LeftBlockVector L q i)) (hS : ∀ v ∈ S, IsLeftOpenMPS b v)
    {v : LeftBlockVector L q i}
    (hv : v ∈ Submodule.span ℂ (S : Set (LeftBlockVector L q i))) :
    IsOpenMPS i q (S.card * max 1 b) (fun x ↦ v (leftConfigOfFin x)) := by
  classical
  by_cases hEmpty : S = ∅
  · subst S
    have hvzero : v = 0 := by
      simpa only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] using hv
    subst v
    apply isOpenMPS_of_internal_cutMatrix_rank_le (WithLp.toLp 2 fun _ ↦ 0)
    intro k _ _
    have hzero : cutMatrix (WithLp.toLp 2 (fun _ : (Fin i → Fin q) ↦ (0 : ℂ))) k = 0 := by
      ext x y
      rfl
    rw [hzero, Matrix.rank_zero]
    exact Nat.zero_le _
  · have hcard : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
    have hprod : 1 ≤ S.card * max 1 b := by
      simpa only [one_mul] using Nat.mul_le_mul hcard (le_max_left 1 b)
    simpa only [IsLeftOpenMPS, max_eq_right hprod] using
      isLeftOpenMPS_of_mem_span S hS hv

/-- A viable final family of left MPS contains a normalized full-chain MPS witness
with its asserted overlap. LVV13, `algo53.tex`, final induction, lines 652--678. -/
theorem IsViable.exists_openMPS_of_forall_isLeftOpenMPS {L q b : ℕ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ : ℝ}
    {S : Finset (LeftBlockVector L q L)}
    (h : IsViable Γ δ (S : Set (LeftBlockVector L q L)))
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v) :
    ∃ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 ∧
      1 - δ ≤ ‖⟪ψ, Γ⟫_ℂ‖ ∧ IsOpenMPS L q (S.card * max 1 b) (fun x ↦ ψ x) := by
  obtain ⟨v, hv, hvnorm, hoverlap⟩ := h.exists_fullLeftVector
  let ψ := (fullLeftEquiv L q).symm v
  refine ⟨ψ, ?_, ?_, ?_⟩
  · simpa only [ψ, LinearIsometryEquiv.norm_map] using hvnorm
  · have hinner : ⟪ψ, Γ⟫_ℂ = ⟪v, fullLeftEquiv L q Γ⟫_ℂ := by
      simpa only [ψ, LinearIsometryEquiv.apply_symm_apply] using
        ((fullLeftEquiv L q).inner_map_map ψ Γ).symm
    rwa [hinner]
  · exact isOpenMPS_leftChain_of_mem_span S hS hv

/-- The final `(L,s,b,δ)`-viable family gives a normalized full-chain MPS of bond
dimension at most `s * max 1 b` and overlap at least `1 - δ`. LVV13, `algo53.tex`,
final induction, lines 652--678. -/
theorem IsViableMPS.exists_openMPS {L q s b : ℕ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ : ℝ}
    {S : Finset (LeftBlockVector L q L)} (h : IsViableMPS Γ s b δ S) :
    ∃ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 ∧
      1 - δ ≤ ‖⟪ψ, Γ⟫_ℂ‖ ∧ IsOpenMPS L q (s * max 1 b) (fun x ↦ ψ x) := by
  obtain ⟨ψ, hnorm, hoverlap, hMPS⟩ :=
    h.2.2.exists_openMPS_of_forall_isLeftOpenMPS h.2.1
  refine ⟨ψ, hnorm, hoverlap, ?_⟩
  apply isOpenMPS_of_internal_cutMatrix_rank_le ψ
  intro k hk0 hkL
  exact (hMPS.rank_cutMatrix_le hk0 hkL).trans (Nat.mul_le_mul_right (max 1 b) h.1)

end TNLean.MPS.AreaLaw
