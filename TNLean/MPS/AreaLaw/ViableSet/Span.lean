/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSSpan
import TNLean.MPS.AreaLaw.ViableSet.Basic

/-!
# Bond dimensions in the span of a viable set

The vectors retained in the size-trimming step lie in the span of the input set. The
finite-span estimate therefore bounds their bond dimensions by the cardinality of the
input set times its effective bond bound `max 1 b`, as specified by `IsLeftOpenMPS`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Claim `c:2`, lines
520–527. This is the finite-span estimate used there, with the library's existing bond
convention; it does not construct the size-trimming set.
-/

namespace TNLean.MPS.AreaLaw

/-- The finite-span estimate of LVV13, `algo53.tex`, Claim `c:2`, lines 520–527, on the
first sites of a chain. The effective input bond bound is `max 1 b`, as in
`IsLeftOpenMPS`; for `b ≥ 1` the resulting budget is `S.card * b`. -/
theorem isLeftOpenMPS_of_mem_span {L q k b : ℕ} (S : Finset (LeftBlockVector L q k))
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) {v : LeftBlockVector L q k}
    (hv : v ∈ Submodule.span ℂ (S : Set (LeftBlockVector L q k))) :
    IsLeftOpenMPS (S.card * max 1 b) v := by
  classical
  let f : LeftBlockVector L q k →ₗ[ℂ] ((Fin k → Fin q) → ℂ) :=
    { toFun := fun w x ↦ w (leftConfigOfFin x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hv' : f v ∈ Submodule.span ℂ
      ((S.image f : Finset ((Fin k → Fin q) → ℂ)) : Set ((Fin k → Fin q) → ℂ)) := by
    simpa only [Finset.coe_image] using
      (Submodule.apply_mem_span_image_of_mem_span f hv)
  have hS' : ∀ w ∈ S.image f, IsOpenMPS k q (max 1 b) w := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
    exact hS u hu
  have hB := isOpenMPS_of_mem_span (S.image f) hS' hv'
  change IsOpenMPS k q (max 1 (S.card * max 1 b)) (f v)
  apply (isOpenMPS_iff_internal_cutMatrix_rank_le (WithLp.toLp 2 (f v))).mpr
  intro j hj0 hjk
  exact (hB.rank_cutMatrix_le (ψ := WithLp.toLp 2 (f v)) hj0 hjk).trans
    ((Nat.mul_le_mul_right (max 1 b) (Finset.card_image_le (f := f) (s := S))).trans
      (le_max_right 1 (S.card * max 1 b)))

end TNLean.MPS.AreaLaw
