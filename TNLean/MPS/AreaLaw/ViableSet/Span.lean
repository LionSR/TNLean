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
  exact hB.mono
    ((Nat.mul_le_mul_right (max 1 b) (Finset.card_image_le (f := f) (s := S))).trans
      (le_max_right 1 (S.card * max 1 b)))

/-- The span of a finite family of left-open matrix product states has an orthonormal
basis of no larger cardinality, and every basis vector has bond dimension at most the
finite-span budget `|S| max(1,b)`.  Thus orthonormalizing the retained subspace does not
alter the subspace and has an explicit matrix product state bond cost. -/
theorem exists_orthonormalBasis_isLeftOpenMPS_span
    {L q k b : ℕ} (S : Finset (LeftBlockVector L q k))
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) :
    ∃ (n : ℕ) (u : Fin n → LeftBlockVector L q k),
      n ≤ S.card ∧ Orthonormal ℂ u ∧
      Submodule.span ℂ (Set.range u) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      ∀ i, IsLeftOpenMPS (S.card * max 1 b) (u i) := by
  classical
  let V := Submodule.span ℂ (S : Set (LeftBlockVector L q k))
  let B := stdOrthonormalBasis ℂ V
  let u : Fin (Module.finrank ℂ V) → LeftBlockVector L q k :=
    fun i ↦ (B i : LeftBlockVector L q k)
  refine ⟨Module.finrank ℂ V, u, ?_, ?_, ?_, ?_⟩
  · exact finrank_span_finset_le_card S
  · exact B.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  · change Submodule.span ℂ (Set.range (V.subtype ∘ B)) = V
    have hB : Submodule.span ℂ (Set.range (B : Fin (Module.finrank ℂ V) → V)) = ⊤ := by
      simpa only [OrthonormalBasis.coe_toBasis] using B.toBasis.span_eq
    rw [Set.range_comp, Submodule.span_image, hB, Submodule.map_subtype_top]
  · intro i
    apply isLeftOpenMPS_of_mem_span S hS
    exact (B i).property

/-- Finite-set form of `exists_orthonormalBasis_isLeftOpenMPS_span`.  The replacement
family is orthonormal when indexed by its own elements, spans exactly the original
retained subspace, has no larger cardinality, and obeys the finite-span bond budget. -/
theorem exists_orthonormal_isLeftOpenMPS_span_finset
    {L q k b : ℕ} (S : Finset (LeftBlockVector L q k))
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) :
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ S.card ∧ Orthonormal ℂ (fun t : T ↦ t.1) ∧
      Submodule.span ℂ (T : Set (LeftBlockVector L q k)) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      ∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v := by
  classical
  obtain ⟨n, u, hn, hu, hspan, hmps⟩ := exists_orthonormalBasis_isLeftOpenMPS_span S hS
  let T := Finset.univ.image u
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · calc
      T.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
      _ ≤ S.card := hn
  · apply orthonormal_subtype_iff_ite.mpr
    intro v hv w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hw
    simpa only [hu.linearIndependent.injective.eq_iff] using
      orthonormal_iff_ite.mp hu i j
  · simpa only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hspan
  · intro v hv
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hv
    exact hmps i

end TNLean.MPS.AreaLaw
