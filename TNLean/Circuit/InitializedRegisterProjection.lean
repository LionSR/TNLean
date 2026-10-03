/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SelectedZeroRegisterReflection
import TNLean.Circuit.SelectedZeroRegisterReflectionPool
import TNLean.Circuit.ExactSubspaceAmplification
open QuantumCircuit

/-!
# The projection onto initialized physical flags

An injective basis inclusion has range projection equal to the diagonal
indicator of its encoded basis configurations. In particular, fixing selected
qudit flags to zero gives exactly the projection tested by the reversible
selected-zero-register reflection. All unselected sites remain arbitrary.

Source: the initialized-subspace and image reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix

namespace QuantumCircuit

/-- The range projection of an injective physical basis inclusion is the
diagonal indicator of its encoded configurations. Source: initialized
subspace projections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initializedBasisMatrix_mul_conjTranspose {ι κ : Type*}
    [Fintype κ] [DecidableEq ι] (e : κ ↪ ι) :
    initializedBasisMatrix e * (initializedBasisMatrix e)ᴴ =
      diagonal (fun x ↦ if x ∈ Set.range e then (1 : ℂ) else 0) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hx : x ∈ Set.range e
    · obtain ⟨u, rfl⟩ := hx
      simp [initializedBasisMatrix, Matrix.mul_apply, Matrix.one_apply,
        e.injective.eq_iff]
    · have hu : ∀ u, x ≠ e u := fun u h ↦ hx ⟨u, h.symm⟩
      have hu' : ∀ u, e u ≠ x := fun u h ↦ hx ⟨u, h⟩
      simp [initializedBasisMatrix, Matrix.mul_apply, hu, hu']
  · rw [Matrix.diagonal_apply_ne _ hxy]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hxu : x = e u
    · have hyu : y ≠ e u := fun h ↦ hxy (hxu.trans h.symm)
      simp [initializedBasisMatrix, Matrix.conjTranspose_apply, Matrix.one_apply, hyu]
    · simp [initializedBasisMatrix, Matrix.one_apply, hxu]

variable {d n a : ℕ} [NeZero d]

/-- Initialize the selected flags to zero and retain arbitrary configurations
on every remaining site. Source: initial and success projections in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroFlagEmbedding (s : Fin a ↪ Fin n) :
    ({i : Fin n // i ∉ Set.range s} → Fin d) ↪ (Fin n → Fin d) where
  toFun u i := if hi : i ∈ Set.range s then 0 else u ⟨i, hi⟩
  inj' u v huv := by
    funext i
    have h := congrFun huv i.1
    simpa only [dite_eq_right i.2] using h

/-- The selected flags of an encoded input are all zero. Source: initialized
flags in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroFlagEmbedding_apply_selected (s : Fin a ↪ Fin n)
    (u : {i : Fin n // i ∉ Set.range s} → Fin d) (j : Fin a) :
    zeroFlagEmbedding s u (s j) = 0 := by
  simp [zeroFlagEmbedding]

/-- The image consists precisely of configurations with selected flags zero.
No validity test on the other sites is imposed. Source: initial and success
subspaces in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem mem_range_zeroFlagEmbedding_iff (s : Fin a ↪ Fin n) (x : (Fin n → Fin d)) :
    x ∈ Set.range (zeroFlagEmbedding (d := d) s) ↔ ∀ j, x (s j) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact zeroFlagEmbedding_apply_selected s u j
  · intro hx
    refine ⟨fun i ↦ x i.1, ?_⟩
    funext i
    by_cases hi : i ∈ Set.range s
    · obtain ⟨j, rfl⟩ := hi
      rw [zeroFlagEmbedding_apply_selected, hx]
    · change (if h : i ∈ Set.range s then 0 else x (⟨i, h⟩ :
        {i : Fin n // i ∉ Set.range s}).1) = x i
      rw [dite_eq_right hi]

/-- The initial-subspace projection is exactly the selected-zero diagonal
projection. Source: image reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroFlagEmbedding_range_projection (s : Fin a ↪ Fin n) :
    initializedBasisMatrix (zeroFlagEmbedding (d := d) s) *
        (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))ᴴ =
      diagonal (fun x : (Fin n → Fin d) ↦ if ∀ j, x (s j) = 0 then (1 : ℂ) else 0) := by
  classical
  rw [initializedBasisMatrix_mul_conjTranspose]
  congr 1
  funext x
  simp only [mem_range_zeroFlagEmbedding_iff]

/-- The initialized-range matrix is an actual orthogonal projection.
Source: initial and success subspaces in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isStarProjection_zeroFlagEmbedding_range (s : Fin a ↪ Fin n) :
    IsStarProjection
      (initializedBasisMatrix (zeroFlagEmbedding (d := d) s) *
        (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))ᴴ) := by
  classical
  exact isStarProjection_mul_conjTranspose_of_isometry _
    (initializedBasisMatrix_isIsometry _)

/-- The reversible selected-flags circuit reflects precisely the range of
the initialized physical-input inclusion. This derives the reflection matrix
required by the amplification theorem. Source: the circuit assembly in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem selectedZeroRegisterLogical_eq_subspaceReflection (s : Fin a ↪ Fin n) :
    selectedZeroRegisterLogical (d := d) s =
      subspaceReflection
        (initializedBasisMatrix (zeroFlagEmbedding (d := d) s) *
          (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))ᴴ) := by
  rw [zeroFlagEmbedding_range_projection, subspaceReflection,
    selectedZeroRegisterLogical_eq_one_sub]

/-- The initialized-range reflection has a derived circuit with a shared
scratch pool and a complete clean identity. Neither a circuit nor a reflection
identity is supplied as a premise. Source: initial and success reflections
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isPairProduct_isCleanImplementation_zeroFlagReflection {A : ℕ}
    (hd : 2 ≤ d) (hn : 2 ≤ n) (s : Fin a ↪ Fin n) (hpool : a ≤ A) :
    ∃ U : Matrix ((Fin (n + A) → Fin d)) ((Fin (n + A) → Fin d)) ℂ,
      IsPairProduct d (n + A) (selectedZeroRegisterReflectionPoolGateCount d n a A) U ∧
      IsCleanImplementation
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A))) U
        (subspaceReflection
          (initializedBasisMatrix (zeroFlagEmbedding (d := d) s) *
            (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))ᴴ)) := by
  obtain ⟨U, hU, hclean⟩ :=
    exists_isPairProduct_isCleanImplementation_selectedZeroRegisterPool hd hn s hpool
  rw [selectedZeroRegisterLogical_eq_subspaceReflection] at hclean
  exact ⟨U, hU, hclean⟩

end QuantumCircuit
