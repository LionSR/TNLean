/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SelectedZeroRegisterReflection

/-!
# The selected zero-register reflection acts only on its flags

A diagonal operator on selected sites embeds as a diagonal operator whose
entries read only those sites. The selected zero-register reflection is
therefore supported within its selected logical flags, with no
initialization condition on any other logical site. The statement includes
an empty selection and its global scalar phase.

Source: interval input and image reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor
open QuantumCircuit

namespace MPSPreparation

variable {d a n : ℕ}

/-- Embedding a diagonal operator reads the selected coordinates and acts
as the identity on the others. Source: the selected-register reflection
identity in Section 5 of the circuit audit. -/
theorem embedOp_diagonal (s : Fin a → Fin n) (f : Cfg d a → ℂ) :
    embedOp s (Matrix.diagonal f) = Matrix.diagonal (fun x : Cfg d n ↦ f (x ∘ s)) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [embedOp_apply, agreeOff_refl]
  · have hrestrict : AgreeOff s x y → x ∘ s ≠ y ∘ s := by
      intro h h'
      apply hxy
      funext i
      by_cases hi : ∃ j, s j = i
      · obtain ⟨j, rfl⟩ := hi
        exact congrFun h' j
      · exact h i (fun j hj ↦ hi ⟨j, hj⟩)
    rw [embedOp_apply]
    by_cases hagree : AgreeOff s x y
    · simp only [hagree, ite_true, Matrix.diagonal_apply, hrestrict hagree, hxy, ite_false]
    · simp only [hagree, ite_false, Matrix.diagonal_apply, hxy]

variable [NeZero d]

/-- The selected reflection is the actual embedding of the all-zero
reflection on the selected register, without a support witness. Source:
selected zero tests in Section 5 of the circuit audit. -/
theorem selectedZeroRegisterLogical_eq_embedOp (s : Fin a ↪ Fin n) :
    selectedZeroRegisterLogical (d := d) s =
      embedOp s (Matrix.diagonal fun x : Cfg d a ↦
        if ∀ j, x j = 0 then (-1 : ℂ) else 1) := by
  rw [embedOp_diagonal]
  rfl

/-- The selected logical reflection acts only on the selected flags, for
arbitrary states on all other logical sites. Source: the input/image
reflection construction in Section 5 of the circuit audit. -/
theorem selectedZeroRegisterLogical_mem_supportedOperators (s : Fin a ↪ Fin n) :
    selectedZeroRegisterLogical (d := d) s ∈ supportedOperators d (Set.range s) := by
  rw [selectedZeroRegisterLogical_eq_embedOp]
  exact embedOp_mem_supportedOperators s.injective _

/-- A larger logical support containing the selected flags also contains
the reflection. Source: interval support preservation in Section 5 of the
circuit audit. -/
theorem selectedZeroRegisterLogical_mem_supportedOperators_of_range_subset
    (s : Fin a ↪ Fin n) {S : Set (Fin n)} (hS : Set.range s ⊆ S) :
    selectedZeroRegisterLogical (d := d) s ∈ supportedOperators d S :=
  supportedOperators_mono hS (selectedZeroRegisterLogical_mem_supportedOperators s)

end MPSPreparation
