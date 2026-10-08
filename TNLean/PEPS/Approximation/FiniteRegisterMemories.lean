/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutOwnerMap
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-dimensional memories of actual register sublists

The polynomial-PEPS manuscript permits arbitrary finite private dimensions
(`04-compression.tex`, lines 5–6), states that every Hilbert space is finite
without a bound on unspecified dimensions (lines 17–19), and retains private
registers until the final trace (lines 23–30). Consequently each register space,
and hence every regional discarded memory, is finite-dimensional.

The hypothesis is imposed on the individual register spaces. Finite-dimensionality
of their full tensor product alone would not imply this: a zero-dimensional
register may annihilate an infinite-dimensional tensor factor. The results below
allow zero-dimensional registers and require no lower bound on any dimension.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
sec:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-actual-sampling-finiteregistermemories-01
TNLean.PEPS.PairEffect.Layout.finiteDimensional_mem_of_registers
Provenance-ID: 8769-actual-sampling-finiteregistermemories-02
TNLean.PEPS.PairEffect.Layout.finiteDimensional_mem_restrict_mapOwner_mapOwner
Provenance-ID: 8769-actual-sampling-finiteregistermemories-03
TNLean.PEPS.PairEffect.Layout.restrictedDiscardBasis
-/


noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Layout
variable {P Q R : Type}

/-- A finite list of finite-dimensional register spaces has finite-dimensional
memory, including when one of its factors is zero-dimensional. -/
theorem finiteDimensional_mem_of_registers (ℓ : Layout P)
    (h : ∀ r ∈ ℓ, FiniteDimensional ℂ r.space) : FiniteDimensional ℂ (Mem ℓ) := by
  induction ℓ with
  | nil => infer_instance
  | cons r ℓ ih =>
    let : FiniteDimensional ℂ r.space := h r (List.mem_cons_self ..)
    let : FiniteDimensional ℂ (Mem ℓ) := ih (fun s hs ↦ h s (List.mem_cons_of_mem _ hs))
    change FiniteDimensional ℂ (r.space ⊗[ℂ] Mem ℓ)
    infer_instance

/-- Selecting either region after two owner identifications preserves finite
dimensionality, because it selects the same original finite register spaces. -/
theorem finiteDimensional_mem_restrict_mapOwner_mapOwner (q : P → Q) (r : Q → R)
    (f : R → Bool) (ℓ : Layout P) (h : ∀ s ∈ ℓ, FiniteDimensional ℂ s.space) :
    FiniteDimensional ℂ (Mem (restrict f (mapOwner r (mapOwner q ℓ)))) := by
  apply finiteDimensional_mem_of_registers
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hs).1
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact h u hu

/-- An actual finite orthonormal basis of the selected discarded registers,
after both owner identifications. No basis or dimension bound is supplied as a premise. -/
def restrictedDiscardBasis (q : P → Q) (r : Q → R) (f : R → Bool)
    (ℓ : Layout P) (h : ∀ s ∈ ℓ, FiniteDimensional ℂ s.space) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (Mem (restrict f (mapOwner r (mapOwner q ℓ)))))) ℂ
      (Mem (restrict f (mapOwner r (mapOwner q ℓ)))) := by
  letI := finiteDimensional_mem_restrict_mapOwner_mapOwner q r f ℓ h
  exact stdOrthonormalBasis ℂ _

end TNLean.PEPS.PairEffect.Layout
