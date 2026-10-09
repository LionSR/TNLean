/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LocalCircuit
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Tensoring physical sites

The two configuration functions are paired at each original site, using the
canonical finite-product encoding. Tensoring two supported operators then
gives an operator on the union of their original supports, with local
dimension equal to the product of the two original local dimensions.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 416–424 and 513–524,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: the doubled Hamiltonians
have the original physical interaction supports.
-/

open scoped Kronecker

namespace QuantumCircuit

/-- Pair the two configuration values at every original site, encoding a pair
by `finProdFinEquiv`.

Source: polynomial-PEPS, `02-information.tex`, lines 416–424. -/
def sitePairConfigurationEquiv (ι : Type*) (d e : ℕ) :
    ((ι → Fin d) × (ι → Fin e)) ≃ (ι → Fin (d * e)) :=
  (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin d) (fun _ ↦ Fin e)).symm.trans
    (Equiv.arrowCongr (Equiv.refl ι) finProdFinEquiv)

/-- Tensoring two physical operators and pairing their local coordinates
preserves the union of their original supports. Empty site sets and zero
local dimensions are included.

Source: polynomial-PEPS, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_kronecker_mem_supportedOperators
    {ι : Type*} [Fintype ι] {d e : ℕ} {S T : Set ι}
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    {B : Matrix (ι → Fin e) (ι → Fin e) ℂ}
    (hA : A ∈ supportedOperators d S) (hB : B ∈ supportedOperators e T) :
    Matrix.reindex (sitePairConfigurationEquiv ι d e) (sitePairConfigurationEquiv ι d e)
      (A ⊗ₖ B) ∈ supportedOperators (d * e) (S ∪ T) := by
  refine Submodule.span_induction₂
    (p := fun A B _ _ ↦
      Matrix.reindex (sitePairConfigurationEquiv ι d e) (sitePairConfigurationEquiv ι d e)
        (A ⊗ₖ B) ∈ supportedOperators (d * e) (S ∪ T))
    ?mem ?zeroL ?zeroR ?addL ?addR ?smulL ?smulR hA hB
  case mem =>
    rintro _ _ ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
    refine Submodule.subset_span
      ⟨fun i ↦ Matrix.reindex finProdFinEquiv finProdFinEquiv (m i ⊗ₖ n i), ?_, ?_⟩
    · intro i hi
      simp only [hm i (fun h ↦ hi (Or.inl h)), hn i (fun h ↦ hi (Or.inr h)),
        Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
    · ext x y
      exact Finset.prod_mul_distrib.symm
  case zeroL => intro y _; rw [Matrix.zero_kronecker]; exact Submodule.zero_mem _
  case zeroR => intro x _; rw [Matrix.kronecker_zero]; exact Submodule.zero_mem _
  case addL =>
    intro x y z _ _ _ hxz hyz; rw [Matrix.add_kronecker]; exact Submodule.add_mem _ hxz hyz
  case addR =>
    intro x y z _ _ _ hxy hxz; rw [Matrix.kronecker_add]; exact Submodule.add_mem _ hxy hxz
  case smulL => intro r x y _ _ hxy; rw [Matrix.smul_kronecker]; exact Submodule.smul_mem _ r hxy
  case smulR => intro r x y _ _ hxy; rw [Matrix.kronecker_smul]; exact Submodule.smul_mem _ r hxy

end QuantumCircuit
