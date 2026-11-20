/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Tensoring physical sites

The two configuration functions are paired at each original site. Tensoring two supported
operators then gives an operator on the union of their original supports, whose local basis
at a site is the product of the two original local bases.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 416–424 and 513–524,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: the doubled Hamiltonians
have the original physical interaction supports.
-/

open scoped Kronecker

namespace QuantumCircuit

/-- Pair the two configuration values at every original site: the paired site carries the
pair of the two values.

Source: polynomial-PEPS, `02-information.tex`, lines 416–424. -/
def sitePairConfigurationEquiv (ι : Type*) (d e : ℕ) :
    ((ι → Fin d) × (ι → Fin e)) ≃ (ι → Fin d × Fin e) :=
  (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin d) (fun _ ↦ Fin e)).symm

/-- Tensoring two physical operators and pairing their local coordinates
preserves the union of their original supports. Empty site sets and zero
local dimensions are included.

Source: polynomial-PEPS, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_kronecker_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d e : ℕ} {S T : Finset ι}
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    {B : Matrix (ι → Fin e) (ι → Fin e) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin e) T) :
    Matrix.reindex (sitePairConfigurationEquiv ι d e) (sitePairConfigurationEquiv ι d e)
      (A ⊗ₖ B) ∈ ManyBody.supportedOperators (fun _ ↦ Fin d × Fin e) (S ∪ T) := by
  induction hA using ManyBody.supportedOperators_induction with
  | prod m hm =>
    induction hB using ManyBody.supportedOperators_induction with
    | prod n hn =>
      have heq : Matrix.reindex (sitePairConfigurationEquiv ι d e)
          (sitePairConfigurationEquiv ι d e)
          (ManyBody.prodOp (X := fun _ : ι ↦ Fin d) m ⊗ₖ
            ManyBody.prodOp (X := fun _ : ι ↦ Fin e) n) =
          ManyBody.prodOp (X := fun _ : ι ↦ Fin d × Fin e) fun i ↦ m i ⊗ₖ n i := by
        ext x y
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
          ManyBody.prodOp_apply, Matrix.kroneckerMap_apply]
        exact Finset.prod_mul_distrib.symm
      rw [heq]
      refine ManyBody.prodOp_mem_supportedOperators fun i hi ↦ ?_
      simp only [hm i (fun h ↦ hi (Finset.mem_union_left _ h)),
        hn i (fun h ↦ hi (Finset.mem_union_right _ h)), Matrix.one_kronecker_one]
    | add B C _ _ hB hC =>
      convert add_mem hB hC using 1
      ext x y
      simp [Matrix.kronecker_add]
    | smul c B _ hB =>
      convert SMulMemClass.smul_mem c hB using 1
      ext x y
      simp [Matrix.kronecker_smul]
  | add A C _ _ hA hC =>
    convert add_mem hA hC using 1
    ext x y
    simp [Matrix.add_kronecker]
  | smul c A _ hA =>
    convert SMulMemClass.smul_mem c hA using 1
    ext x y
    simp [Matrix.smul_kronecker]

end QuantumCircuit
