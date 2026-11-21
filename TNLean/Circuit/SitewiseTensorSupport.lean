/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import QICLean.ManyBody.Sites.Relabel
import QICLean.ManyBody.Sites.SitewiseProduct

/-!
# Tensoring physical sites

The two configuration functions are paired at each original site, using the
canonical finite-product encoding. Tensoring two supported operators gives an
operator on the union of their original supports
(`ManyBody.reindex_kronecker_mem_supportedOperators`), on the system with basis
`Fin d × Fin e` at every site; the encoding of the pairs in `Fin (d * e)` is a
relabelling of the basis at every site, which keeps supports
(`ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators`).

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

end QuantumCircuit
