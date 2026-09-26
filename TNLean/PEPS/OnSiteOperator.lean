/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import TNLean.Algebra.MonomialMatrix

/-!
# On-site operators on lattice configurations

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Section
"Symmetric PEPS", `Papers/2011.12127/TN-Review-main.tex` lines 1437–1443 and 1462–1466: a
global on-site symmetry of a PEPS acts by the same operator `U` at every site, `U^{⊗ N}`.

**Formalized here.** The operator `U^{⊗ V}` on the coefficient vectors of configurations
`σ : V → Fin d` of a finite set `V` of sites, and its form when `U` is a monomial matrix: the
permutation acts site by site and the phases multiply.

## Main definitions

* `TNLean.PEPS.onSiteOperator`: the matrix of `U^{⊗ V}`.

## Main results

* `TNLean.PEPS.onSiteOperator_monomial`: `U^{⊗ V}` of a monomial matrix is monomial.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] {d : ℕ}

/-- The on-site operator `U^{⊗ V}` on configurations: its entry at `(σ', σ)` is
`∏_v U_{σ' v, σ v}`. -/
def onSiteOperator (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (V → Fin d) (V → Fin d) ℂ :=
  Matrix.of fun σ' σ => ∏ v, U (σ' v) (σ v)

theorem onSiteOperator_apply (U : Matrix (Fin d) (Fin d) ℂ) (σ' σ : V → Fin d) :
    onSiteOperator U σ' σ = ∏ v, U (σ' v) (σ v) := rfl

/-- The on-site operator of a monomial matrix `U |s⟩ = φ(s) |π s⟩` is monomial: it applies
`π` at every site and multiplies the phases of all sites. -/
theorem onSiteOperator_monomial [DecidableEq V] (π : Equiv.Perm (Fin d)) (φ : Fin d → ℂ) :
    onSiteOperator (V := V) (Matrix.monomial π φ) =
      Matrix.monomial (Equiv.piCongrRight fun _ => π) fun σ => ∏ v, φ (σ v) := by
  ext σ' σ
  simp only [onSiteOperator_apply, Matrix.monomial_apply, Fintype.prod_ite_zero]
  congr 1
  exact propext ⟨fun h => funext h, fun h v => congrFun h v⟩

end PEPS
end TNLean
