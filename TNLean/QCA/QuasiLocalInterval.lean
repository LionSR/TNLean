/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.IntervalCoordinates
import TNLean.QCA.QuasiLocal

/-!
# Consecutive interval observables in the quasi-local algebra

Numbering a consecutive integer interval gives a star-algebra inclusion of
its ordinary matrix coordinates into the quasi-local algebra. The inclusion
preserves the matrix operator norm. Empty intervals are included.

## References

* Nachtergaele, *The spectral gap for some spin chains with discrete symmetry breaking*, Commun.
  Math. Phys. 175 (1996), arXiv:cond-mat/9410110, Section 3: the finite local observable
  convention.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2285--2300.
-/

open scoped ComplexOrder

namespace SpinChain

/-- The quasi-local inclusion of an observable in consecutive matrix coordinates.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3. -/
noncomputable def quasiLocalIntervalObservable (d : ℕ) [NeZero d] (a : ℤ) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  (quasiLocalObservable d (finiteChainRegion a N)).comp
    (intervalCoordinates d a N).symm.toStarAlgHom

/-- The interval inclusion is the finite-region inclusion after coordinate transport.
Source: arXiv:1703.09188, Appendix, lines 2285--2300. -/
@[simp] theorem quasiLocalIntervalObservable_apply (d : ℕ) [NeZero d] (a : ℤ) {N : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    quasiLocalIntervalObservable d a N X = quasiLocalObservable d (finiteChainRegion a N)
      ((intervalCoordinates d a N).symm X) := rfl

/-- The interval inclusion preserves the matrix operator norm.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
theorem norm_quasiLocalIntervalObservable (d : ℕ) [NeZero d] (a : ℤ) {N : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    ‖quasiLocalIntervalObservable d a N X‖ = ‖CStarMatrix.ofMatrix X‖ := by
  rw [quasiLocalIntervalObservable, StarAlgHom.comp_apply, norm_quasiLocalObservable]
  exact NonUnitalStarAlgHom.norm_map
    (CStarMatrix.ofMatrixStarAlgEquiv.symm.trans (intervalCoordinates d a N).symm)
    (EquivLike.injective _) (CStarMatrix.ofMatrix X)

end SpinChain
