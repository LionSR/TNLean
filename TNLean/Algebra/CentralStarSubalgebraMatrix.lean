/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.StarSubalgebraFactor

/-!
# Full-matrix presentation of a star-subalgebra with scalar centre

Let `S` be a unital star-subalgebra of a nonzero finite complex matrix algebra whose centre
consists exactly of the scalar multiples of its unit. Then `S` is star-isomorphic to a single
full complex matrix algebra `M_r(ℂ)` with `r ≥ 1`, and its complex dimension is `r * r`.

The star-isomorphism itself is the companion library's theorem
`StarSubalgebra.exists_starAlgEquiv_matrix_of_isCentral`; the statement below packages it with
the resulting positive matrix size and the dimension identity in the single form used by the
quantum-cellular-automaton support-algebra development.

Some nontriviality hypothesis is indispensable. For an empty index type the ambient matrix
algebra is the zero ring; its centre is still the scalar image, yet it is star-isomorphic to no
`M_r(ℂ)` with `r ≥ 1`. Here that role is played by nonemptiness of the matrix index.

## Main results

* `StarSubalgebra.exists_starAlgEquiv_matrix_and_finrank_of_isCentral` — a star-subalgebra of a
  nonzero full complex matrix algebra whose centre is scalar is star-isomorphic to `M_r(ℂ)` for
  a positive `r`, and has complex dimension `r * r`.

## References

* B. Schumacher and R. F. Werner, *Reversible quantum cellular automata*, quant-ph/0405174,
  Proposition `Csform`, lines 2082--2098.
* D. Gross, V. Nesme, H. Vogts, and R. F. Werner, *Index theory of one-dimensional quantum walks
  and cellular automata*, arXiv:0910.3675, lines 1276--1282.

**Scope restriction (Schumacher--Werner `Csform`):** the result below is not a formalization of
Proposition `Csform`. That proposition decomposes an abstract finite-dimensional C*-algebra into
a direct sum of full matrix algebras, cutting by the minimal projections of its centre. What is
formalized here is the single building block of that decomposition, for an algebra already
presented as a star-subalgebra of a matrix algebra: neither the abstract C*-algebra generality
nor the central cut is covered. The omitted content and its elimination plan are recorded in the
companion library's paper-gap note
<https://sirui-lu.com/QICLean/paper-gaps/sw04_csform_matrix_scope.pdf>.
-/

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A star-subalgebra of complex matrices with scalar centre is a full matrix algebra of a
definite size.** Let `S` be a star-subalgebra of a nonzero full complex matrix algebra whose
centre consists of the scalar multiples of its unit. Then there is an `r ≥ 1` with
`S ≃⋆ₐ[ℂ] M_r(ℂ)` and `dim_ℂ S = r * r`.

This is the building-block step of the structure theorem for finite-dimensional C*-algebras,
Schumacher--Werner, quant-ph/0405174, Proposition `Csform`, lines 2082--2098, specialized to an
algebra presented as a star-subalgebra of a matrix algebra; the scope restriction is described
in the module docstring. It is the conclusion invoked by Gross--Nesme--Vogts--Werner,
arXiv:0910.3675, `References/0910.3675v2/QCI12.tex`, lines 1276--1282, where a support algebra is
first shown to have scalar centre, because a central element of it is central in the generated
quasi-local algebra, and is then identified with `M_{r(x)}(ℂ)`. -/
theorem exists_starAlgEquiv_matrix_and_finrank_of_isCentral [Nonempty n]
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) [Algebra.IsCentral ℂ ↥S] :
    ∃ r : ℕ, 0 < r ∧ Nonempty (↥S ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ) ∧
      Module.finrank ℂ ↥S = r * r := by
  obtain ⟨r, hr, ⟨e⟩⟩ := S.exists_starAlgEquiv_matrix_of_isCentral
  exact ⟨r, Nat.pos_of_ne_zero hr.out, ⟨e⟩, S.finrank_eq_mul_self_of_starAlgEquiv_matrix e⟩

end StarSubalgebra
