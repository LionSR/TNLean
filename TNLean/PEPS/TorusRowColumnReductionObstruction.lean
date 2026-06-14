import TNLean.MPS.Defs

/-!
# The row-and-column reduction cannot factor the row-cut gauge

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) concludes a per-edge gauge
`B^i = λ · (X ⊗ Y) A^i (X⁻¹ ⊗ Y⁻¹)`, with `X` on the horizontal virtual legs
and `Y` on the vertical ones.  A natural route reduces this corollary to the
formalized one-dimensional matrix product state corollary applied row-wise and
column-wise: contract each torus row over its horizontal bonds into a single
super-site, obtaining a matrix product state tensor on the super-physical space
`(Fin d)^width` with super-bond space the collected vertical bonds, and apply
the one-dimensional Fundamental Theorem to the resulting closed chain of `m`
super-sites.

That application delivers **one** conjugating matrix `Z` on the whole collected
vertical-bond space together with a root of unity, with `B`-super-tensor equal
to the `Z`-conjugate of the `A`-super-tensor.  To reach the per-edge conclusion
the matrix `Z` would have to factor as a tensor product `⨂ Y_x` of one gauge per
vertical edge.  This file records, with a machine-checked refutation, that the
one-dimensional reduction does **not** force that factorization: the
super-tensor relation produced by the row reduction is invariant under
conjugation by an arbitrary invertible matrix of the collected bond space, and
an arbitrary invertible matrix of a tensor-product space is not a tensor
product even up to a scalar.

## The conjugation-invariance obstruction

The one-dimensional reduction reads the row super-tensor only as an abstract
family of matrices on the collected vertical-bond space, together with the
closed-chain trace coefficients (the torus state).  Both of these inputs are
*conjugation invariant*: if `A` is a normal matrix product state tensor and `G`
is any invertible matrix of the bond space, the conjugate family
`B^i = G⁻¹ A^i G` has the same closed-chain coefficients (the trace is invariant
under conjugation) and the same block injectivity (conjugation by an invertible
matrix preserves the span of any family).  So the row reduction cannot
distinguish a per-edge-gauged `B` from a `B` produced by an arbitrary,
non-product conjugation `G`; only the former has the per-edge conclusion.

Because the `A`-super-tensor here is injective, its only self-conjugations are
the scalars, so the conjugating matrix of the reduction is `G` up to a nonzero
scalar.  When `G` is not a tensor product even after rescaling, no per-edge
factorization of the reduction's gauge exists.  The witness below makes this
concrete on the smallest collected-bond space carrying two vertical edges,
`Fin 2 × Fin 2`: the matrix-unit family `A` is injective at block length one,
and the conjugator `G` is a "controlled" invertible matrix whose four
`Fin 2 × Fin 2` blocks are not mutually proportional, hence not a scalar times
any tensor product.

The companion route through a column-wise application does not repair this: a
single column cut crosses the horizontal edges of one column boundary, an
entirely disjoint set of bonds from the vertical edges crossed by a row cut, so
the row-cut gauge on the vertical-bond space and the column-cut gauge on the
horizontal-bond space share no bond and impose no consistency equation on each
other.  The factorization the per-edge conclusion needs is therefore not forced
by either application, nor by the two together.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and
  proof sketch at lines 2296--2445 of `Papers/1804.04964/paper_normal.tex`,
  whose one-dimensional engine is the overlapping-window corollary
  `fundamentalTheorem_normalMPSChain_of_overlap`](https://arxiv.org/abs/1804.04964);
  the row-and-column reduction and the absence of a coherence question are
  discussed in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section "No
  coherence question between rows".
-/

open scoped Matrix

namespace TNLean
namespace PEPS
namespace RowColumnReductionObstruction

open MPSTensor

/-! ### The collected-bond space and its tensor-product reading

The smallest collected vertical-bond space carrying two vertical edges is
`Fin 4`, read as `Fin 2 × Fin 2` through the pairing `(r, s) ↦ 2 * r + s`.  A
*per-edge gauge* on this space is a tensor product `Y₀ ⊗ Y₁` of one `Fin 2`
gauge per edge; in entry form `(Y₀ ⊗ Y₁)_{(r,s),(r',s')} = (Y₀)_{r r'} (Y₁)_{s s'}`.
We do not need the general Kronecker product: the obstruction is a property of the
four `2 × 2` blocks `M_{r r'}` of a `4 × 4` matrix `M`, `(M_{r r'})_{s s'} =
M_{(2r+s),(2r'+s')}`, namely that a product has all four blocks proportional to
the single factor `Y₁`. -/

/-- The `(r, s)` index of `Fin 4` under the pairing `(r, s) ↦ 2 * r + s`. -/
def pair (r s : Fin 2) : Fin 4 := ⟨2 * r.val + s.val, by omega⟩

/-- The `(s', s)` entry of the `(r', r)` block of a `4 × 4` matrix under the
pairing.  A matrix is a per-edge product `Y₀ ⊗ Y₁` exactly when every block
`blockEntry M r r'` equals `(Y₀)_{r r'} • Y₁` for fixed gauges `Y₀, Y₁`. -/
def blockEntry (M : Matrix (Fin 4) (Fin 4) ℂ) (r r' : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun s s' => M (pair r s) (pair r' s')

/-- `M` is a *per-edge product matrix* when it factors as a tensor product of one
`Fin 2`-gauge per vertical edge: there are matrices `Y₀, Y₁` with every entry
`M_{(r,s),(r',s')} = (Y₀)_{r r'} (Y₁)_{s s'}`. -/
def IsPerEdgeProduct (M : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ Y₀ Y₁ : Matrix (Fin 2) (Fin 2) ℂ,
    ∀ r s r' s' : Fin 2, M (pair r s) (pair r' s') = Y₀ r r' * Y₁ s s'

/-- In a per-edge product matrix the two diagonal blocks `(0,0)` and `(0,1)` are
proportional: `(Y₀)_{0 1} • blockEntry M 0 0 = (Y₀)_{0 0} • blockEntry M 0 1`,
since each block is a scalar multiple of the common factor `Y₁`. -/
theorem blocks_proportional_of_isPerEdgeProduct {M : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsPerEdgeProduct M) (s s' : Fin 2) :
    blockEntry M 0 0 s s' * blockEntry M 0 1 1 1 =
      blockEntry M 0 1 s s' * blockEntry M 0 0 1 1 := by
  obtain ⟨Y₀, Y₁, hY⟩ := h
  simp only [blockEntry, hY]
  ring

end RowColumnReductionObstruction
end PEPS
end TNLean
