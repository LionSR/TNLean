# Paired orthonormal basis construction for #7581

## Source and statement

`Papers/1703.09188/paper_v2.tex`, proof of `corconj`, lines 1129–1140,
uses the orthogonal normal form of a real skew-unitary matrix. The new
`LinearIsometry.exists_paired_orthonormalBasis` supplies the complete
paired-basis existence step, on Mathlib's real inner-product spaces and
linear isometries. In dimension `2*m`, for an isometry `J` satisfying
`J (J x) = -x`, it constructs an orthonormal basis indexed by
`Fin m × Fin 2` with

```text
J (B (i, 0)) = -B (i, 1)
J (B (i, 1)) =  B (i, 0).
```

The orientation agrees with the paper's `Y = !![0,1;-1,0]`. There is no
assumed paired basis, invariant decomposition, or sign choice in the
hypotheses. The preceding foundation proves that a real skew-orthogonal
matrix supplies the required square-minus-one identity.

## Construction and reuse

The dimension-zero case uses the empty orthonormal family. At a successor,
a unit vector gives the orthonormal pair `x, -J x`. Its span has dimension
two by Mathlib's `finrank_span_eq_card`; the orthogonal complement has
dimension `2*m` by `Submodule.finrank_add_finrank_orthogonal`. The foundation's
`restrictInvariantOrthogonal` restricts the same operator to that complement
and retains its square-minus-one identity, so the induction hypothesis
applies. `Fin.cases` adjoins the pair to the complement's basis. Mixed inner
products vanish by Mathlib's orthogonal-complement lemmas. Cardinality and
linear independence give full span, and `OrthonormalBasis.mk` supplies the
bundled basis.

The proof uses the pinned Mathlib sources directly; it introduces no local
linear-algebra structures, compatibility aliases, or extra source hypotheses.
The import aggregator was regenerated. The repeated cardinality-to-basis
step is recorded in the tactic ledger.

## Validation boundary

Hosted build job 123434027875 at exact code head
`5ac5980c6bd709812788fc8dcb2b1edd1a5eba30` compiled this basis construction,
its foundation and both consuming matrix normal-form capstones. The full
repository build and strict Lean checks passed, followed by Blueprint web
and PDF checks. The basis and matrix normal-form Blueprint nodes now carry
`leanok`. The separate MPU classification statement remains `notready`.

No local Lean invocation or persistent proof fixture was used. Source/API,
generated import, formatting, width and integrity checks were also run.
Issue #7581 remains open pending integration of the verified matrix slice.
