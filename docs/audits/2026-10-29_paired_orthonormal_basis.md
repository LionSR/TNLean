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

This is uncompiled proof text, written under the user's explicit instruction
to perform no Lean builds or compilation. Source checks inspect the exact
Mathlib signatures used, generated imports, line length, trailing whitespace,
and absence of proof-integrity placeholders. The tactic-pattern scanner is
also run. These checks do not establish Lean elaboration or kernel checking.

Issue #7581 remains open: this basis construction must be compiled together
with its foundation, and the separate real and complex matrix-congruence
capstones must consume the constructed basis before the source theorem can
be marked complete.
