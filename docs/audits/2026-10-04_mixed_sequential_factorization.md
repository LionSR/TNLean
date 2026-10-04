# Mixed sequential factorization

Addresses [#8206](https://github.com/LionSR/TNLean/issues/8206).
Source: arXiv:2307.01696, page 3, footnote 4 to equations (13)–(15).

Two changes to the issue's proposed statement are necessary to state the
source's construction faithfully:

- The source bounds intermediate bond dimensions by D²; it does not claim
  monotonicity along either sweep. No monotonicity assumption or conclusion
  is introduced.
- Moving the input to the central site leaves both exterior bonds
  one-dimensional. The D²-dimensional input remains an independent leg of
  the central tensor, not the final bond of a one-sided matrix product.

The construction factors the virtual-pair coefficient matrices of the left
and right subchains independently as E_L T_L and E_R T_R. The local tensors
of each E are isometric on their bounded bonds. A central matrix F combines
the central site with the inverse polar factor. Then
C = (T_L ⊗ I ⊗ T_R) F and V = (E_L ⊗ I ⊗ E_R) C exactly.
Because both outer evaluations are isometries, C†C = V†V = I.
The right subchain is indexed from the right boundary inward; reversing
and transposing it recovers the original physical ordering.

The final theorem specializes the construction to the polar isometry of
an injective blocked site-dependent chain at an arbitrary chosen site,
including either endpoint. Positive bond dimension is explicit. No
translation-invariance, normalization, or additional rank condition is used.

The non-injective case permitted by source footnote 3 is now handled in
`MixedSequentialSupport`. QICLean's existing orthogonal-projection range
isometry supplies J with J†J = I and JJ† equal to the actual polar support.
The same inward sweeps factor VJ on this finite input, and multiplication
by J† reconstructs V. No full-dimensional isometry is asserted for V itself.
The resolved source note is
[`mswc24_mixed_polar_injectivity_scope`](../paper-gaps/mswc24_mixed_polar_injectivity_scope.tex).

The mixed factorization predicate and central-input constructions now allow
arbitrary finite input dimension. Their original full-input specializations
are unchanged. The existing chain splitting argument is shared rather than
duplicated, and no new support predicate or spectral-basis proof is introduced.
