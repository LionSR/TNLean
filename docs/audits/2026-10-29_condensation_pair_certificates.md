# Explicit condensation-pair certificates

The split and non-split example modules record numerical data for the
sixteen pairs in the Z2 × Z2 condensation example. The common compression
and intertwiner arguments already belong to shared constructors.

The twelve split entries use `MultiBlockCompression.ofEq` ten times and
`MultiBlockCompression.ofConjInt` twice, with source and target dimensions
varying between one and two. The two conjugated entries use the displayed
sign gauge. An indexed family would retain the dimension and gauge cases.

The four non-split entries all use `MultiBlockCompression.ofScalarFlagFour`.
Their source dimension is four, target dimension is one, and retained scalar
is always in the third coordinate. The targets, integer gauges and inverses,
conjugated letters and intertwiner witnesses vary. These explicit numerical
certificates remain named; their trace, nilpotency and intertwiner proofs
are supplied by the shared constructors.

The defect module already assembles all sixteen pairs from target normality
and the common word-trace identity. No additional indexed construction is
needed to share a mathematical proof. This documented choice concerns
certificate organization and changes no Lean declaration or proof.
