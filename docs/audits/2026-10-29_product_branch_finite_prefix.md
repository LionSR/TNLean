# Actual finite-prefix ground vectors in the product-state branch

Source: SPWC10, arXiv:0909.5347, Theorem 5 and proof, main.tex lines 850–880.
Native obligation: #10386, blocking #10280. This child stacks the finite
representation/padding source in #10376, preserving the original eventual
dichotomy and its hypotheses.

The general missing condition is exact zero momentum of a nonzero short
volume ground vector. An invariant ground line alone does not prove it.
The all-volume hypotheses concern one fixed positive interaction; tensoring
a short periodic state does not automatically preserve the wrap constraints,
so that operation is not used to claim a general extension theorem.

The new actual construction treats the derived normal tensor when its bond
dimension is one. Core/BondOneVector reuses the existing forced-bond trace
expansion. A nonzero letter gives a nonzero constant-configuration amplitude
at every positive length. Normality supplies the letter through an existing
lemma; no finite-length state nonvanishing is supplied.

The actual local-kernel inclusion from the prime-length propagation argument
annihilates the periodic vector at every permitted length, including all
short ones. Trace cyclicity gives exact zero momentum. If the actual kernels
are one-dimensional at all permitted volumes, the same bond-one tensor spans
each kernel. Neither short representations nor momentum equations are added
as hypotheses. Positivity is used upstream when deriving the actual local
kernel inclusion, not redundantly repeated on its consumer.

The actual prime-length extraction now exposes the normal tensor and local
kernel inclusion it already derived, without repeating that proof. Its
existing eventual-only theorem remains the projection used by the quantitative
dichotomy. The new public product caller starts only with the fixed positive
interaction, all-volume uniqueness and one nonzero bond-one prime-length
ground representation with N ≥ L+4. Extraction returns a positive bond
D0 ≤ 1, hence D0=1, and supplies both standing data internally. The caller
then constructs one actual bond-one ground family at every permitted positive
volume. The derived B and local-kernel inclusion are not caller premises.

This is a scoped product-state branch, not a resolution of #10386 for
higher virtual dimension. No full-hypothesis counterexample is claimed.
Both new Blueprint entries remain notready. Source/import/role/prose/TeX,
file-size, tactic, integrity and diff checks are used; no local Lean/Lake,
compilation, checkdecls or cache mutation. Hosted validation and integration
remain pending.
