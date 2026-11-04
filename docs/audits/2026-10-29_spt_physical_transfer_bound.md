# Physical clustering to actual limiting transfer correlations

Sources: SPC11, arXiv:1010.3732, Section II.F, lines 929–953;
Hastings–Koma, arXiv:math-ph/0507008, Section 3; and arXiv:2307.01696,
Supplemental Material, proof of Lemma 2.

The actual finite connected correlator is now connected to the physical
clustering theorem in #10333. On a ring of length L+t+L+n, the two actual
length-L windows have cyclic distance greater than t when n>=t. Their
embeddings are contractive and the first support has at most L sites.
Thus the common physical constants give K(L+1)||X||||Y||exp(-kappa t)
for the exact finite correlator used by the transfer contraction formula.

Normalized finite expectations depend only on the actual periodic rays.
Mathlib's singleton-span theorem gives a unit scalar even in the zero
case; its modulus-squared factor cancels from the expectation ratio.
This transports the bound to every representative of those rays,
without any continuous gauge or nonzero-vector side condition.

For a trace-preserving block-injective tensor and its faithful stationary
trace-one density, pointwise primitivity gives complementary transfer
powers tending to zero. The existing exact finite-ring formula therefore
converges to the actual limiting connected contraction at every fixed
positive separation. No uniform transfer rate or assumed convergence is
used in this argument: a qualitative rate may depend on the tensor.

An eventual finite bound passes through that norm limit. The existing
eigenvalue observables then force every nonunit transfer eigenvalue to
have modulus at most r=exp(-kappa)<1. The physical path supplies kappa;
neither the convergence nor the common transfer bound is substituted as
a public physical premise.

The actual faithful adjoint fixed point of an injective unital tensor
supplies its square-root trace-preserving bond gauge. Injectivity, the
positive periodic rays, and the transfer spectrum are preserved. Primitive
Perron--Frobenius theory derives a faithful stationary density, normalized
by its positive trace. Thus neither a gauge nor a density is added as an
extra public hypothesis to the common unital transfer-bound theorem.

The resulting bound has exactly the input required by the existing
compact-limit/class-invariance argument. The new physical theorem
`ExactMPSGroundPath.exists_constant_virtual_class` consequently derives
one physical character and a common virtual cohomology class across
changes of minimal bond dimension. No clustering, limiting-correlation,
transfer-bound, continuous canonical-gauge or virtual-action conclusion
is supplied as an additional premise. The theorem concerns the existing
exact MPS physical-path domain; it makes no claim about arbitrary paths
whose ground states have no such MPS realization.

This source-written stack remains pending hosted Lean acceptance and
integration; the new Blueprint nodes and proofs remain notready. No local
Lean build, elaboration or checkdecls was run, as requested. Native
declaration/import/prose/format/integrity checks and independent source/API
review do not replace proof acceptance. Issue #9879 stays open.
