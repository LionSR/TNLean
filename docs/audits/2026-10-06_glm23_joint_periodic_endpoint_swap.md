# GLM23: sector exchange and both actual periodic endpoints

## Source and scope

This extends the checked first-endpoint package for GLM23 v3,
`Papers/2203.12563/REsubmission.tex`, lines 1695–1777. The actual mixed
family, joint support, and periodic Hamiltonian are the existing objects.
The new result covers the second periodic endpoint and supplies one
positive constant valid at both endpoints for every ring length at least
two. It does not assert a gap over the interior of the path or settle
the open-boundary comparison or phase classification.

## Exact permutation and transport

The physical equivalence sends `00(i)` to reversed `11(i)`, `11(j)` to
reversed `00(j)`, `01(x,a,b)` to reversed `10(x,a,b)`, and `10(x,a,b)` to
reversed `01(x,a,b)`. Both rectangular coordinates retain their order.
The virtual change is the actual summand permutation in each block,
not transport along an equality of dimension numerals.

Writing this virtual algebra equivalence as `Φₓ`, the actual letters obey

```
C_rev,x(e μ) = Φₓ(C_x(μ))
W_rev,x(1−γ) = Φₓ(W_x(γ))
A_rev,x(1−γ,e μ) = Φₓ(A_x(γ,μ))
```

These statements hold for every real parameter without injectivity or
dimension assumptions. The physical isometry `U_N` maps reversed-chain
vectors to original-chain vectors by precomposition with the alphabet
equivalence. The joint two-site boundary identity is
`U₂ Γ_rev,1−γ((ΦₓXₓ)ₓ) = Γ_γ(X)`.
Trace invariance is applied to every complete block product before the
joint sum is taken, preserving all physical overlap between block labels.

Surjectivity on each virtual block gives exact support equality. Orthogonal
projection onto an isometric image then gives local parent conjugacy.
The existing generic cyclic-placement conjugacy supplies the full periodic
Hamiltonian conjugacy, preserving both directed terms at length two.
The same matrix permutation transports actual component MPS vectors and
their common coefficient map, even at length zero.

## Endpoint kernels and gaps

Apply the first-endpoint theorem to the reversed pair. The second-endpoint
kernel is exactly the span of the actual parameter-one component vectors.
Its uniform gap has exactly the reversed first-endpoint constant.
The source hypotheses are the two simultaneous one-site spans and
positive second-block dimensions. No positivity of the original first
dimensions, nonempty-label assumption, or nonzero physical alphabet is
introduced.

The generic isometric-conjugacy helper explicitly transports kernel
membership, the whole kernel, and its orthogonal complement. It preserves
any real norm-gap bound in both directions without positivity or finite
dimensionality assumptions. The kernel-orthogonality transport is therefore
part of the proof, rather than an additional premise.

When both endpoint block dimensions are positive, the minimum of the two
common-parent endpoint constants works at both parameter values. Each
endpoint bound comes from its full joint canonical parent. The result
does not take minima of separate block gaps.

## Implementation and ownership

- `JointMixedEndpointSwap` proves the exact physical and virtual family,
  joint-support, and local-parent identities.
- `JointMixedEndpointRightPeriodicGap` proves actual periodic transport,
  the parameter-one kernel and uniform gap, and both-endpoint statements.
- `IsometricConjugationGap` provides five generic isometry lemmas. Their
  unique blueprint owner is the shared ch13 martingale entry
  `thm:martingale_isometric_conjugation_gap`; the core-identification
  development uses the same file and owner.

The eight first-endpoint proof modules are reused unchanged. Integration
adds three generated imports, one strict regression entry, and one chapter
include. The swap blueprint leaf gives direct mathematical statements and
proofs; it adds no tensor diagram.

## Validation checkpoint

The initial three-module source checkpoint is preserved publicly at
`18fe4919ac69bfbf670245dcf6c9d0fe02808b47`, tree
`27d03b2780228bb42c94b9af4b4f8a0c547e49f0`.
The generic helper passed an isolated strict native compile in 8.9 seconds
before the executor filesystem interruption, with no source repair.
The actual swap and right-periodic modules are still uncompiled at this
checkpoint. Their new blueprint entries remain unchecked.

The regression covers physically overlapping block columns on endpoint
alphabets of sizes two and three, unequal virtual dimensions one and two,
the ordered rectangular tuple `(0,1)`, arbitrary-parameter conjugacy,
two-site kernels, the derived uniform gaps, an original endpoint with
zero physical and bond dimensions, and empty labels with both empty and
nonempty physical alphabets. Fourteen strict guards expect only
`propext`, `Classical.choice`, and `Quot.sound`.

Strict regression and full compiled declaration checks remain pending.
No success is inferred from the completed first-endpoint checks or from
the generic helper's separate native check.

The focused PDF and web builds pass. Both new mathematical pages, PDF
pages 3–4, were visually inspected; the equations fit and references
resolve. The full focus has no overfull boxes. All 21 declaration links
are present in the HTML and have unique source owners. The native Tenkz
event audit passes for the one inherited context panel, with no hard
errors or advisories. Raw HTML reader checks, pinned latexindent 3.24.7,
reader-facing prose, generated imports, and source reverse coverage pass.
The prior local browser launch was denied permission to create its
singleton socket; it was not repeated. The exact-head CI browser gate
remains required. The adjacent validation JSON records all source and
render hashes and distinguishes these checks from the pending Lean gates.
